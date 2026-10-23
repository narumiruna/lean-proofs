"""Header-only regression tests, cross-checked with pinned Lean parseHeader."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import test_checks

checks = test_checks.checks
ORACLE = Path(__file__).with_name("fixtures") / "header_imports.lean"
SHARED = "Math.Rudin.Support.Shared"


def cases():
    valid = {
        "plain": (f"import {SHARED}\n", [SHARED]),
        "trailing_line": (f"import {SHARED} -- comment", [SHARED]),
        "trailing_block": (f"import {SHARED}/- comment -/", [SHARED]),
        "nested": (f"/- import Math.Fake /- inner -/ -/\nimport/- nested /- x -/ -/{SHARED}\n", [SHARED]),
        "multiline": (f"import\n/- split -/\n{SHARED}\n", [SHARED]),
        "same_line": (f"import {SHARED} import Math.Other", [SHARED, "Math.Other"]),
        "crlf": (f"import\r\n{SHARED} -- trailing\r\n", [SHARED]),
        "prelude": (f"prelude\nimport {SHARED}\n", [SHARED]),
        "module_prelude": (f"module\nprelude\nimport {SHARED}\n", [SHARED]),
        "line_comment": (f"-- import Math.Fake\nimport {SHARED}", [SHARED]),
        "string_body": (f'import {SHARED}\ndef s := "\nimport Math.Fake\n"\n', [SHARED]),
        "raw_string_body": ('def s := r#"\nimport Math.Fake\n"#\n', []),
        "body_comment": (f"import {SHARED}\ndef x := 0\n/-\nimport Math.Fake\n-/", [SHARED]),
        "body_import": (f"import {SHARED}\nnamespace X\nimport Math.Fake", [SHARED]),
        "module_doc": (f"import {SHARED}\n/-!\nimport Math.Fake\n-/\nimport Math.Late", [SHARED]),
        "declaration_doc": ("/--\nimport Math.Fake\n-/\ndef x := 0", []),
        "public_body": (f"module\nimport {SHARED}\npublic section\nimport Math.Fake", [SHARED]),
        "meta_body": (f"module\nimport {SHARED}\nmeta def x := 1\nimport Math.Fake", [SHARED]),
        "empty": ("", []),
        "comment_only": ("/- nested /-- doc inside -/ /-! module doc inside -/ -/", []),
    }
    for flags in ("import", "public import", "meta import", "public meta import", "import all", "meta import all"):
        valid[flags.replace(" ", "_")] = (f"module\n{flags} {SHARED}\n", [SHARED])
        valid["split_" + flags.replace(" ", "_")] = (
            "module\n" + "/- separator -/\n".join(flags.split()) + f"/- name -/{SHARED}", [SHARED])
    return valid


class HeaderTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_supported_headers_match_pinned_lean(self):
        directory = self.root / "oracle-inputs"
        directory.mkdir(exist_ok=True)
        inputs = []
        for label, (source, expected) in cases().items():
            path = directory / (label + ".lean")
            path.write_bytes(source.encode())
            inputs.append(str(path))
            with self.subTest(label=label):
                self.assertEqual(checks.header_imports(path.read_text()), expected)
        result = subprocess.run(["lean", "--run", str(ORACLE), *inputs],
                                capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(rows), len(inputs))
        for row in rows:
            with self.subTest(lean=Path(row["path"]).stem):
                self.assertEqual(row["errors"], [])
                self.assertEqual(row["imports"], cases()[Path(row["path"]).stem][1])

    def test_unsupported_or_invalid_header_fails_closed(self):
        for source in (
            "import Math.«Rudin».Support.Shared", "import «Math».Rudin.Support.Shared",
            "import Math.Rudin.λ", "import Math.Rudin.Sharedλ", "import«Math»",
            "import Math.Rudin.Shared'", "import Math.Rudin.Shared!", "import Math..Shared",
            "import Math.", "import", "import -- no name", "import /-- doc -/ Math.X",
            "import\tMath.X", "import\u00a0Math.X", "import Math.X\t", "import Math.X /- open",
            "/- open", "public import Math.X", "meta import Math.X", "import all Math.X",
            "module\npublic import all Math.X", "module\npublic meta import all Math.X",
        ):
            with self.subTest(source=source):
                with self.assertRaises(checks.InventoryError):
                    checks.header_imports(source)

    def test_legal_extended_names_are_explicitly_rejected(self):
        directory = self.root / "oracle-rejected-inputs"
        directory.mkdir(exist_ok=True)
        sources = [
            "import Math.«Rudin».Support.Shared", "import «Math».Rudin.Support.Shared",
            "import«Math».Rudin.Support.Shared", "import Math.Rudin.α",
            "import Math.Rudin.Sharedα", "import Math.Rudin.Shared'",
            "import Math.Rudin.Shared!", "import Math.Rudin.Shared?",
        ]
        paths = []
        for i, source in enumerate(sources):
            path = directory / f"case{i}.lean"
            path.write_text(source)
            paths.append(str(path))
            with self.subTest(source=source):
                with self.assertRaises(checks.InventoryError):
                    checks.header_imports(source)
        result = subprocess.run(["lean", "--run", str(ORACLE), *paths],
                                capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(rows), len(sources))
        for row in rows:
            self.assertEqual(row["errors"], [])
            self.assertEqual(len(row["imports"]), 1)

    def test_first_review_tracks_commented_shared_import(self):
        case = test_checks.InventoryTests()
        case.setUp()
        try:
            path = case.verified_fixture()
            shared = checks.module_path(case.root, SHARED)
            shared.parent.mkdir(parents=True)
            shared.write_text("-- Shared source.\n")
            path.write_text(f"import {SHARED} -- regression\n")
            (case.root / "Math/Rudin.lean").write_text(
                f"import Math.Rudin.Chapter01.Exercise01\nimport {SHARED}\n")
            evidence = case.data["exercises"][0]["obligations"][0]["evidence"]
            evidence["source_hashes"] = checks.proof_fingerprint(
                case.root, "Math.Rudin.Chapter01.Exercise01")
            case.validate()
            shared.write_text("-- Changed shared source.\n")
            with self.assertRaisesRegex(checks.InventoryError, "Stale proof-source"):
                case.validate()
        finally:
            case.doCleanups()

    def test_comment_cannot_make_orphan_support_reachable(self):
        case = test_checks.InventoryTests()
        case.setUp()
        try:
            shared = checks.module_path(case.root, SHARED)
            shared.parent.mkdir(parents=True)
            shared.write_text("-- Unimported support.\n")
            (case.root / "Math/Rudin.lean").write_text(
                f"/-\nimport {SHARED}\n-/\n")
            with self.assertRaisesRegex(checks.InventoryError, "not imported"):
                case.validate()
        finally:
            case.doCleanups()

    def test_transitive_closure_cycle_and_second_evidence_gate(self):
        import test_second_review
        case = test_second_review.SecondReviewTests()
        case.setUp()
        try:
            shared = checks.module_path(case.root, SHARED)
            shared.parent.mkdir(parents=True)
            shared.write_text(f"import {case.data['exercises'][0]['module']} -- cycle\n")
            case.path.write_text(f"import {SHARED} -- regression\n")
            hashes = checks.proof_fingerprint(case.root, case.data["exercises"][0]["module"])
            self.assertEqual(set(hashes), {SHARED, case.data["exercises"][0]["module"]})
            case.group["source_hashes"] = hashes
            case.validate(final=True)
            shared.write_text(shared.read_text() + "-- changed support\n")
            self.assertNotEqual(hashes, checks.proof_fingerprint(case.root, case.data["exercises"][0]["module"]))
            with self.assertRaisesRegex(checks.InventoryError, "second-review source closure"):
                case.validate(final=True)
        finally:
            case.doCleanups()


if __name__ == "__main__":
    unittest.main()

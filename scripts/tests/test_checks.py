"""Regression tests for inventory structure and the actual Lean axiom audit."""

import copy
import importlib.util
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("check_exercises", ROOT / "scripts/check_exercises.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


def inventory_fixture():
    chapters, exercises = [], []
    for chapter, count in enumerate(checks.COUNTS, 1):
        page = chapter * 10
        chapters.append({"number": chapter, "exercise_count": count, "book_pages": [page, page]})
        for number in range(1, count + 1):
            eid = f"R{chapter:02}E{number:02}"
            exercises.append({
                "id": eid, "chapter": chapter, "number": number,
                "book_pages": [page], "pdf_pages": [page + 9],
                "summary": "Synthetic test contract.",
                "module": f"Math.Rudin.Chapter{chapter:02}.Exercise{number:02}",
                "source_review": {"method": "ocr"}, "issues": [], "depends_on": [],
                "disposition": "as_stated", "obligation_count": 1,
                "obligations": [{"id": eid + ".main", "summary": "Prove the test contract.",
                                 "kind": "proof", "status": "todo", "declarations": [], "evidence": None}],
            })
    return {"schema_version": 1, "source": {"title": "Test", "edition": "Test", "sha256": "0" * 64,
                                           "exercise_count": 287, "obligation_count": 287},
            "chapters": chapters, "exercises": exercises}


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Math").mkdir()
        (self.root / "Math.lean").write_text("import Math.Rudin\n")
        (self.root / "Math/Rudin.lean").write_text("-- Synthetic root.\n")
        (self.root / "lean-toolchain").write_text("test-toolchain\n")
        (self.root / "lakefile.toml").write_text('name = "test"\n')
        (self.root / "lake-manifest.json").write_text("{}\n")
        self.data = inventory_fixture()

    def validate(self, final=False):
        return checks.validate(self.data, self.root, final)

    def test_partial_inventory_passes_development_gate(self):
        request, _, statuses = self.validate()
        self.assertEqual(statuses["todo"], 287)
        self.assertEqual(request["modules"], ["Math.Rudin"])

    def test_final_gate_rejects_unfinished_work(self):
        with self.assertRaisesRegex(checks.InventoryError, "Unfinished"):
            self.validate(final=True)

    def test_missing_exercise_fails(self):
        self.data["exercises"].pop()
        with self.assertRaisesRegex(checks.InventoryError, "exercise"):
            self.validate()

    def test_missing_subquestion_fails(self):
        exercise = self.data["exercises"][0]
        exercise["obligation_count"] = 2
        with self.assertRaisesRegex(checks.InventoryError, "subquestion"):
            self.validate()

    def test_duplicate_exercise_fails(self):
        self.data["exercises"][-1] = copy.deepcopy(self.data["exercises"][0])
        with self.assertRaisesRegex(checks.InventoryError, "Duplicate"):
            self.validate()

    def test_false_verified_status_fails(self):
        self.data["exercises"][0]["obligations"][0]["status"] = "verified"
        with self.assertRaisesRegex(checks.InventoryError, "no theorem"):
            self.validate()

    def test_missing_semantic_evidence_fails(self):
        obligation = self.data["exercises"][0]["obligations"][0]
        obligation.update(status="verified", declarations=["Rudin.Chapter01.exercise01"])
        with self.assertRaisesRegex(checks.InventoryError, "evidence"):
            self.validate()

    def test_truthy_failed_evidence_is_rejected(self):
        obligation = self.data["exercises"][0]["obligations"][0]
        obligation.update(status="verified", declarations=["Rudin.Chapter01.exercise01"],
                          evidence={"semantic_review": {"reviewed": False}, "checks": {"success": False}})
        with self.assertRaisesRegex(checks.InventoryError, "successful semantic"):
            self.validate()

    def test_failed_check_result_is_rejected(self):
        obligation = self.data["exercises"][0]["obligations"][0]
        obligation.update(status="verified", declarations=["Rudin.Chapter01.exercise01"], evidence={
            "semantic_review": {"result": "passed", "reviewer": "test", "notes": "Synthetic review."},
            "checks": {"single_file": "passed", "project_build": "passed",
                       "axiom_audit": "failed", "coverage": "passed"}})
        with self.assertRaisesRegex(checks.InventoryError, "successful check"):
            self.validate()

    def verified_fixture(self):
        path = self.root / "Math/Rudin/Chapter01/Exercise01.lean"
        path.parent.mkdir(parents=True)
        path.write_text("-- Synthetic delivery.\n")
        (self.root / "Math/Rudin.lean").write_text("import Math.Rudin.Chapter01.Exercise01\n")
        obligation = self.data["exercises"][0]["obligations"][0]
        obligation.update(status="verified", declarations=["Rudin.Chapter01.exercise01"], evidence={
            "semantic_review": {"result": "passed", "reviewer": "test", "notes": "Synthetic review."},
            "checks": {key: "passed" for key in ("single_file", "project_build", "axiom_audit", "coverage")},
            "source_hashes": checks.proof_fingerprint(self.root, "Math.Rudin.Chapter01.Exercise01"),
            "environment_sha256": checks.environment_fingerprint(self.root)})
        return path

    def test_structured_success_evidence_is_accepted(self):
        self.verified_fixture()
        request, _, statuses = self.validate()
        self.assertEqual(statuses["verified"], 1)
        self.assertEqual(request["targets"][0]["name"], "Rudin.Chapter01.exercise01")

    def test_changed_proof_source_invalidates_evidence(self):
        path = self.verified_fixture()
        path.write_text("-- Changed mathematical statement.\n")
        with self.assertRaisesRegex(checks.InventoryError, "Stale proof-source"):
            self.validate()

    def test_changed_shared_definition_invalidates_evidence(self):
        path = self.verified_fixture()
        support = self.root / "Math/Rudin/Support/Shared.lean"
        support.parent.mkdir(parents=True)
        support.write_text("-- Original shared definition.\n")
        path.write_text("import Math.Rudin.Support.Shared\n")
        evidence = self.data["exercises"][0]["obligations"][0]["evidence"]
        evidence["source_hashes"] = checks.proof_fingerprint(self.root, "Math.Rudin.Chapter01.Exercise01")
        self.validate()
        support.write_text("-- Changed shared definition.\n")
        with self.assertRaisesRegex(checks.InventoryError, "Stale proof-source"):
            self.validate()

    def test_changed_environment_invalidates_evidence(self):
        self.verified_fixture()
        (self.root / "lake-manifest.json").write_text('{"changed": true}\n')
        with self.assertRaisesRegex(checks.InventoryError, "Stale environment"):
            self.validate()

    def test_wrong_page_reference_fails(self):
        self.data["exercises"][0]["pdf_pages"] = [999]
        with self.assertRaisesRegex(checks.InventoryError, "page mismatch"):
            self.validate()

    def test_unimported_delivery_fails(self):
        path = self.root / "Math/Rudin/Support/Orphan.lean"
        path.parent.mkdir(parents=True)
        path.write_text("-- This file is not imported.\n")
        with self.assertRaisesRegex(checks.InventoryError, "not imported"):
            self.validate()

    def test_unlisted_exercise_file_fails(self):
        path = self.root / "Math/Rudin/Chapter01/Exercise99.lean"
        path.parent.mkdir(parents=True)
        path.write_text("-- Not in the source inventory.\n")
        with self.assertRaisesRegex(checks.InventoryError, "Unlisted"):
            self.validate()


class LeanAuditTests(unittest.TestCase):
    """Run negative fixtures in temporary source files, not the delivery library."""

    @classmethod
    def setUpClass(cls):
        result = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT,
                                text=True, capture_output=True, timeout=30, check=True)
        cls.lean_path = result.stdout.strip()

    def audit(self, declaration="", request=None, outside_source=None):
        base = ROOT / ".lake"
        base.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="rudin-audit-", dir=base) as directory:
            root = Path(directory)
            env = os.environ | {"LEAN_PATH": str(root) + os.pathsep + self.lean_path}
            path = root / "Math/Rudin/Fixture.lean"
            path.parent.mkdir(parents=True)
            request_path = root / "request.json"
            request_path.write_text(json.dumps(request or {"modules": [], "targets": []}))
            source = (ROOT / "scripts/check_axioms.lean").read_text()
            # Use the same audit code, without loading the full delivery library per fixture.
            source = source.replace("import Math\n", "import Outside\n" if outside_source else "")
            if outside_source:
                outside = root / "Outside.lean"
                outside.write_text(outside_source)
                compiled = subprocess.run(
                    ["lean", f"--root={root}", "-o", str(root / "Outside.olean"), str(outside)],
                    cwd=ROOT, env=env, text=True, capture_output=True, timeout=180,
                )
                self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            source = source.replace('".lake/rudin-check/request.json"', json.dumps(str(request_path)))
            source = source.replace("open Lean Elab Command", declaration + "\n\nopen Lean Elab Command", 1)
            path.write_text(source)
            return subprocess.run(
                ["lean", f"--root={root}", str(path)],
                cwd=ROOT, env=env, text=True, capture_output=True, timeout=180,
            )

    def test_valid_theorem_passes(self):
        result = self.audit("theorem Rudin.fixture : True := True.intro")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Axiom audit passed", result.stdout)

    def test_sorry_is_rejected_by_environment_audit(self):
        result = self.audit("theorem Rudin.fixture : False := by sorry")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("sorryAx", result.stdout + result.stderr)

    def test_unused_custom_axiom_is_rejected(self):
        result = self.audit("axiom Rudin.fixture : True")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Custom axiom", result.stdout + result.stderr)

    def test_transitive_custom_axiom_is_rejected(self):
        result = self.audit("theorem Rudin.fixture : False := Outside.assumption",
                            outside_source="axiom Outside.assumption : False\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("depends on Outside.assumption", result.stdout + result.stderr)

    def test_missing_declaration_is_rejected(self):
        request = {"modules": [], "targets": [{"name": "Rudin.Chapter01.doesNotExist",
                    "module": "Math.Rudin.Fixture", "obligation": "fixture"}]}
        result = self.audit(request=request)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Missing declaration", result.stdout + result.stderr)

    def test_missing_actual_import_is_rejected(self):
        result = self.audit(request={"modules": ["Math.Rudin.Missing"], "targets": []})
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("not imported", result.stdout + result.stderr)

    def test_definition_cannot_replace_theorem(self):
        request = {"modules": [], "targets": [{"name": "Rudin.Chapter01.fixture",
                    "module": "Math.Rudin.Fixture", "obligation": "fixture"}]}
        result = self.audit("def Rudin.Chapter01.fixture : True := True.intro", request)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("proved theorem", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()

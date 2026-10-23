"""Regression tests for retained, source-bound second semantic reviews."""

import copy
import tempfile
import unittest
from pathlib import Path

import test_checks

checks = test_checks.checks


class SecondReviewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name, content in (("lean-toolchain", "test\n"),
                              ("lakefile.toml", 'name = "test"\n'),
                              ("lake-manifest.json", "{}\n")):
            (self.root / name).write_text(content)
        exercise = copy.deepcopy(test_checks.inventory_fixture()["exercises"][0])
        obligation = exercise["obligations"][0]
        obligation["declarations"] = ["Rudin.Chapter01.exercise01"]
        self.data = {"source": {"sha256": "0" * 64}, "exercises": [exercise]}
        self.path = checks.module_path(self.root, exercise["module"])
        self.path.parent.mkdir(parents=True)
        self.path.write_text("-- Synthetic source.\n")
        self.group = {
            "id": "test-group", "reviewer": "independent-test",
            "report_sha256": "1" * 64,
            "environment_sha256": checks.environment_fingerprint(self.root),
            "source_hashes": checks.proof_fingerprint(self.root, exercise["module"]),
            "checks": dict.fromkeys(("source_review", "fresh_build", "actual_body_audit",
                                    "theorem_origins", "independent_controls"), "passed"),
            "decisions": [{"id": obligation["id"], "result": "passed",
                           "declarations": list(obligation["declarations"]),
                           "disposition": "as_stated", "notes": "Synthetic source-to-type review."}],
        }
        self.review = {"schema_version": 1, "stage": "second_full_book",
                       "source_sha256": "0" * 64, "groups": [self.group]}

    def validate(self, final=False):
        return checks.validate_second_reviews(self.data, self.review, self.root, final)

    def test_complete_review_passes(self):
        self.assertEqual(self.validate(final=True), 1)

    def test_partial_review_is_development_only(self):
        extra = copy.deepcopy(self.data["exercises"][0]["obligations"][0])
        extra["id"] += "_extra"
        self.data["exercises"][0]["obligations"].append(extra)
        self.assertEqual(self.validate(), 1)
        with self.assertRaisesRegex(checks.InventoryError, "Incomplete second"):
            self.validate(final=True)

    def test_failed_check_is_rejected(self):
        self.group["checks"]["actual_body_audit"] = "failed"
        with self.assertRaisesRegex(checks.InventoryError, "second-review checks"):
            self.validate()

    def test_duplicate_decision_is_rejected(self):
        self.group["decisions"].append(copy.deepcopy(self.group["decisions"][0]))
        with self.assertRaisesRegex(checks.InventoryError, "duplicate second-review obligation"):
            self.validate()

    def test_duplicate_group_is_rejected(self):
        self.review["groups"].append(copy.deepcopy(self.group))
        with self.assertRaisesRegex(checks.InventoryError, "duplicate second-review group"):
            self.validate()

    def test_changed_mapping_is_rejected(self):
        self.group["decisions"][0]["declarations"] = ["Rudin.Chapter01.wrong"]
        with self.assertRaisesRegex(checks.InventoryError, "second-review declarations"):
            self.validate()

    def test_changed_source_is_rejected(self):
        self.path.write_text("-- Changed theorem.\n")
        with self.assertRaisesRegex(checks.InventoryError, "second-review source closure"):
            self.validate()

    def test_changed_shared_source_is_rejected(self):
        support = self.root / "Math/Rudin/Support/Shared.lean"
        support.parent.mkdir(parents=True)
        support.write_text("-- Shared definition.\n")
        self.path.write_text("import Math.Rudin.Support.Shared\n")
        self.group["source_hashes"] = checks.proof_fingerprint(
            self.root, self.data["exercises"][0]["module"])
        self.validate()
        support.write_text("-- Changed definition.\n")
        with self.assertRaisesRegex(checks.InventoryError, "second-review source closure"):
            self.validate()

    def test_changed_environment_is_rejected(self):
        (self.root / "lean-toolchain").write_text("different\n")
        with self.assertRaisesRegex(checks.InventoryError, "second-review environment"):
            self.validate()

    def test_changed_source_disposition_is_rejected(self):
        self.group["decisions"][0]["disposition"] = "refuted_and_corrected"
        with self.assertRaisesRegex(checks.InventoryError, "second-review source disposition"):
            self.validate()

    def test_missing_notes_or_failed_decision_is_rejected(self):
        for key, value in (("notes", ""), ("result", "failed")):
            with self.subTest(key=key):
                old = self.group["decisions"][0][key]
                self.group["decisions"][0][key] = value
                with self.assertRaisesRegex(checks.InventoryError, "second semantic review"):
                    self.validate()
                self.group["decisions"][0][key] = old

    def test_wrong_stage_or_primary_source_is_rejected(self):
        for key, value in (("stage", "first_review"), ("source_sha256", "2" * 64)):
            with self.subTest(key=key):
                old = self.review[key]
                self.review[key] = value
                with self.assertRaises(checks.InventoryError):
                    self.validate()
                self.review[key] = old

    def test_missing_report_hash_is_rejected(self):
        del self.group["report_sha256"]
        with self.assertRaisesRegex(checks.InventoryError, "report hash"):
            self.validate()


if __name__ == "__main__":
    unittest.main()

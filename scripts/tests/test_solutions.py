"""Regression checks for solution-article coverage and source references."""

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("check_solutions", ROOT / "scripts/check_solutions.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


class SolutionArticleTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.article = self.root / "docs/rudin/solutions.md"
        self.chapter = self.article.parent / "solutions/chapter-01.md"
        self.chapter.parent.mkdir(parents=True)
        self.source = self.root / "Math/Rudin/Chapter01/Exercise01.lean"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("theorem exercise01 : True := by trivial\n")
        self.record = {"id": "R01E01", "chapter": 1, "number": 1,
                       "disposition": "as_stated", "obligations": [
                           {"status": "verified", "declarations": ["Rudin.Chapter01.exercise01"]}]}
        self.save_inventory()
        (self.root / "README.md").write_text("[Solutions](docs/rudin/solutions.md)\n")
        self.index_text = """# Solutions
**1 exercise files**; **1 verified resolutions**; 1 proved as stated; **0 entries** pending.
[Chapter 1](solutions/chapter-01.md#chapter-01)
"""
        self.article.write_text(self.index_text)
        self.text = """<a id="chapter-01"></a>
# Chapter 1
[All chapters](../solutions.md)
<a id="r01e01"></a>
### 1.1 — True
**Lean source:** [Exercise01.lean](../../../Math/Rudin/Chapter01/Exercise01.lean).
**Inventory status:** Verified as stated.
**Statement.** True.
**Proof.** By definition.
**Lean declarations:** `exercise01`.
"""
        self.chapter.write_text(self.text)

    def save_inventory(self):
        (self.root / "exercises.json").write_text(json.dumps({"exercises": [self.record]}))

    def test_complete_article_passes(self):
        self.assertEqual(checks.validate(self.root), [])

    def test_one_pending_entry_uses_singular(self):
        self.record["obligations"][0]["status"] = "in_progress"
        self.save_inventory()
        self.article.write_text(self.index_text.replace("**1 verified resolutions**",
            "**0 verified resolutions**").replace("1 proved as stated", "0 proved as stated")
            .replace("**0 entries**", "**1 entry**"))
        self.chapter.write_text(self.text.replace("Verified as stated.", "Pending verification."))
        self.assertEqual(checks.validate(self.root), [])
        self.article.write_text(self.article.read_text().replace("**1 entry**", "**1 entries**"))
        self.assertIn("Stale pending-entry count", checks.validate(self.root))

    def test_new_exercise_requires_article_entry(self):
        self.source.with_name("Exercise02.lean").write_text("theorem exercise02 : True := by trivial\n")
        self.assertTrue(any("missing=['r01e02']" in e for e in checks.validate(self.root)))

    def test_duplicate_entry_is_rejected(self):
        self.chapter.write_text(self.text + '<a id="r01e01"></a>\n')
        self.assertIn("Duplicate exercise entries", checks.validate(self.root))

    def test_stale_status_is_rejected(self):
        self.chapter.write_text(self.text.replace("Verified as stated.", "Pending verification."))
        self.assertIn("r01e01: stale inventory status", checks.validate(self.root))

    def test_missing_mapped_declaration_is_rejected(self):
        self.chapter.write_text(self.text.replace("`exercise01`", "`other`"))
        errors = checks.validate(self.root)
        self.assertTrue(any("missing mapped declaration" in e for e in errors))
        self.assertIn("r01e01: unknown source declaration other", errors)

    def test_broken_anchor_is_rejected(self):
        self.chapter.write_text(self.text + "\n[Missing](#missing)\n")
        self.assertIn("Broken article anchor: #missing", checks.validate(self.root))

    def test_source_alias_is_accepted(self):
        self.source.write_text("theorem original : True := by trivial\nalias exercise01 := original\n")
        self.assertEqual(checks.validate(self.root), [])

    def test_stale_count_is_rejected(self):
        self.article.write_text(self.index_text.replace("**1 exercise files**", "**2 exercise files**"))
        self.assertIn("Stale exercise-file count", checks.validate(self.root))

    def test_truncated_output_is_rejected(self):
        self.chapter.write_text(self.text + "\n[Showing lines 1-20]\n")
        self.assertIn("Truncated tool output in article", checks.validate(self.root))

    def test_missing_chapter_is_rejected(self):
        self.chapter.unlink()
        self.assertIn("Chapter files differ from exercise sources", checks.validate(self.root))

    def test_wrong_chapter_is_rejected(self):
        self.chapter.rename(self.chapter.with_name("chapter-02.md"))
        self.assertIn("r01e01: wrong chapter file", checks.validate(self.root))

    def test_missing_index_link_is_rejected(self):
        self.article.write_text(self.index_text.replace("[Chapter 1](solutions/chapter-01.md#chapter-01)", ""))
        self.assertIn("Chapter 01: index link missing", checks.validate(self.root))

    def test_cross_file_anchor_is_checked(self):
        self.article.write_text(self.index_text + "\n[Missing](solutions/chapter-01.md#missing)\n")
        self.assertIn("Broken article anchor: solutions/chapter-01.md#missing", checks.validate(self.root))

    def test_cross_chapter_link_passes(self):
        self.chapter.write_text(self.text + "\n[This exercise](chapter-01.md#r01e01)\n")
        self.assertEqual(checks.validate(self.root), [])


if __name__ == "__main__":
    unittest.main()

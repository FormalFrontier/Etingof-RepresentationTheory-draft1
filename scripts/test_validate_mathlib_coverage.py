#!/usr/bin/env python3

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

import validate_mathlib_coverage as validator


class RenderCheckerTests(unittest.TestCase):
    def test_renders_each_distinct_nonempty_name_once(self):
        coverage = [
            {"description": "First dependency", "mathlib_names": ["Nat.add", "Nat.mul"]},
            {"description": "Second dependency", "mathlib_names": ["Nat.mul", "Nat.sub"]},
        ]
        checker = validator.render_checker(coverage)
        self.assertEqual(checker.count("#check @Nat.add"), 1)
        self.assertEqual(checker.count("#check @Nat.mul"), 1)
        self.assertEqual(checker.count("#check @Nat.sub"), 1)

    def test_wraps_long_descriptions_below_linter_limit(self):
        coverage = [{"description": "word " * 40, "mathlib_names": ["Nat.add"]}]
        checker = validator.render_checker(coverage)
        self.assertTrue(all(len(line) <= 100 for line in checker.splitlines()))

    def test_related_names_are_also_checked(self):
        coverage = [{
            "description": "Missing result with nearby infrastructure",
            "mathlib_names": [],
            "related_mathlib_names": ["Nat.add"],
        }]
        self.assertIn("#check @Nat.add", validator.render_checker(coverage))


class ValidationTests(unittest.TestCase):
    def make_repo(self) -> Path:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        (root / "dependencies").mkdir()
        (root / "research").mkdir()
        (root / "EtingofRepresentationTheory").mkdir()
        external = [{"description": "Dependency"}]
        coverage = [{
            "description": "Dependency",
            "category": "folklore",
            "mathlib_names": ["Nat.add"],
            "match_quality": "exact",
            "notes": "Covered.",
        }]
        audit = {
            "mathlib_revision": "abc",
            "mathlib_input_revision": "v1",
            "entries_reviewed": 1,
            "previously_partial_and_missing_entries_reviewed": 24,
            "nonexact_entries_after_audit": 0,
        }
        manifest = {"packages": [{"name": "mathlib", "rev": "abc", "inputRev": "v1"}]}
        (root / "dependencies/external.json").write_text(json.dumps(external))
        (root / "research/mathlib-coverage-external.json").write_text(json.dumps(coverage))
        (root / validator.AUDIT_RELATIVE_PATH).write_text(json.dumps(audit))
        (root / "lake-manifest.json").write_text(json.dumps(manifest))
        (root / validator.CHECKER_RELATIVE_PATH).write_text(validator.render_checker(coverage))
        return root

    def validate_quietly(self, root: Path) -> bool:
        with contextlib.redirect_stdout(io.StringIO()):
            return validator.validate(root)

    def test_valid_fixture(self):
        self.assertTrue(self.validate_quietly(self.make_repo()))

    def test_rejects_stale_checker(self):
        root = self.make_repo()
        (root / validator.CHECKER_RELATIVE_PATH).write_text("import Mathlib\n")
        self.assertFalse(self.validate_quietly(root))

    def test_rejects_audit_revision_mismatch(self):
        root = self.make_repo()
        audit_path = root / validator.AUDIT_RELATIVE_PATH
        audit = json.loads(audit_path.read_text())
        audit["mathlib_revision"] = "stale"
        audit_path.write_text(json.dumps(audit))
        self.assertFalse(self.validate_quietly(root))

    def test_rejects_missing_audit_metadata(self):
        root = self.make_repo()
        (root / validator.AUDIT_RELATIVE_PATH).unlink()
        self.assertFalse(self.validate_quietly(root))

    def test_rejects_wrong_review_count(self):
        root = self.make_repo()
        audit_path = root / validator.AUDIT_RELATIVE_PATH
        audit = json.loads(audit_path.read_text())
        audit["entries_reviewed"] = 2
        audit_path.write_text(json.dumps(audit))
        self.assertFalse(self.validate_quietly(root))


if __name__ == "__main__":
    unittest.main()

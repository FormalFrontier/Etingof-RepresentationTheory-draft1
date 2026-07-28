#!/usr/bin/env python3
"""Tests for check_proof_placeholders.py."""

import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

import check_proof_placeholders as checker


ADO_ITEM_ID = "Chapter2/Remark2.9.3"
ADO_SOURCE = "EtingofRepresentationTheory/Chapter2/Remark2_9_3.lean"
ADO_DECLARATION = "Etingof.ado"
SCOPE_HEADING = "Book-stated external results intentionally left as `proof_wanted`"


class ProofPlaceholderTests(unittest.TestCase):
    def run_checker(self, root: Path, *, enforce_completion: bool = False) -> int:
        arguments = ["check_proof_placeholders.py", "--root", str(root)]
        if enforce_completion:
            arguments.append("--enforce-completion")
        with (
            patch.object(sys, "argv", arguments),
            redirect_stdout(StringIO()),
            redirect_stderr(StringIO()),
        ):
            return checker.main()

    def write_items(self, root: Path, items: list[dict]) -> None:
        progress = root / "progress"
        progress.mkdir(parents=True, exist_ok=True)
        (progress / "items.json").write_text(json.dumps(items), encoding="utf-8")

    def approved_ado_item(self) -> dict:
        return {
            "id": ADO_ITEM_ID,
            "status": checker.APPROVED_STATUS,
            "coverage": "covered_full",
            "sorry_free": True,
            checker.APPROVAL_FIELD: {
                "classification": checker.APPROVAL_CLASSIFICATION,
                "declaration": ADO_DECLARATION,
                "source": ADO_SOURCE,
                "scope_document": "skipped-exercises.md",
                "scope_heading": SCOPE_HEADING,
                "reason": "Reviewed external-result boundary.",
                "approved_by_issue": 8110,
            },
        }

    def write_ado_scope_entry(self, root: Path) -> None:
        (root / "skipped-exercises.md").write_text(
            f"## {SCOPE_HEADING}\n\n{ADO_ITEM_ID} records `{ADO_DECLARATION}`.\n",
            encoding="utf-8",
        )

    def test_scan_ignores_comments_and_string_forms(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "EtingofRepresentationTheory" / "Test.lean"
            source.parent.mkdir()
            source.write_text(
                "/- sorry /- proof_wanted hidden -/ axiom hidden -/\n"
                "def prose := \"admit constant hidden\"\n"
                "def quote := '\"'\n"
                "def raw := r###\"sorryAx theorem_wanted hidden\"###\n"
                "-- proof_wanted alsoHidden\n"
                "axiom realAxiom : True\n"
                "constant realConstant : Nat\n"
                "example : True := by\n"
                "  sorry\n"
                "theorem_wanted approved : True\n",
                encoding="utf-8",
            )

            markers = checker.scan_lean_file(root, source)

        self.assertEqual(
            [(marker.kind, marker.line, marker.declaration) for marker in markers],
            [
                ("project_axiom", 6, "realAxiom"),
                ("project_constant", 7, "realConstant"),
                ("sorry", 9, None),
                ("theorem_wanted", 10, "approved"),
            ],
        )

    def test_unterminated_lexical_form_fails_closed(self) -> None:
        for source in ('def text := "unterminated', "/- unterminated"):
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    checker.code_without_comments_or_strings(source)

    def test_sorry_is_reported_by_default_and_enforced_at_completion(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_items(root, [])
            source = root / "EtingofRepresentationTheory" / "Test.lean"
            source.parent.mkdir()
            source.write_text("example : True := by sorry\n", encoding="utf-8")

            self.assertEqual(self.run_checker(root), 0)
            self.assertEqual(self.run_checker(root, enforce_completion=True), 1)

    def test_forbidden_placeholders_fail_in_default_mode(self) -> None:
        forbidden_sources = {
            "admit": "example : True := by admit\n",
            "sorryAx": "example : True := sorryAx True true\n",
            "axiom": "open Foo in axiom hiddenAxiom : True\n",
            "constant": "namespace N\nconstant hiddenConstant : Nat\nend N\n",
            "def_wanted": "def_wanted missingData : Nat\n",
            "instance_wanted": "instance_wanted missingInstance : Inhabited Nat\n",
        }
        for name, content in forbidden_sources.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self.write_items(root, [])
                source = root / "EtingofRepresentationTheory" / "Test.lean"
                source.parent.mkdir()
                source.write_text(content, encoding="utf-8")
                self.assertEqual(self.run_checker(root), 1)

    def test_unapproved_wanted_theorem_in_root_module_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_items(root, [])
            (root / "EtingofRepresentationTheory.lean").write_text(
                "proof_wanted unapproved : True\n", encoding="utf-8"
            )
            self.assertEqual(self.run_checker(root), 1)

    def test_approved_ado_marker_succeeds(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / ADO_SOURCE
            source.parent.mkdir(parents=True)
            source.write_text("proof_wanted ado : True\n", encoding="utf-8")
            self.write_ado_scope_entry(root)
            self.write_items(root, [self.approved_ado_item()])

            approvals, errors = checker.load_approvals(
                root, root / "progress" / "items.json"
            )

            self.assertEqual(errors, [])
            self.assertIn((ADO_SOURCE, "ado"), approvals)
            self.assertEqual(self.run_checker(root), 0)

    def test_orphaned_approval_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / ADO_SOURCE
            source.parent.mkdir(parents=True)
            source.write_text("theorem unrelated : True := True.intro\n", encoding="utf-8")
            self.write_ado_scope_entry(root)
            self.write_items(root, [self.approved_ado_item()])

            self.assertEqual(self.run_checker(root), 1)


if __name__ == "__main__":
    unittest.main()

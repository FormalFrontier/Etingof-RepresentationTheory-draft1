#!/usr/bin/env python3
"""Tests for check_proof_placeholders.py."""

import json
import tempfile
import unittest
from pathlib import Path

import check_proof_placeholders as checker


class ProofPlaceholderTests(unittest.TestCase):
    def test_scan_ignores_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "EtingofRepresentationTheory" / "Test.lean"
            source.parent.mkdir()
            source.write_text(
                "/- sorry /- proof_wanted hidden -/ axiom hidden -/\n"
                "def prose := \"admit constant hidden\"\n"
                "-- proof_wanted alsoHidden\n"
                "axiom realAxiom : True\n"
                "constant realConstant : Nat\n"
                "example : True := by\n"
                "  sorry\n"
                "proof_wanted approved : True\n",
                encoding="utf-8",
            )

            markers = checker.scan_lean_file(root, source)

        self.assertEqual(
            [(marker.kind, marker.line, marker.declaration) for marker in markers],
            [
                ("project_axiom", 4, "realAxiom"),
                ("project_constant", 5, "realConstant"),
                ("sorry", 7, None),
                ("proof_wanted", 8, "approved"),
            ],
        )

    def test_load_approvals_requires_scope_entry(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source_name = "EtingofRepresentationTheory/Test.lean"
            source = root / source_name
            source.parent.mkdir()
            source.write_text("proof_wanted approved : True\n", encoding="utf-8")
            heading = "Book-stated external results intentionally left as `proof_wanted`"
            (root / "skipped-exercises.md").write_text(
                f"## {heading}\n\nItem/Test records `Etingof.approved`.\n",
                encoding="utf-8",
            )
            items_path = root / "items.json"
            items_path.write_text(
                json.dumps(
                    [
                        {
                            "id": "Item/Test",
                            "status": checker.APPROVED_STATUS,
                            checker.APPROVAL_FIELD: {
                                "classification": checker.APPROVAL_CLASSIFICATION,
                                "declaration": "Etingof.approved",
                                "source": source_name,
                                "scope_document": "skipped-exercises.md",
                                "scope_heading": heading,
                                "reason": "Reviewed external-result boundary.",
                                "approved_by_issue": 8110,
                            },
                        }
                    ]
                ),
                encoding="utf-8",
            )

            approvals, errors = checker.load_approvals(root, items_path)

        self.assertEqual(errors, [])
        self.assertIn((source_name, "approved"), approvals)


if __name__ == "__main__":
    unittest.main()

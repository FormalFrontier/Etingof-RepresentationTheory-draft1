#!/usr/bin/env python3
"""Focused regression tests for the exercise-coverage ratchet."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parent))

from reconcile_exercise_coverage import render_declaration_checker  # noqa: E402
from validate_exercise_coverage import (  # noqa: E402
    declaration_names,
    github_heading_slug,
)


class ExerciseCoverageTests(unittest.TestCase):
    def test_declaration_names_expands_legacy_separator(self) -> None:
        self.assertEqual(declaration_names("A.one; A.two"), ["A.one", "A.two"])

    def test_scope_heading_slug_matches_checked_anchors(self) -> None:
        self.assertEqual(
            github_heading_slug("Problem 8.2.8 — the Ext Künneth formula"),
            "problem-828--the-ext-künneth-formula",
        )
        self.assertEqual(
            github_heading_slug("Problem 2.16.5 — full quantum sl₂ classification"),
            "problem-2165--full-quantum-sl-classification",
        )

    def test_checker_imports_provider_instead_of_root(self) -> None:
        checker = render_declaration_checker(
            [
                {
                    "id": "Chapter2/Example",
                    "lean_file": [
                        "EtingofRepresentationTheory/Chapter2/Example.lean"
                    ],
                    "claim_coverage": {
                        "claims": [
                            {
                                "unit": "part_a",
                                "verdict": "formalized",
                                "lean_decl": ["Etingof.example"],
                            }
                        ]
                    },
                }
            ]
        )
        self.assertIn("import EtingofRepresentationTheory.Chapter2.Example", checker)
        self.assertNotIn("import EtingofRepresentationTheory\n", checker)
        self.assertIn("#check @Etingof.example", checker)


if __name__ == "__main__":
    unittest.main()

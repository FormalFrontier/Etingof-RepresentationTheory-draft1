#!/usr/bin/env python3

import unittest

from validate_lean_decls import Pointer, collect, lean_ref_groups, render_shards


class ValidateLeanDeclsTests(unittest.TestCase):
    def test_collects_nested_declarations(self) -> None:
        pointers, errors = collect(
            [{"id": "Chapter1/Test", "claim_coverage": {"claims": [
                {"lean_decl": "Etingof.first; Mathlib.second"}
            ]}}]
        )
        self.assertEqual(errors, [])
        self.assertEqual([pointer.name for pointer in pointers], ["Etingof.first", "Mathlib.second"])

    def test_rejects_expression_and_prose(self) -> None:
        _, errors = collect([{"id": "Chapter1/Test", "lean_decl": "CommRing k"}])
        self.assertTrue(any("not an exact Lean declaration name" in error for error in errors))

    def test_parses_canonical_lean_ref(self) -> None:
        errors: list[str] = []
        groups = lean_ref_groups(
            "EtingofRepresentationTheory/Chapter2/Definition2_2_1.lean :: "
            "Etingof.AssociativeAlgebra, Etingof.AssociativeAlgebra.IsUnit",
            "test",
            errors,
        )
        self.assertEqual(errors, [])
        self.assertEqual(groups[0][1], [
            "Etingof.AssociativeAlgebra", "Etingof.AssociativeAlgebra.IsUnit"
        ])

    def test_render_deduplicates_checks(self) -> None:
        shards, excluded = render_shards(
            [Pointer("Etingof.same", "one"), Pointer("Etingof.same", "two")],
            {"Etingof.same": "EtingofRepresentationTheory.Chapter1.Same"},
        )
        text = next(iter(shards.values()))
        self.assertEqual(excluded, 0)
        self.assertEqual(text.count("#check @Etingof.same"), 1)
        self.assertIn("one, two", text)

    def test_rejects_stale_provider_map(self) -> None:
        with self.assertRaisesRegex(ValueError, "provider.*stale"):
            render_shards([Pointer("Etingof.current", "one")], {"Etingof.old": "Mathlib"})


if __name__ == "__main__":
    unittest.main()

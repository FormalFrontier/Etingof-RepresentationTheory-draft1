#!/usr/bin/env python3

import unittest

from validate_lean_decls import (
    CI_EXCLUDED_PROVIDER_MODULES,
    Pointer,
    collect,
    environment_pins,
    lean_ref_groups,
    module_source_path,
    render_shards,
    source_sha256,
    validate_excluded_attestations,
    validate_lean_ref_providers,
)


class ValidateLeanDeclsTests(unittest.TestCase):
    def test_collects_nested_declarations(self) -> None:
        pointers, errors = collect(
            [{"id": "Chapter1/Test", "claim_coverage": {"claims": [
                {"lean_decl": "Etingof.first; Mathlib.second"}
            ]}}]
        )
        self.assertEqual(errors, [])
        self.assertEqual(
            [pointer.name for pointer in pointers], ["Etingof.first", "Mathlib.second"])

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
        self.assertEqual(excluded, [])
        self.assertEqual(text.count("#check @Etingof.same"), 1)
        self.assertIn("one, two", text)

    def test_generated_shard_disables_long_line_linter(self) -> None:
        name = "Etingof." + "veryLongNamespace." * 7 + "theorem"
        shards, _ = render_shards(
            [Pointer(name, "one")],
            {name: "EtingofRepresentationTheory.Chapter1.Same"},
        )
        text = next(iter(shards.values()))
        self.assertIn("set_option linter.style.longLine false", text)
        self.assertIn(f"#check @{name}", text)

    def test_rejects_stale_provider_map(self) -> None:
        with self.assertRaisesRegex(ValueError, "provider.*stale"):
            render_shards([Pointer("Etingof.current", "one")], {"Etingof.old": "Mathlib"})

    def test_ci_exclusions_have_real_source_files(self) -> None:
        self.assertTrue(CI_EXCLUDED_PROVIDER_MODULES)
        self.assertTrue(all(module_source_path(module).is_file()
                            for module in CI_EXCLUDED_PROVIDER_MODULES))

    def test_ci_excluded_name_is_attested_not_sharded(self) -> None:
        name = "Etingof.Proposition5_22_2"
        module = "EtingofRepresentationTheory.Chapter5.Proposition5_22_2"
        shards, excluded = render_shards([Pointer(name, "one")], {name: module})
        self.assertEqual(shards, {})
        self.assertEqual(excluded, [name])

    def test_excluded_attestation_requires_name_module_and_source_hash(self) -> None:
        module = "EtingofRepresentationTheory.Chapter5.Proposition5_22_2"
        providers = {"Etingof.example": module}
        good = {"Etingof.example": {
            "module": module,
            "source_sha256": source_sha256(module),
            **environment_pins(),
        }}
        self.assertEqual(validate_excluded_attestations(providers, good), [])
        self.assertTrue(validate_excluded_attestations(providers, {}))
        bad = {"Etingof.example": {"module": module, "source_sha256": "bad"}}
        self.assertTrue(validate_excluded_attestations(providers, bad))

    def test_lean_ref_must_name_its_real_provider(self) -> None:
        item = {"id": "Chapter1/Test", "lean_ref":
                "EtingofRepresentationTheory/Chapter2/Definition2_2_1.lean :: Etingof.same"}
        self.assertEqual(validate_lean_ref_providers(
            [item], {"Etingof.same":
                     "EtingofRepresentationTheory.Chapter2.Definition2_2_1"}), [])
        errors = validate_lean_ref_providers(
            [item], {"Etingof.same": "EtingofRepresentationTheory.Chapter1.Other"})
        self.assertTrue(any("not EtingofRepresentationTheory.Chapter2.Definition2_2_1" in e
                            for e in errors))

    def test_rejects_malformed_lean_refs(self) -> None:
        for value in [
            "missing separator",
            "NotProject/Provider.lean :: Etingof.same",
            "EtingofRepresentationTheory/Chapter2/Definition2_2_1.lean :: ",
        ]:
            errors: list[str] = []
            lean_ref_groups(value, "test", errors)
            self.assertTrue(errors, value)


if __name__ == "__main__":
    unittest.main()

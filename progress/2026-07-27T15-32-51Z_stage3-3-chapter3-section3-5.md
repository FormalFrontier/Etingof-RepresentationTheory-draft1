# Stage 3.3 proof-integrity audit — Chapter 3 §3.5

**Date:** 2026-07-27  
**Scope:** `Chapter3/Introduction_to_3.5` through `Chapter3/Proposition3.5.8`  
**Stacked base:** Stage 3.2 PR #8069, commit `60a816c86a55a8ba437f84f4baf39edf7f719024`  
**Result:** complete — eight mathematical items are verified sorry-free; the section heading has no proof obligation.

## Scope and outcome

The audited interval is exactly the nine contiguous `progress/items.json` entries 147–155.
Its strict predecessor is `Chapter3/Lemma3.4.2` and its strict successor is
`Chapter3/Introduction_to_3.6`. The Stage 3.2 claim inventory remains unchanged: 26
claims, comprising 22 `formalized`, two `covered_elsewhere`, and two
`non_formalizable` verdicts.

Stage 3.3 metadata now records the complete public declaration inventory for each
mathematical item. The heading is marked `proof_integrity: not_applicable`; the other
eight items are marked `proof_integrity: sorry_free`. No Lean source, claim-coverage
record, dependency file, or item outside the interval changed.

## Provider and declaration inventory

Ten modules provide the scoped declarations. Declaration ownership was read from the
compiled environment (`moduleIdxForModule?` and `declsInModuleIdx`), rather than
inferred from textual name matching.

| Provider module | Direct imports | Public declarations | Private/generated declarations |
|---|---:|---:|---:|
| `Definition3_5_1` | 1 | 1 | 1 |
| `Proposition3_5_2` | 1 | 2 | 0 |
| `Proposition3_5_3` | 3 | 2 | 1 |
| `Theorem3_5_4` | 11 | 1 | 1 |
| `Theorem3_5_4_Finiteness` | 6 | 2 | 0 |
| `Theorem3_5_4_CompleteFamily` | 2 | 5 | 3 |
| `Corollary3_5_5` | 8 | 1 | 0 |
| `Example3_5_6` | 11 | 41 | 82 |
| `Definition3_5_7` | 1 | 1 | 0 |
| `Proposition3_5_8` | 9 | 8 | 1 |
| **Total** | **53** | **64** | **89** |

The 64 public names are stored exactly, by item, in the new `stage3_3.declarations`
arrays. A sorted comparison between those arrays and the compiled-environment inventory
had no difference. Including private proof helpers, generated equations, boxed helpers,
and generated instances, the exhaustive inventory contains 153 declarations.

## Admission and axiom audit

All ten provider sources were scanned for `sorry`, `admit`, `proof_wanted`, `sorryAx`,
`native_decide`, and source-level `axiom` or `opaque` declarations. The scan returned no
matches.

`Lean.collectAxioms` was then run on every one of the 153 compiled declarations,
including the 89 private/generated declarations. The distribution was:

- 26 declarations with no axioms;
- 8 with `propext` only;
- 39 with `propext` and `Quot.sound`;
- 80 with `propext`, `Classical.choice`, and `Quot.sound`.

There were zero unexpected axioms. In particular, no declaration depends on `sorryAx`
or a project-defined axiom.

## Import audit

Every provider was re-elaborated from its source with `#redundant_imports` appended.
All ten elaborations succeeded. The sources contain 53 direct-import entries naming 30
unique modules. Five providers have no transitively redundant imports:
`Definition3_5_1`, `Proposition3_5_2`, `Proposition3_5_3`,
`Theorem3_5_4_CompleteFamily`, and `Definition3_5_7` (five providers total).

The diagnostic found 32 transitively redundant entries in the remaining providers:

- `Theorem3_5_4`: `Mathlib.RingTheory.Jacobson.Semiprimary`,
  `Mathlib.RingTheory.SimpleModule.Basic`,
  `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  `Mathlib.RingTheory.Jacobson.Ideal`, `Mathlib.RingTheory.Artinian.Module`,
  `Mathlib.Algebra.Algebra.Pi`, `Mathlib.FieldTheory.IsAlgClosed.Basic`, and
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`;
- `Theorem3_5_4_Finiteness`: `Mathlib.RingTheory.SimpleModule.Basic`,
  `Mathlib.Algebra.Algebra.Pi`, `Mathlib.LinearAlgebra.Dimension.Constructions`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, and
  `Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`;
- `Corollary3_5_5`: `Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
  `Mathlib.RingTheory.SimpleModule.Basic`,
  `Mathlib.LinearAlgebra.Dimension.Constructions`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, and
  `Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`;
- `Example3_5_6`: `Mathlib.RingTheory.Nilpotent.Lemmas`,
  `Mathlib.RingTheory.SimpleModule.Basic`,
  `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  `Mathlib.RingTheory.Polynomial.Ideal`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`,
  `Mathlib.RingTheory.Jacobson.Radical`, and
  `Mathlib.LinearAlgebra.Matrix.Block`;
- `Proposition3_5_8`: `Mathlib.RingTheory.SimpleModule.Basic`,
  `Mathlib.LinearAlgebra.Dimension.Finite`, `Mathlib.RingTheory.Artinian.Module`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`,
  `Mathlib.LinearAlgebra.Quotient.Basic`, and `Mathlib.Data.List.TFAE`.

These are recorded as Stage 3.4 dependency-trimming candidates. They were deliberately
not removed during the Stage 3.3 proof-integrity pass, preserving the workflow boundary
and exact source scope.

## Validation

- Scoped ten-provider build: passed, 1,977 jobs.
- Full `EtingofRepresentationTheory.Chapter3` build: passed, 8,692 jobs.
- `scripts/validate_items.py`: passed (593 records including ten derived overlays;
  existing schema warnings only).
- `scripts/validate_dependencies.py`: passed (583 entries, 582 edges; expected
  conservative-default warning only).
- `scripts/validate_external_deps.py`: passed (58 external dependencies).
- `scripts/validate_mathlib_coverage.py`: passed (58/58 entries).
- Scope-invariance normalization: deleting only `stage3_3` from entries 147–155 makes
  `progress/items.json` byte-for-byte JSON-equivalent to the stacked base.

The build reproduced the repository's existing linter warnings, including the unused
`Fintype` assumption in `density_theorem_part2`, the unused `h_complete` argument in
`sum_dim_sq_le_dim`, and proof-style/deprecation warnings in `Example3_5_6`. Those are
Stage 3.5 proof-polishing concerns, not proof-integrity failures.

## Handoff

Chapter 3 §3.5 has completed Stage 3.3. Its next designated step is Stage 3.4 dependency
trimming; only after that step completes is the section eligible for the Stage 3.5
Mathlib-quality proof-polishing pass.

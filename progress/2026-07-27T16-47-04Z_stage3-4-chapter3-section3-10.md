# Stage 3.4 dependency trimming — Chapter 3 §3.10

## Scope

This pass analyzes the exact six §3.10 catalog items after Stage 3.3: the section heading,
Exercise 3.10.1, the preview and statement of Theorem 3.10.2, Remark 3.10.3, and the theorem's
proof discussion. Their four direct providers and all Stage 3.2 and Stage 3.3 records are
preserved.

## Internal dependency result

The six conservative reading-order edges were replaced by declaration-backed dependencies:

- the section heading, matrix-algebra exercise, and organizational theorem preview use no earlier
  project item;
- Theorem 3.10.2 depends on `Chapter3/Theorem3.2.2`, whose
  `Etingof.density_theorem_part1` is invoked by its irreducibility and classification proofs;
- Remark 3.10.3 depends on `Chapter2/Discussion_2.7_intro`,
  `Chapter2/Proposition2.7.1`, and `Chapter2/Remark2.7.2` for the Weyl-algebra presentation and
  relations, the PBW basis and domain infrastructure, and the polynomial differential-operator
  representation used in its counterexample;
- the proof discussion depends on `Chapter3/Theorem3.2.2` and
  `Chapter3/Theorem3.10.2`, because its recorded endpoints explicitly reuse the density theorem
  and Theorem 3.10.2's irreducibility, classification, and uniqueness declarations.

The exact scoped graph therefore has six actual edges. The graph metadata and each item's
`stage3_4.actual_internal_dependencies` array agree exactly. All six items now have complete
Stage 3.4 records and top-level status `dependency_trimmed`.

## Import trimming

Every one of the original 26 direct imports was removed independently from an otherwise unchanged
provider and the full provider source was re-elaborated. The two Exercise 3.10.1 imports, the
Theorem 3.2.2 project import, all seven semantically focused Remark 3.10.3 imports, and the
radical provider's original umbrella could not be dropped without replacement. Seven direct
Mathlib imports in `Theorem3_10_2.lean` and eight in `Remark3_10_3.lean` were proven redundant
and removed.

The cumulative `minImports` linter was then run across `TensorProductRadical.lean`; it identified
the `Mathlib` umbrella as unneeded and supplied a focused candidate header. Each candidate was
again tested independently, six transitively covered suggestions were discarded, and the final
provider retains four necessary imports: `Mathlib.Tactic.NoncommRing`,
`Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Mathlib.RingTheory.SimpleModule.WedderburnArtin`, and
`Mathlib.RingTheory.TensorProduct.Pi`.

The final four providers have 14 direct imports in total (2 / 1 / 4 / 7). Every final import fails
an independent removal elaboration, and a final `#redundant_imports` run reports no transitively
redundant import in any provider. Only import headers changed; all declaration and proof bodies are
byte-for-byte unchanged.

## Validation

- fresh exact-provider baseline build before trimming: success (8,588 jobs);
- post-trim exact-provider build: success (2,481 jobs with the focused import closure);
- full `EtingofRepresentationTheory.Chapter3` build: success (8,693 jobs);
- independent original-import and final-import removal elaborations, cumulative `minImports`, and
  final `#redundant_imports` checks: success;
- `scripts/validate_items.py`, `scripts/validate_dependencies.py`,
  `scripts/validate_external_deps.py`, and `scripts/validate_mathlib_coverage.py`: success;
- `scripts/verify_blobs.py` remains inapplicable to the repository's derived overlay records and
  exits at the first such record with the pre-existing `KeyError: 'id'`;
- exact six-item tracker/graph agreement, provider-body invariance, normalized prior-stage and
  non-scope tracker invariance, and non-scope dependency-graph invariance: success;
- `jq empty dependencies/internal.json progress/items.json` and `git diff --check`: success.

This PR is limited to Chapter 3 §3.10 and Stage 3.4.

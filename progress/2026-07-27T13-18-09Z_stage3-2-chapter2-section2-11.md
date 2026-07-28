# Stage 3.2 fidelity review — Chapter 2 §2.11

## Scope

Reading order gives exactly eleven §2.11 catalog items, from
`Chapter2/Discussion_2.11_heading` through `Chapter2/Exercise2.11.7`. The preceding item is
`Chapter2/Discussion_2.10_continued`; the next item is `Chapter2/Discussion_2.12_heading`. The
scope includes all three discussion records between the numbered items.

The eleven items are served by twelve Lean provider files. Problem 2.11.3 has five providers;
the mixed-tensor definition and basis share `Discussion_pure_tensors.lean`; and
`Problem2_11_6.lean` is the policy/documentation provider for the intentional omission.

## Claim audit and repairs

All eleven blobs and all twelve providers were read in full. The durable tracker inventory has 44
claim units:

- 28 `formalized`;
- 4 `covered_elsewhere` by precise Mathlib or project declarations;
- 7 `non_formalizable` terminology, notation, or organizational units;
- 5 `intentional_omission` units belonging to Problem 2.11.6's standalone noncommutative
  bimodule API.

Stage 3.2 found and repaired three accidental gaps:

1. The free-abelian-group quotient in Exercise 2.11.2 was only additively equivalent to the tensor
   product. It now carries the transported `k`-module structure and a named linear equivalence,
   including the formula on generator classes.
2. The book's space `V^{⊗n} ⊗ (V*)^{⊗m}` of tensors of type `(m,n)` now has a direct project
   definition, `Etingof.TensorTypes.TensorType`.
3. The displayed basis of the mixed tensor space now has a direct construction,
   `Etingof.TensorTypes.tensorTypeBasis`, from the basis of `V`, its dual basis, the two finite
   indexed tensor-product bases, and their tensor-product basis.

After these repairs there are zero accidental or unclassified proof/coverage gaps. The five
remaining claim-level gaps are the explicit scope decision already recorded in
`skipped-exercises.md`: induced bimodule actions, balanced-tensor associativity, the Hom bimodule,
and the noncommutative tensor-Hom adjunction. Their only downstream use, Frobenius reciprocity, is
formalized directly as `Etingof.Theorem5_10_1`; no placeholder declaration represents the omitted
API.

## Durable tracker result

Every scoped item now has a complete Stage 3.2 `claim_coverage` record with verified definition
integrity, statement fidelity, and nonvacuity. Exercise 2.11.2 moves from `covered_partial` to
`covered_full`, closing the substance of follow-up #5972. The mixed-tensor discussion moves from
no mathematical coverage to full coverage. Problem 2.11.6 remains honestly `covered_partial` and
records each intentional omission separately. The non-§2.11 projection of `progress/items.json`
is byte-for-byte equivalent after normalized JSON comparison, and dependency metadata is
unchanged.

## Validation

- local worktree build state: `.lake/build` is worktree-local, while `.lake/packages` points to
  the shared package cache;
- all 12 scoped providers built successfully together (8592 jobs); the only replayed warning was
  the pre-existing header warning in `Infrastructure/Triangularization.lean`;
- `lake build EtingofRepresentationTheory.Chapter2`: success (8744 jobs); warnings are pre-existing
  and outside the two changed §2.11 providers;
- scoped scan found no `sorry`, `admit`, `axiom`, `opaque`, or `native_decide` declarations;
- `jq empty progress/items.json` and the exact 11-item/44-claim verdict aggregation passed;
- `python3 scripts/validate_items.py`: passed with full 5721/5721-line coverage (and its 593
  pre-existing extra-field warnings);
- `python3 scripts/validate_dependencies.py`: passed (one pre-existing conservative-default
  warning);
- normalized non-scope tracker hashes match, and `git diff --check` passes.

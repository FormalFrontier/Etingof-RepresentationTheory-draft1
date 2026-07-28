# Coverage-arm audit — §3.9 remaining items (Problems 3.9.2, 3.9.3, 3.9.5)

**Issue:** #7375 (Stage 3.7 exercise-coverage ratchet)
**Date:** 2026-07-22
**Scope:** the original audit assigned `coverage` fields and `lean_decl` targets
to Problems 3.9.2, 3.9.3, and 3.9.5. This permanent report is reconciled with
the current eight providers for those items:
`Problem3_9_2`, `Problem3_9_2_Classification`, `Problem3_9_3`,
`Problem3_9_3_TwoDim`, `Problem3_9_5`, `Problem3_9_5_Spinor`,
`Problem3_9_5_Spinor_Transport`, and `Problem3_9_5_Spinor_Odd`.

## Method

- `lake build` on `Chapter3.Problem3_9_2`, `Chapter3.Problem3_9_3`,
  `Chapter3.Problem3_9_5` — all succeed (only style lint warnings).
- Real `sorry` count = 0 in each file (`command grep -n sorry | grep -v sorry-free`).
- `#print axioms` on every headline decl shows only
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
- Every recorded `lean_decl` `#check`s against the built oleans.

### Axiom-check gotcha (important)

Appending `#print axioms` to the source and running `lake env lean <source>`
directly (the method in `.claude/commands/review.md`) reported a **spurious**
`sorryAx` on `Problem3_9_2.ext1_subsingleton_of_ne`, accompanied by
nondeterministic `synthInstanceFailed` / `rewrite failed` errors that do **not**
occur under `lake build`. Re-elaborating the whole source from scratch is flaky
for this file (instance synthesis order), and a failed elaboration is filled with
`sorryAx`, producing a false positive. The **reliable** check is a scratch file
that `import`s the *already-built* module and runs `#print axioms` there — against
the oleans, all decls are clean. (This only works because the full module + deps
were `lake build`-ed first, so no transitive olean is missing.)

## Verdicts

### Problem 3.9.2 — `covered_full`

- **(a)** `A = ℂ[x₁..xₙ]`. Ext¹ is fully computed both ways: `ext1_self` (277)
  `Ext¹(Vₐ,Vₐ) ≅ ℂⁿ`; `ext1_subsingleton_of_ne` (309) `Ext¹(V_b,Vₐ) = 0` for
  `a ≠ b`. `two_dim_is_extension` (511): every 2-dim rep is an extension of two
  1-dim reps — with the Ext¹ computation this classifies 2-dim reps. **covered_full.**
- **(b)** `B = ℂ⟨x₁..xₙ⟩/(xᵢxⱼ)`. `infinitely_many_indecomposables` (677): for
  `n>1`, a family `Cyc n k` of pairwise non-isomorphic indecomposable modules.
  **covered_full.**
- Roll-up **covered_full**. `Ext1` = in-book Problem3_9_1 `Z¹/B¹`.

### Problem 3.9.3 — `covered_full`

Single item, three book sub-questions:

- **Irreducibles** (full): `simpleRep_isIrreducible` (50) each `S_i` irreducible;
  `irreducible_isSimpleRep` (124) every irreducible of a *finite acyclic* quiver
  is `≅ S_i`.
- **Ext¹** (full): `ext1_simpleRep_vanishes_iff` gives the vanishing
  characterization and `finrank_ext1_simpleRep` proves the exact formula
  `dim Ext¹(S_i,S_j) = card (i⟶j)`. The latter closed #7376.
- **2-dim classification** (full): the core provider gives
  `two_dim_classification`; `Problem3_9_3_TwoDim` strengthens this to the
  explicit family `twoRep i j c`, the exhaustive module isomorphism
  `two_dim_normalForm`, the decomposable/indecomposable dichotomy, and exact
  support and scalar-isomorphism criteria, including parallel arrows. This
  completed the classification in #7420.

All three book requests are therefore `covered_full`; #7376 is closed and is
not an outstanding follow-up.

### Problem 3.9.5 (The Clifford algebra) — `covered_full`

Coverage is supplied by four current providers. `Problem3_9_5` proves the
abstract semisimplicity, matrix-algebra, dimension, and radical-quotient
results. `Problem3_9_5_Spinor` constructs wedge, contraction, the hyperbolic
spin representation, and its parity operator.
`Problem3_9_5_Spinor_Transport` transports arbitrary nondegenerate even forms
to the hyperbolic model. `Problem3_9_5_Spinor_Odd` constructs the two odd
spinors and proves irreducibility, nonisomorphism, and exhaustiveness.

- **(i)** nondegenerate ⇒ semisimple with even/odd classification:
  `isSemisimpleRing_of_nondegenerate` (475); `even_isMatrixAlgebra` (899)
  `Cl(V) ≃ₐ End(S)`, `dim S = 2ⁿ` for `dim V = 2n`; `odd_isSumMatrixAlgebra`
  (1126) `Cl(V) ≃ₐ End(S) × End(S)`, `dim S = 2ⁿ` for `dim V = 2n+1`. The
  matrix-algebra form is *stronger* than counting irreducibles — `End(S)` (resp.
  `End(S)²`) has exactly one (resp. two) simple module(s), so "no other
  irreducibles" is automatic; `finrank_cliffAlg` (374) `= 2^N` gives the
  `2^{dim V}` spanning-set bound. **covered_full.**
- **(ii)** `isSemisimpleRing_iff_nondegenerate` (1476) semisimple ⟺ nondegenerate;
  `radicalQuotient_isClifford_of_degenerate` (1742) degenerate ⇒
  `Cl(V)/Rad ≅ Cl(W,B')` for the induced nondegenerate form `B'` on `W ≅ V/rad(B)`
  (surjective algebra map, kernel = Jacobson radical). **covered_full.**
- Roll-up **covered_full**. `Cl(V)` = Mathlib `CliffordAlgebra` of `Q(v)=B(v,v)`.

## Reconciliations

- The original audit fixed stale `sorry_free: false` booleans; those booleans
  remain `true`. After the completed Stage 3.4 audit, the canonical top-level
  status of all three items is `dependency_trimmed`.
- Current `lean_file` arrays enumerate both Problem 3.9.2 providers, both
  Problem 3.9.3 providers, and all four Problem 3.9.5 providers.
- `progress/items.json` parses (`jq empty`).

## Follow-up

- **#7376 is closed** by `finrank_ext1_simpleRep`.
- The current Problems 3.9.2, 3.9.3, and 3.9.5 are all `covered_full`; no
  coverage follow-up remains for this audit.

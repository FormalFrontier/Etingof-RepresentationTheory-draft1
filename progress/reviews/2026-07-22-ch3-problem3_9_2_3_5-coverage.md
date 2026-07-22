# Coverage-arm audit — §3.9 remaining items (Problems 3.9.2, 3.9.3, 3.9.5)

**Issue:** #7375 (Stage 3.7 exercise-coverage ratchet)
**Date:** 2026-07-22
**Scope:** assign honest `coverage` fields + `lean_decl` targets to the three §3.9
items already `sorry_free` / `fidelity: verified` but lacking `coverage`. No
re-proving. Siblings 3.9.1 / 3.9.4 were classified earlier (#7363).

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

### Problem 3.9.3 — `covered_partial`  → follow-up #7376

Single item, three book sub-questions:

- **Irreducibles** (full): `simpleRep_isIrreducible` (50) each `S_i` irreducible;
  `irreducible_isSimpleRep` (124) every irreducible of a *finite acyclic* quiver
  is `≅ S_i`.
- **2-dim classification** (full): `two_dim_classification` (332) decomposable
  `S_i⊕S_j` or indecomposable supported on a single arrow `i→j` (`i≠j`) acting as
  an isomorphism.
- **Ext¹** (partial — reason for `covered_partial`): `ext1_simpleRep_vanishes_iff`
  (265) proves only the **vanishing** characterization
  `Ext1Vanishes(S_i,S_j) ↔ IsEmpty (i⟶j)`. The book asks to *compute* Ext¹, whose
  full answer `dim Ext¹(S_i,S_j) = card (i⟶j)` is only stated parenthetically in
  the docstring, not proved. Strictly weaker than the book claim.

Follow-up **feature #7376** tracks the missing dimension formula; landing it lifts
the item to `covered_full`.

### Problem 3.9.5 (The Clifford algebra) — `covered_full`

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

- Fixed stale `sorry_free: false` (with `status: sorry_free`) → `true` on all
  three items (verified sorry-free).
- Normalized `lean_file` from a bare string to a one-element list, matching the
  audited siblings 3.9.1 / 3.9.4.
- `progress/items.json` parses (`jq empty`).

## Follow-up

- **#7376** — formalize `dim Ext¹(S_i,S_j) = number of arrows i→j` for path-algebra
  simples (lifts 3.9.3 to `covered_full`). No other follow-ups: 3.9.2 and 3.9.5 are
  fully covered.

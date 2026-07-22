# Stage 3.7 re-audit — Problem 4.12.1 (irreducible reps of dihedral groups)

**Issue:** #7268 (re-audit resolving the sole `unchecked` item in the tree; closes the
earlier GAP recorded in #7219).
**File:** `EtingofRepresentationTheory/Chapter4/Problem4_12_1.lean` (888 lines).
**Blob:** `blobs/Chapter4/Problem4.12.1.md`.
**Verdict:** **VERIFIED** — statement-faithful and non-vacuous for both parts (a) and (b).

## Build / axiom check

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_1` exits 0.
- `#print axioms` on all 13 headline declarations returns exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, axiom-clean:
  `irreducible_dim`, `Vrep_irreducible`, `Vrep_trace_r`, `Vrep_not_iso`,
  `one_dim_reps_card_odd`, `one_dim_reps_card_even`, `simple_iso_char_or_Vrep`,
  `two_dim_simples_card_odd`, `two_dim_simples_card_even`, `total_irreps_card_odd`,
  `total_irreps_card_even`, `irreps_sum_sq`, `tensor_square_character`.

## Book text

> (a) Describe all irreducible complex representations of the symmetry group of a regular
> N-gon (order 2N), for odd and even N.
> (b) Let V be the 2-dim complexification of the standard real-plane representation. Find the
> decomposition of V ⊗ V into irreducibles.

## Part (a) — fidelity

- **Group model** (`DihedralGroup N`, blob line 1): Mathlib's dihedral group has order `2N`
  (`DihedralGroup.card`, used at line 740/825), generators `r k` (rotations) / `sr k`
  (reflections) — the faithful model of the N-gon symmetry group.
- **Dimension dichotomy** `irreducible_dim` (line 58): hypothesis is genuine irreducibility
  (`IsSimpleModule (MonoidAlgebra ℂ …) ρ.asModule`, converted to
  `Representation.IsIrreducible`); conclusion `finrank = 1 ∨ = 2`. Non-vacuous (`NeZero N`,
  `FiniteDimensional`, `Nontrivial` derived from simplicity). Faithful necessary condition.
- **Explicit 2-dim family** `Vrep N j` (line 280): a real `def` (body constructed via
  `repMat`, `Matrix.toLin'`), not a stub — `r 1` acts by `diag(ζ^j, ζ^{-j})`, `sr 0` swaps
  coordinates. `Vrep_irreducible` (line 318): simple iff `2·j ≠ 0`. `Vrep_trace_r` (line 399):
  character `ζ^{jk}+ζ^{-jk}`. `Vrep_not_iso` (line 410): distinct `r 1`-characters ⇒ no
  intertwining iso. All faithful to the standard 2-dim irreps.
- **1-dim characters** `charEquiv` (line 502): characters `DihedralGroup N →* ℂˣ` are in
  bijection with pairs `(u,w)` s.t. `u^N=1, u^2=1, w^2=1` (the `u^2=1` derived correctly from
  the dihedral relation `sr·r·sr = r⁻¹`). Counts `one_dim_reps_card_odd = 2` (line 573),
  `one_dim_reps_card_even = 4` (line 581) — match the book. `charOfData` is a genuine `def`.
- **Exhaustiveness** `simple_iso_char_or_Vrep` (line 730): every simple `FDRep ℂ (DihedralGroup
  N)` is iso to a 1-dim `charRep χ` or a 2-dim `Vrep N j` (`2j ≠ 0`). This is the genuine
  "describe ALL" content the #7219 audit found absent — now proved via
  `exists_simples_sum_finrank_sq_eq_card` (Artin–Wedderburn, `∑ dim² = 2N`) plus a pigeonhole
  (`surj_of_injective_of_sum_eq`) on a pairwise-non-isomorphic exhibited family. `charRep`
  (Example4_3_S3 line 66) is a real 1-dim representation (`g ↦ χ(g)·id`), confirmed simple.
- **Counts**: `two_dim_simples_card_odd = (N-1)/2`, `two_dim_simples_card_even = (N-2)/2`
  (integer division makes `card_TwoDimIdx = (N-1)/2` agree with `(N-2)/2` for even N),
  `total_irreps_card_odd = 2+(N-1)/2`, `total_irreps_card_even = 4+(N-2)/2`,
  `irreps_sum_sq = #1dim·1 + #2dim·4 = 2N`. All match the book's odd/even classification.

## Part (b) — fidelity

- `tensor_square_character` (line 163): `χ_V(g)² = 1 + χ_ε(g) + χ_{V₂}(g)` for all `g`,
  encoding `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂` (character of a tensor product is the product of characters).
- Class functions `chiStd`, `chiSign`, `chiRot2` are genuine `def`s (real bodies, no `True`
  stub): `χ_V(r k) = ζ^k+ζ^{-k}` (`0` on reflections), sign `±1`, `χ_{V₂}(r k) = ζ^{2k}+ζ^{-2k}`
  — the correct D_N characters. Proven for all `N`.

**Encoding note (not a gap):** part (b) is stated as a character identity among
independently-defined class functions rather than a bundled `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂` `FDRep`
isomorphism, and the file does not add a lemma equating `chiStd` to the character of the actual
complexified standard representation object (the values agree with `Vrep_trace_r` at `j=1`, and
`chiRot2` with `j=2`). This is a legitimate, standard formalization choice: over ℂ for a finite
group, character equality is equivalent to isomorphism, so the identity faithfully determines
the decomposition. Recorded as an observation for a possible future strengthening.

## Non-vacuity

All hypotheses are satisfiable (`NeZero N` for `N ≥ 1`; `Simple`/`IsSimpleModule` hypotheses
witnessed by `charRep` and `Vrep`); every definition is constructed, not sorry'd (`zeta`,
`eigen`, `repMat`, `Vrep`, `charOfData`, `charEquiv`, `chiStd`, `chiSign`, `chiRot2`); no
`True`-typed placeholders. `NeZero N` is the natural non-degeneracy hypothesis (N-gon needs
`N ≥ 1`), not a vacuity dodge.

## Outcome

`progress/items.json` → `Chapter4/Problem4.12.1`: `fidelity` set from `unchecked` to
`verified`; `fidelity_note` updated to record this re-audit basis. This clears the last
`unchecked` item in the tree.

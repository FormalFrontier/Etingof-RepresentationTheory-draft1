# Coverage-arm audit — Problem 5.2.7 (Galois extension for representations & vanishing of characters)

- **Issue:** #7352 (Stage 3.7 exercise-coverage ratchet)
- **Item:** `Chapter5/Problem5.2.7`
- **Backing Lean:** `EtingofRepresentationTheory/Chapter5/Remark5_2_8.lean`
  (no dedicated `Problem5_2_7.lean`; the id is a book id backed by embedded
  content in the Remark 5.2.8 file, the book's alternative proof of the same
  vanishing statement).
- **Verdict:** `covered_partial` (part (a) `not_started`, part (b) `covered_partial`).
- **Auditor model:** different model than formalized it; no prior fidelity review existed.

## The two book claims

- **(a)** For any finite group `G` there exists a finite Galois extension `K ⊂ ℂ`
  of `ℚ` such that any finite-dimensional complex representation of `G` has a basis
  in which every group element acts by a matrix with entries in `K`.
- **(b)** If `V` is an irreducible complex representation of a finite group `G`
  with `dim V > 1`, then there exists `g ∈ G` with `χ_V(g) = 0`.

## Build / axiom verification

- `lake build EtingofRepresentationTheory.Chapter5.Remark5_2_8` succeeds; file is
  sorry-free (no `sorry` occurrences).
- `#print axioms` on `character_prod_rat`, `beta_rat_not_mem_Ioo`,
  `isIntegral_prod_normSq_character`, `character_eq_sum_rootsOfUnity`,
  `character_ringHom_pow` all report exactly `[propext, Classical.choice, Quot.sound]`
  — no `sorryAx`.

## Part (b) — `covered_partial`

**What is honestly formalized** (Steps 3-5 of the remark, the Galois-conjugate
rationality core):

- `character_prod_rat` (line 423): `∃ q : ℚ, algebraMap ℚ ℂ q = ∏_{g≠1} χ_V(g)·χ_V(g⁻¹)`.
  Realizes `K = ℚ(ζ_N) = ℚ⟮ζ⟯ ⊆ ℂ`, lifts `β` to `K`, shows it is fixed by all of
  `Gal(K/ℚ)` (each automorphism acts as `ζ ↦ ζʲ`, combined with reindexing along
  `g ↦ gʲ`), and concludes `β ∈ ℚ` from the fixed field of the full Galois group
  being the base field. Genuine, non-vacuous.
- `character_eq_sum_rootsOfUnity` (215) / `trace_pow_eq_sum_eigenvalues` (307) /
  `character_ringHom_pow` (346): Steps 3-4 (eigenvalues are `N`-th roots of unity;
  `σ_j(χ_V(g)) = χ_V(gʲ)`).
- `isIntegral_prod_normSq_character` (181): `β` is an algebraic integer.
- `beta_rat_not_mem_Ioo` (570): composes the above into the final contradiction.

**Why it is only partial** (the two genuine gaps):

1. **`beta_rat_not_mem_Ioo` is hypothesis-gated on `0 < q < 1`** (`h0 : 0 < q`,
   `h1 : q < 1`). Its own docstring says this bound "is established by the main
   argument of Problem 5.2.7(b), not this remark." The `0 < β < 1` bound — the step
   that uses **character orthonormality**, and the **only** step where
   irreducibility and `dim > 1` enter — is not formalized. Tellingly,
   `character_prod_rat` and the whole rationality machinery quantify over an
   arbitrary `V : FDRep ℂ G` and use **neither** `Simple V` nor `dim V > 1`; those
   hypotheses live entirely in the missing bound.
2. **No declaration asserts the honest top-level conclusion** `∃ g, χ_V(g) = 0`
   for irreducible `dim > 1`. The whole file is the by-contradiction skeleton;
   the existence statement itself is never stated. (`Theorem5_4_4:405`,
   `V.character g = 0 ∨ ∃ c, V.ρ g = c • id`, is an unrelated per-element
   dichotomy under a coprimality hypothesis, not this global existence.)

Per the issue's explicit instruction, the hypothesis-gated `beta_rat_not_mem_Ioo`
is **not** counted as covering the full part-(b) claim.

## Part (a) — `not_started`

No declaration in the repository asserts the existence of the finite Galois
extension `K`, nor the `K`-entry basis. `rg` over `EtingofRepresentationTheory/`
finds only `Remark5_2_8.lean` referencing 5.2.7, and its content is entirely the
part-(b) vanishing argument. Part (a) (a Galois-descent-from-`ℚ̄` argument, the book
hint) is genuinely unformalized.

## items.json changes

Replaced the stale prose `coverage_note` (audit #7001) with an honest
`coverage: covered_partial` + `coverage_arm: audited`, `lean_file`/`lean_decl`
pointers into `Remark5_2_8.lean`, `last_updated: 2026-07-22`, and a `derived[]`
array tracking both parts at sub-part granularity:

- `(a) Galois extension` → `not_started`, `status: accepted`.
- `(b) vanishing character` → `covered_partial`, `status: accepted`.

`status` reconciled to `partially_formalized` (agrees with `covered_partial`).
JSON re-validated (`json.load`).

## Follow-up

A genuine gap is confirmed, so per Deliverable 3 a **follow-up `feature` issue**
(#7353) is opened for the tractable part-(b) residual: formalize the `0 < β < 1` orthonormality
bound (using irreducibility + `dim > 1`) and assemble the honest
`∃ g, χ_V(g) = 0` conclusion, composing with the existing `beta_rat_not_mem_Ioo`
and `character_prod_rat` skeleton. Part (a) is recorded as a tracked `not_started`
`derived` item but **not** scheduled as a feature issue this cycle: it is a
substantially larger, independent Galois-descent task better left for a planner to
prioritize.

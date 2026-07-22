# Stage 3.7 reconciliation: six stale `accepted` derived items (issue #7245)

**Date:** 2026-07-22
**Session type:** review (metadata hygiene, `items.json`-only — no Lean proof edits)

## Problem

Six `derived` items in `progress/items.json` carried `status: accepted` with no
`issue` field. Each had been flagged as a coverage gap by an earlier audit wave,
was subsequently formalized in Lean, but the metadata was never updated. This is
exactly the state a planner reads as "unformalized gap needing a feature issue,"
so it risked duplicate feature work (per the issue, a planner nearly created some).
It also failed the Stage 3.7 verify requirement "every `accepted` derived item has
an issue."

## Method

Each of the six was verified against its blob and Lean source with the Stage 3.2
non-vacuity tests (does the Lean genuinely assert the claim, or a weaker/vacuous
surrogate?). Six independent verification passes were run.

## Findings

| # | `derived_from` | Verdict | Disposition |
|---|----------------|---------|-------------|
| 1 | `Chapter5/Discussion_1dim_reps` | covered_full | `accepted` → `sorry_free` + `lean_ref` |
| 2 | `Chapter5/Discussion_5.11_examples` | covered_full | `accepted` → `sorry_free` + `lean_ref` |
| 3 | `Chapter5/Discussion_after_Definition5.23.1` | covered_partial | stay `accepted`, `issue: 7251` |
| 4 | `Chapter5/Discussion_complementary_series_summary` | covered_partial | stay `accepted`, `issue: 7252` |
| 5 | `Chapter5/Discussion_footnote_5.15` | covered_full | `accepted` → `sorry_free` + `lean_ref` |
| 6 | `Chapter7/Discussion_after_Example7.9.5` | covered_full | `accepted` → `sorry_free` + `lean_ref` |

### Full-coverage items (1, 2, 5, 6)

- **1 — 1-dim reps of GL₂(𝔽_q):** `Etingof.Discussion_1dim_reps.characterCompDetEquiv`
  is a genuine bijection (characters `ξ:𝔽_q×→ℂˣ`) ≃ (1-dim reps `G→ℂˣ`) — surjectivity
  gives "every 1-dim rep has form `ξ∘det`", injectivity gives uniqueness of `ξ`;
  `characterCompDetEquiv_apply` pins the map to `ξ(det g)`; `card_oneDimRep` gives
  the count `q−1`. Sorry-free, axiom-clean. (For `q>2`, matching the source.)
- **2 — Ind_{S₃}^{S₄} decompositions:** `indH_triv_decomp` / `indH_sign_decomp` /
  `indH_twoDim_decomp` are genuine `FDRep ℂ S₄` isomorphisms with correct
  multiplicities via the semisimple Hom-multiplicity classifier
  `iso_of_forall_finrank_hom_eq`, not mere character-scalar equalities. Sorry-free.
- **5 — footnote 5.15 lex inequality:** both the inequality `σ(ρ)≤ρ`
  (`rhoVec_comp_perm_le`) and the load-bearing equality-iff-identity
  (`rhoVec_comp_perm_eq_iff`, an actual `↔ σ=1`), plus the equivalent
  `λ+ρ−σ(ρ)≥λ` form (`laVec_eq_shifted_sub_perm_iff`). Sorry-free.
- **6 — additive functor on a semisimple category is exact:**
  `additiveFunctor_shortExact_of_isSemisimpleCategory`. `IsSemisimpleCategory`
  faithfully = "every short exact sequence splits"; conclusion is genuine two-sided
  exactness; the proof genuinely consumes semisimplicity. Sorry-free.

### Partial-coverage items (3, 4) — genuine residual gaps

- **3 — unique irreducible algebraic `L_λ`:** construction (`algIrrepGLRepρ`, the honest
  `det^{-shift}` twist of the Schur module, for every weakly-decreasing integer
  weight including negatives) and uniqueness (`algIrrepGLRepρ_iso_iff_eq`, highest
  weight a complete iso-invariant) are fully formalized and sorry-free. **Residual:**
  irreducibility (`algIrrepGLRep_isSimple`) is only proved over ℂ within the
  Schur–Weyl range `∑λ.toNatWeight ≤ N`, not for arbitrary dominant weights.
  Tracked by **#7251**; item kept `accepted` with `issue: 7251`.
- **4 — complementary-series completeness:** sub-claim (a), the arithmetic
  `(q−1)+q(q−1)/2+q(q−1)/2 = q²−1` (`constructed_irrep_count`), and sub-claim (b),
  `q²−1 = #conjugacy classes` (`card_conjClasses_eq`, odd char, separate file), are
  proved. **Residual:** sub-claim (c) — "these are ALL the irreducibles"
  (completeness) — is not stated as a formal proposition (only the unproved Prop
  `foundAllIrreducibles` and prose comments). Tracked by **#7252**; item kept
  `accepted` with `issue: 7252`.

## Outcome

- `progress/items.json`: four items reclassified `accepted` → `sorry_free` with
  `lean_ref` pointers; two partials kept `accepted` with a real `issue` and
  `lean_ref` for the covered portion + a `note` scoping the residual.
- Verify passes: no `derived` item is left `accepted` with `issue: null`.
- New feature issues #7251 (L_λ irreducibility beyond Schur–Weyl range) and
  #7252 (GL₂ completeness statement) track the two genuine residuals.

## Note for future planners

This reconciliation removes six false "open gap" signals. Items 1, 2, 5, 6 are
fully covered and now read as such — do **not** create feature work for them.
Items 3 and 4 have narrowly-scoped residuals already captured by #7251 and #7252;
those two issues are the *only* remaining work for these discussions. The bulk of
each (construction + uniqueness for 3; the count arithmetic + conjugacy-class count
for 4) is done — do not re-file broad feature issues that duplicate the covered
portion.

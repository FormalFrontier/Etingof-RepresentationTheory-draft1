# Sorry Landscape Analysis — Wave 32

Generated 2026-03-24 by summarize session (issue #1687).

## Summary

**45 sorries** across 23 files. Down from 52 / 24 in wave 31 (−7 sorries, −1 file). Chapters 3, 4, 7, 8 remain 100% sorry-free. 244 of 267 Lean files (91.4%) are sorry-free. 565 of 583 items (96.9%) sorry-free.

8 PRs merged since wave 31 (#1673, #1674, #1677, #1682, #1683, #1684, #1685, #1686). Key changes:
- **PowerSumCauchyIdentity.lean** became sorry-free — `cauchyProd_coeff_perm` proved (PR #1684), making `cauchyRHS_coeff_diag` complete
- **Theorem5_25_2** went from 8 → 2 sorries (−6): `complementW_simple` proved (PR #1685), `principalSeries_simple_of_ne` proved (PR #1673), infrastructure sorries proved (PR #1682)
- **Theorem9_2_1** `hd_eq` dimension matching proved (PR #1683) — 1 sorry remains (`hσ_surj`)
- **principalSeries_decomp** proved (PR #1674) — V(μ,μ) ≅ W_μ ⊕ det·χ_μ

This is the largest single-wave improvement since wave 28→29 (−5). The GL₂(𝔽_q) principal series cluster saw the most progress.

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 1 | 2% | Standard math, clear path exists |
| Tier 2 — Hard but tractable | 3 | 7% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~24 | 53% | Missing Mathlib or project infrastructure |
| Tier 4 — Deep blockers | ~17 | 38% | SchurModule, Clifford theory, major gaps |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 31 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 29 | 9 | −7 sorries, −2 files (PowerSumCauchyIdentity now sorry-free; Theorem5_25_2 8→2) |
| Ch6 | 10 | 8 | 0 |
| Ch9 | 3 | 3 | 0 |
| Infra | 2 | 2 | 0 |

## Files That Became Sorry-Free Since Wave 31

- **PowerSumCauchyIdentity.lean** — Cauchy product coefficient extraction. PR #1684 proved `cauchyProd_coeff_perm`, making `cauchyRHS_coeff_diag` sorry-free.

## Open PRs (In-Flight Work)

No open PRs. All wave 31 in-flight PRs (#1673, #1676, #1672) have been resolved — #1673 merged, #1676 superseded by #1684, #1672 superseded by #1683.

## Tier 1 — Achievable (1 sorry)

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternatingKostka_norm_sq_eq_one` — proves ∑_ν L(λ,ν)² = 1. Key step in the Frobenius character formula.
**Status:** PowerSumCauchyIdentity is now sorry-free, providing the `cauchyRHS_coeff_diag` infrastructure. Issue #1688 created for this work. Requires connecting power sum Cauchy identity to the inner product computation.

## Tier 2 — Hard but Tractable (3 sorries)

### Theorem5_25_2 — 2 sorries
**File:** `Chapter5/Theorem5_25_2.lean`
**Nature:** Two classification results remain:
1. `complementW_iso_implies_eq` (line 2308) — W_μ ≅ W_ν ⟹ μ = ν. Requires character extraction on diagonal matrices.
2. `Theorem5_25_2_part3b` (line 2330) — V(χ₁,χ₂) ≅ V(χ'₁,χ'₂) ↔ {χ₁,χ₂}={χ'₁,χ'₂}. Character-based classification.
**Progress:** Major improvement: 8 → 2 sorries. All decomposition and irreducibility results now proved. Only uniqueness/classification remains.

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability via transfer from AB-invariant to Q₂-invariant decomposition. Issue #1637 unclaimed.

## Tier 3 — Blocked on Infrastructure (~24 sorries)

### Blocker Cluster 1: SchurModule & Characters (Ch5, ~20 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_22_1 (3), PolytabloidBasis (2), Theorem5_18_4 (4), Proposition5_21_1 (2)
**Missing:** Concrete SchurModule definition. Everything downstream blocked. This is the project's critical path.

### Blocker Cluster 2: Gabriel's Theorem Chain (Ch6, 7 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Proposition6_6_7 (1), Theorem6_5_2 (1), CoxeterInfrastructure (1)
**Status:** Unchanged. Chain still blocked on `indecomposable_reduces_to_simpleRoot` (type-changing iterated reflection functor).

### Blocker Cluster 3: Reflection Functor (Ch6, 2 sorries)
**Files:** Proposition6_6_6 (2)
**Status:** Unchanged. Remaining: arrow cases in naturality proof.

### Blocker Cluster 4: Finite-Dimensional Algebras (Ch9, 3 sorries)
**Files:** Theorem9_2_1 (1), MoritaStructural (1), Example9_4_4 (1)
**Status:** PR #1683 proved `hd_eq` (dimension matching). Only `hσ_surj` (surjectivity) remains in Theorem9_2_1. Issue #1669 unclaimed.

## Tier 4 — Deep Blockers (~17 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure. No path without ~500 lines of new theory.

### GL₂(𝔽_q) Classification residual (Ch5, 2 sorries)
**File:** Theorem5_25_2 (lines 2308, 2330)
**Status:** Dramatically reduced from 8 in wave 31. The 2 remaining sorries are classification results requiring character extraction. These are genuinely hard but self-contained.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Morita/Basic Algebra Infrastructure (2 sorries)
**Files:** Infrastructure/BasicAlgebraExistence (1), Infrastructure/MoritaStructural (1)
**Missing:** Existence of basic Morita-equivalent algebra.

### Coxeter element infrastructure (1 sorry)
**File:** CoxeterInfrastructure.lean
**Status:** `admissibleOrdering_exists` remains.

### Proposition5_22_2 (1 sorry)
**File:** Chapter5/Proposition5_22_2.lean
**Status:** Blocked on SchurModule construction.

## Definition-Level Sorries (Regression Check)

The following definition-level sorries remain. These make downstream theorems vacuous:

1. **Theorem5_22_1.lean:38** — `SchurModule` is entirely sorry'd (`FDRep k ... := sorry`)
2. **Theorem5_22_1.lean:46** — `schurPolynomial` sorry'd (`MvPolynomial ... := sorry`)
3. **Theorem5_23_2.lean:62,65,68** — `AlgIrrepGL` instances (AddCommGroup, Module, Finite) sorry'd
4. **Theorem5_23_2.lean:76,79** — `AlgIrrepGLDual` instances sorry'd
5. **Proposition5_21_1.lean:334** — `kostkaNumber` sorry'd (`ℚ := sorry`)
6. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` sorry'd (`Prop := sorry`)

No new definition-level sorries since Wave 30. Until SchurModule is constructed, ~20 downstream sorries (44%) are vacuous.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta |
|------|---------|--------|-------|
| Theorem5_23_2 | 9 | SchurModule instances + character formulas | 0 |
| Theorem5_27_1 | 5 | Mackey machine (Clifford theory) | 0 |
| Theorem5_18_4 | 4 | Young symmetrizer character formula | 0 |
| Theorem5_22_1 | 3 | SchurModule + schurPolynomial defs + theorem | 0 |
| Theorem5_25_2 | 2 | Classification: W_μ≅W_ν⟹μ=ν, V(χ₁,χ₂) classification | **−6** |
| PolytabloidBasis | 2 | Linear independence + straightening | 0 |
| Proposition5_21_1 | 2 | kostkaNumber def + character expansion | 0 |
| Problem6_1_5_theorem | 2 | IsFiniteTypeQuiver def + iff theorem | 0 |
| Proposition6_6_6 | 2 | Reflection functor naturality cases | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem statement | 0 |
| Theorem5_15_1 | 1 | Alternating Kostka norm squared | 0 |
| Proposition5_22_2 | 1 | Schur polynomial character formula | 0 |
| Problem6_9_1 | 1 | Q₂-rep decomposability | 0 |
| Corollary6_8_3 | 1 | Indecomposable → positive root | 0 |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots | 0 |
| CoxeterInfrastructure | 1 | Admissible ordering existence | 0 |
| Proposition6_6_7 | 1 | Reflection functor preserves indec | 0 |
| Theorem6_5_2 | 1 | Indecomposable decomposition uniqueness | 0 |
| Example9_4_4 | 1 | Homological dimension of polynomial ring | 0 |
| MoritaStructural (Ch9) | 1 | Morita equivalence construction | 0 |
| Theorem9_2_1 | 1 | Artin-Wedderburn block structure | 0 |
| BasicAlgebraExistence | 1 | Basic algebra existence | 0 |
| MoritaStructural (Infra) | 1 | Morita structural infrastructure | 0 |

**Removed since Wave 31:** PowerSumCauchyIdentity (was 1 sorry, now 0)

## Strategic Recommendations

1. **Highest-ROI unclaimed work:** Issue #1688 (`alternatingKostka_norm_sq_eq_one` in Theorem5_15_1) — PowerSumCauchyIdentity is now sorry-free, so the infrastructure is ready. This would close the Frobenius character formula.

2. **Next-best targets:** Theorem5_25_2 classification sorries (2 remaining) — character extraction on diagonal matrices is a self-contained problem. Theorem9_2_1 `hσ_surj` (issue #1669) — surjectivity via semisimple module decomposition.

3. **Critical path unchanged:** SchurModule remains the mega-blocker. ~20 sorries (44%) transitively blocked. This is the project's critical path and the hardest remaining work.

4. **Velocity observation:** Wave 31 → 32 saw −7 net sorries, the best single-wave improvement in recent history. The GL₂(𝔽_q) principal series work (PRs #1673, #1682, #1685) was highly productive. However, the remaining sorries are increasingly hard — most are either blocked on SchurModule infrastructure or require novel theory (Clifford, Morita).

5. **Stale comment:** Theorem5_25_2.lean:1191 contains the comment "For now, sorry the augmentation computation" but the augmentation is actually proved below. This is cosmetic only — not an actual sorry.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 29 | 61 | 26 | 562/583 (96.4%) | 2026-03-23 |
| 30 | 51 | 24 | 564/583 (96.7%) | 2026-03-23 |
| 31 | 52 | 24 | 565/583 (96.9%) | 2026-03-24 |
| 32 | 45 | 23 | 565/583 (96.9%) | 2026-03-24 |

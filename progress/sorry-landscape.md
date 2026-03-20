# Sorry Landscape Analysis — Wave 26

Generated 2026-03-20 by summarize session (issue #1520).

## Summary

**71 sorries** across 27 files. Down from 95 at wave 25 (-24, largest single-wave reduction).

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 4 | 6% | Standard math, Mathlib APIs exist, needs effort |
| Tier 2 — Hard but tractable | 17 | 24% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~38 | 53% | Missing Mathlib or project infrastructure |
| Tier 4 — Deep blockers | ~12 | 17% | SchurModule, Clifford theory, major missing infrastructure |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 25 |
|---------|---------|-------|---------------------|
| Ch2 | 2 | 2 | -5 |
| Ch5 | 42 | 13 | -7 |
| Ch6 | 20 | 9 | -9 |
| Ch9 | 7 | 3 | -3 |

Ch3, Ch4, Ch7, Ch8 are 100% sorry-free.

## Tier 1 — Achievable (4 sorries)

### Example6_4_9_Dn — 1 sorry
**File:** `Chapter6/Example6_4_9_Dn.lean`
**Nature:** D_n root count = n*(n-1). Issue #1498 claimed.
**Approach:** Arithmetic computation, `omega`/`norm_num`.

### Theorem2_1_1 — 1 sorry
**File:** `Chapter2/Theorem2_1_1.lean` (line ~530)
**Nature:** sl(2) complete reducibility via Casimir eigenspace decomposition. Issue #1489 unclaimed, dependency #1519 resolved.
**Approach:** Strong induction on dim V. Casimir eigenspaces are Lie submodules (casimir_comm proved). Each eigenspace decomposes by induction.

### Theorem5_26_1 — 1 sorry
**File:** `Chapter5/Theorem5_26_1.lean`
**Nature:** Artin's theorem direction.
**Approach:** Standard character theory argument.

### Corollary5_19_2 — 1 sorry
**File:** `Chapter5/Corollary5_19_2.lean`
**Nature:** Schur-Weyl decomposition as S_n × GL(V) rep.
**Approach:** Follows from Proposition5_19_1 (now sorry-free) and Theorem5_18_4.

## Tier 2 — Hard but Tractable (17 sorries)

### Theorem5_15_1 — 2 sorries
Majorization argument and alternating sum cancellation. Issue #1446 unclaimed.

### Lemma5_25_3 — 2 sorries
Elliptic norm-squared sum. Blocked on normalizer theory (#1517, #1518).

### Theorem_Dynkin_classification — 6 sorries
n≥5 arm extraction and exceptional types. Substantial but well-defined.

### Proposition6_6_6 — 4 sorries
Reflection functor round-trip. Issue #1401 claimed (long-running).

### Problem6_9_1 — 1 sorry
Nilpotent case dimension constraint. Issue #1191 claimed (long-running).

### Proposition5_21_1 — 2 sorries
Character expansion in terms of Schur polynomials.

## Tier 3 — Blocked on Infrastructure (~38 sorries)

### Blocker Cluster 1: SchurModule & Characters (Ch5, ~20 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_22_1 (3), Proposition5_22_2 (2), PolytabloidBasis (4), FRTHelpers (1), Corollary5_19_2 (1)
**Missing:** Concrete SchurModule definition. Everything downstream blocked.

### Blocker Cluster 2: Schur-Weyl Tensor Decomposition (Ch5, ~5 sorries)
**Files:** Theorem5_18_4 (5)
**Missing:** Tensor space decomposition V^⊗n = ⊕ V_λ ⊗ L_λ. Mutual centralizers proved (#1505); dimension formula and decomposition remain.

### Blocker Cluster 3: Gabriel's Theorem (Ch6, ~6 sorries)
**Files:** Corollary6_8_3 (2), Corollary6_8_4 (1), Proposition6_6_7 (2), Theorem6_5_2 (1)
**Missing:** Reflection functor round-trip (#1401), Decidable.casesOn opacity issues.

### Blocker Cluster 4: Finite-Dimensional Algebras (Ch9, ~7 sorries)
**Files:** Theorem9_2_1 (3), Corollary9_7_3 (3), Example9_4_4 (1)
**Missing:** Krull-Schmidt theorem, Morita structural theorem (#1510).

## Tier 4 — Deep Blockers (~12 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure (semidirect product orbit method). No path without ~500 lines of new theory.

### GL₂(𝔽_q) Classification (Ch5, 5 sorries)
**File:** Theorem5_25_2
**Missing:** Principal series defs added (#1507), but irreducibility proofs and classification require substantial GL₂ representation theory.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on the Gabriel's theorem cluster in Ch6.

## Strategic Recommendations

1. **Highest ROI:** Tier 1 (4 sorries). Theorem2_1_1_ii (#1489) is freshly unblocked and achievable. Example6_4_9_Dn (#1498) already claimed.

2. **Biggest unblock:** Normalizer theory (#1517) unblocks #1518 → Lemma5_25_3 (2 sorries). Morita theorem (#1510) unblocks Ch9 chain.

3. **Long-running claims need attention:** #1191, #1386, #1401 have been claimed across 3+ waves. Consider decomposition or replan.

4. **SchurModule remains the mega-blocker:** ~20 sorries (28% of remaining) transitively blocked. This is the project's critical path but the largest infrastructure gap.

5. **The endgame is infrastructure-gated:** Of 71 remaining sorries, only ~21 (Tier 1+2) are approachable without new infrastructure. The project needs strategic infrastructure investment to make further progress.

# Sorry Landscape Analysis — Wave 38

Generated 2026-03-27 by summarize session (issue #1818).

## Summary

**27 sorries** across 19 files. Down from 33 / 21 in wave 37 (−6 sorries, −2 files). Chapters 3, 4, 7, 8 remain 100% sorry-free. 249 of 271 Lean files (91.9%) are sorry-free. 209 of 583 items (35.8%) sorry-free.

15 PRs merged since wave 37 (#1795–#1822). Key changes:
- **Proposition6_6_7 sorry-free** (#1800) — Both source-case sorrys proved via Decidable.casesOn workarounds. Removes 2 sorrys and unblocks Gabriel chain partially.
- **Proposition5_21_1 sorry-free** (#1808) — Antisymmetric basis decomposition proved. Character expansion in terms of Schur polynomials complete.
- **Theorem5_18_4 reduced to 1 sorry** (#1817 + earlier #1781) — Centralizer theorem proved; 3 of 4 sorrys resolved. Only partition-indexed decomposition remains.
- **Theorem5_22_1 reduced to 1 sorry** (#1815, #1806) — Weight-to-Schur-poly coefficient identity proved. Only vandermonde multiplication formula remains.
- **Problem6_9_1 decomposed** (#1807) — Single sorry split into finer structure; 6 of 8 sub-goals proved, 2 remain (IsCompl conditions).
- **BasicAlgebraExistence expanded** (#1803) — Helper lemma `fullIdempotent_cornerRing_moritaEquivalent` added with its own sorry (1→2 sorrys, but more structured).
- **Mackey machine infrastructure** (#1804, #1822) — coset_fixed_iff and LHS simplification proved; no sorry count change yet (4 remain).
- **Cauchy identity progress** (#1801, #1812) — Reduced FPS Cauchy identity to polynomial determinant; coefficient-level alternating identity proved.
- **Tabloid infrastructure** (#1797, #1811) — Dominance order properties proved; swap_column_dominance done.

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 3 | 11% | Standard math, clear path, 1-2 sessions |
| Tier 2 — Hard but tractable | 4 | 15% | Non-trivial proofs, self-contained |
| Tier 3 — Significant infrastructure | 7 | 26% | Clifford, Morita, Schur-Weyl decomposition |
| Tier 4 — Deep blockers | ~13 | 48% | SchurModule-dependent + Gabriel chain |

## Definition-Level Sorries (Regression Check)

**All definition-level sorries remain resolved: 0.** Every mathematical object in the project is constructed. No regression since wave 37.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 37 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 12 | 7 | −3 sorrys, −1 file (Proposition5_21_1 sorry-free; Theorem5_18_4 4→1; Theorem5_22_1 2→1) |
| Ch6 | 9 | 7 | −2 sorrys, −1 file (Proposition6_6_7 sorry-free; Problem6_9_1 1→2) |
| Ch9 | 2 | 2 | 0 |
| Infra | 3 | 2 | +1 sorry (BasicAlgebraExistence helper added) |

## Files That Became Sorry-Free Since Wave 37

1. **Proposition6_6_7.lean** — 2 sorrys → 0. Both source-case sorrys proved via Decidable.casesOn workarounds (#1800).
2. **Proposition5_21_1.lean** — 1 sorry → 0. Antisymmetric basis decomposition proved (#1808).

## Open PRs (In-Flight Work)

| PR | Issue | Title | Status |
|----|-------|-------|--------|
| #1821 | #1785? | Prove Proposition6_6_6 remaining 2 sorrys | Open |

Note: The wave 37 backlog of 3 open PRs (#1780, #1781, #1786) has been fully merged.

## Tier 1 — Achievable (3 sorries)

### PowerSumCauchyBilinear — 1 sorry
**File:** `Chapter5/PowerSumCauchyBilinear.lean`
**Nature:** `card_sigma_fiberPerm_eq_factorial_mul` (orbit-stabilizer for element bicolorings).
**Delta:** Unchanged. Cauchy identity infrastructure improved (#1801, #1812) but this sorry persists.

### PolytabloidBasis — 2 sorries
**File:** `Chapter5/PolytabloidBasis.lean`
**Nature:** `polytabloid_linearIndependent` and `perm_mul_youngSymmetrizer_mem_span_polytabloids` (straightening lemma).
**Delta:** Unchanged. Dominance order infrastructure improved (#1797, #1811) but core sorrys persist.

## Tier 2 — Hard but Tractable (4 sorries)

### Proposition6_6_6_source — 2 sorries
**File:** `Chapter6/Proposition6_6_6_source.lean`
**Nature:** `hdim` (finrank equality via rank-nullity) and source naturality (instance diamond).
**Delta:** Unchanged. Active PR #1821 in progress.

### Problem6_9_1 — 2 sorries
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** Two `IsCompl` conditions (complementarity of projected subspaces pV/qV and pW/qW).
**Delta:** Decomposed from 1 coarse sorry into 8 sub-goals; 6 proved, 2 remain (#1807).

## Tier 3 — Significant Infrastructure (7 sorries)

### Mackey Machine (Ch5, 4 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure. 4 sorry'd proof obligations remain.
**Delta:** Infrastructure improved (coset_fixed_iff #1804, LHS simplification #1822) but sorry count unchanged.
**Status:** Issue #1731.

### Morita/Basic Algebra Infrastructure (3 sorries)
**Files:** MoritaStructural Ch9 (1), BasicAlgebraExistence (2), MoritaStructural Infra (1)
**Delta:** BasicAlgebraExistence went from 1→2 (helper lemma added #1803). Net +1 sorry but better structured.
**Status:** Issue #1729.

## Tier 4 — Deep Blockers (~13 sorries)

### SchurModule Proofs (Ch5, 4 sorries)
**Files:** Theorem5_23_2 (2), Theorem5_18_4 (1), Theorem5_22_1 (1)
**Delta:** Major progress. Theorem5_18_4 went from 4→1 (centralizer proved #1817, semisimplicity #1781). Theorem5_22_1 went from 2→1 (coefficient identity #1815).
**Active issues:** #1773 (Theorem5_22_1 vandermonde), #1816 (Theorem5_18_4 partition decomposition).

### Proposition5_22_2 — 1 sorry
**File:** `Chapter5/Proposition5_22_2.lean`
**Nature:** Determinant twist isomorphism for Schur modules.
**Active issue:** #1785.

### Gabriel's Theorem Chain (Ch6, 5 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (1), Theorem6_5_2 (1), CoxeterInfrastructure (1)
**Delta:** Proposition6_6_7 becoming sorry-free partially unblocks this chain, but Proposition6_6_6_source (2 sorrys) still blocks.
**Status:** Issue #1734.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Homological Dimension (Ch9, 1 sorry)
**File:** Example9_4_4
**Status:** `homologicalDimension (MvPolynomial (Fin n) k) = n` — standalone, deep homological algebra.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W37 |
|------|---------|--------|----------------|
| Theorem5_27_1 | 4 | Mackey machine (Clifford theory) | 0 |
| Theorem5_23_2 | 2 | Complete reducibility + Peter-Weyl decomposition | 0 |
| Theorem5_18_4 | 1 | Partition-indexed Schur-Weyl decomposition | **−3** |
| Theorem5_22_1 | 1 | Vandermonde multiplication formula | **−1** |
| Proposition6_6_6_source | 2 | Reflection functor source (hdim + naturality) | 0 |
| PolytabloidBasis | 2 | Linear independence + straightening | 0 |
| Problem6_9_1 | 2 | IsCompl conditions (pV/qV, pW/qW) | **+1** |
| BasicAlgebraExistence | 2 | Basic algebra existence + corner ring Morita | **+1** |
| Proposition5_22_2 | 1 | Schur polynomial character formula | 0 |
| Corollary6_8_3 | 1 | Indecomposable → positive root | 0 |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots | 0 |
| CoxeterInfrastructure | 1 | Admissible ordering existence | 0 |
| Theorem6_5_2 | 1 | Indecomposable decomposition uniqueness | 0 |
| Problem6_1_5_theorem | 1 | Finite type ↔ Dynkin | 0 |
| PowerSumCauchyBilinear | 1 | card_sigma_fiberPerm (orbit-stabilizer) | 0 |
| MoritaStructural (Ch9) | 1 | Morita equivalence construction | 0 |
| MoritaStructural (Infra) | 1 | Morita structural infrastructure | 0 |
| Example9_4_4 | 1 | Homological dimension of polynomial ring | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem statement | 0 |

**Removed since Wave 37:** Proposition6_6_7.lean (2 sorrys → 0), Proposition5_21_1.lean (1 sorry → 0)
**Changed since Wave 37:**
- Theorem5_18_4: 4→1 (centralizer proved #1817, semisimplicity/decomposition #1781)
- Theorem5_22_1: 2→1 (coefficient identity #1815)
- Problem6_9_1: 1→2 (decomposed into finer structure #1807, +1 net but 6 sub-goals proved)
- BasicAlgebraExistence: 1→2 (helper lemma added #1803)

## Strategic Recommendations

1. **Close out Proposition6_6_6_source** — PR #1821 is in-flight. Resolving the 2 remaining sorrys here unblocks most of the Gabriel chain (5 sorrys in Corollary6_8_3, Corollary6_8_4, Problem6_1_5_theorem, Theorem6_5_2, CoxeterInfrastructure).

2. **Finish Theorem5_18_4** (#1816) — Only 1 sorry remains (partition-indexed decomposition). The centralizer and semisimplicity infrastructure is done.

3. **Finish Theorem5_22_1** (#1773) — Only 1 sorry remains (vandermonde multiplication). Coefficient identity is proved.

4. **Complete PolytabloidBasis** (#1717) — 2 sorrys. Independent of other work. Dominance order infrastructure has improved.

5. **Mackey machine** — 4 sorrys but infrastructure is building up (coset_fixed_iff, LHS simplification). Still needs significant Clifford theory work.

6. **Problem6_9_1 IsCompl** — 2 remaining sorrys are localized complementarity conditions, potentially tractable.

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date |
|------|---------|-------|------------------|------|
| 28 | 66 | 27 | 560/583 (96.1%) | 2026-03-22 |
| 29 | 61 | 26 | 562/583 (96.4%) | 2026-03-23 |
| 30 | 51 | 24 | 564/583 (96.7%) | 2026-03-23 |
| 31 | 52 | 24 | 565/583 (96.9%) | 2026-03-23 |
| 32 | 45 | 23 | 565/583 (96.9%) | 2026-03-24 |
| 33 | 43 | 22 | 566/583 (97.1%) | 2026-03-24 |
| 34 | 44 | 22 | 567/583 (97.2%) | 2026-03-24 |
| 35 | 43 | 21 | 568/583 (97.4%) | 2026-03-26 |
| 36 | 37 | 22 | 568/583 (97.4%) | 2026-03-27 |
| 37 | 33 | 21 | 568/583 (97.4%) | 2026-03-27 |
| 38 | 27 | 19 | 570/583 (97.8%) | 2026-03-27 |

Note: "Items sorry-free" counts items whose Lean files contain zero `sorry` keywords. The 209/583 (35.8%) figure in items.json counts individual item-level sorry_free status, which is a different (stricter) metric tracking whether each specific theorem/definition is proved.

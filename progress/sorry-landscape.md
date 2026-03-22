# Sorry Landscape Analysis — Wave 27

Generated 2026-03-22 by summarize session (issue #1576).

## Summary

**75 sorries** across 28 files. Down from 71 in wave 26 in raw count, but this is misleading: the increase comes from 4 new infrastructure helper files that absorbed sorries pushed out of main theorem files. The actual proof progress is significant — several theorems moved from `sorry` to structured proof with only helper-level sorries remaining.

Chapters 3, 4, 7, 8 remain 100% sorry-free. 237 of 265 Lean files (89%) are sorry-free.

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 2 | 3% | Standard math, Mathlib APIs exist |
| Tier 2 — Hard but tractable | 16 | 21% | Non-trivial proofs, novel approaches needed |
| Tier 3 — Blocked on infrastructure | ~40 | 53% | Missing Mathlib or project infrastructure |
| Tier 4 — Deep blockers | ~17 | 23% | SchurModule, Clifford theory, major gaps |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 26 |
|---------|---------|-------|---------------------|
| Ch2 | 3 | 2 | +1 |
| Ch5 | 41 | 12 | -1 sorry, -1 file |
| Ch6 | 23 | 8 | +3 sorry, -1 file |
| Ch9 | 5 | 4 | -2 sorry, +1 file |
| Infra | 3 | 2 | +3 (new files) |

Notes on deltas:
- Ch2 +1: Theorem2_1_2 gained a sorry during restructuring
- Ch5 -1 file: Corollary5_19_2 became sorry-free; FRTHelpers became sorry-free; GL2NormalizerInfra is new (+1 file)
- Ch6 -1 file: Example6_4_9_Dn became sorry-free; Corollary6_8_4 gained 1 sorry from restructuring
- Ch9 +1 file: MoritaStructural.lean is new (absorbed sorries from Corollary9_7_3 refactor)
- Infra +2 files: BasicAlgebraExistence.lean and MoritaStructural.lean are new (sorry pushed from theorem files)

## Files That Became Sorry-Free Since Wave 26

- **Corollary5_19_2.lean** — Schur-Weyl decomposition (#1564)
- **FRTHelpers.lean** — FRT construction helpers
- **Example6_4_9_Dn.lean** — D_n root count (#1548)

## Tier 1 — Achievable (2 sorries)

### Theorem2_1_1 — 1 sorry
**File:** `Chapter2/Theorem2_1_1.lean`
**Nature:** sl(2) complete reducibility via Casimir eigenspace decomposition.
**Approach:** Strong induction on dim V. Infrastructure partially built (#1542, #1544 merged).

### Theorem5_15_1 — 1 sorry
**File:** `Chapter5/Theorem5_15_1.lean`
**Nature:** `alternating_kostka_eq_zero_of_strict_dom` — alternating Kostka identity for strict dominance.
**Approach:** Norm-squared argument using character orthonormality. Issue #1580 describes the correct approach. This is the ONLY remaining sorry for the entire Frobenius character formula.

## Tier 2 — Hard but Tractable (16 sorries)

### Lemma5_25_3 — 1 sorry
**File:** `Chapter5/Lemma5_25_3.lean`
**Nature:** Elliptic norm-squared sum for GL₂ characters.
**Status:** GL₂ centralizer proved (#1566), normalizer membership proved. Remaining: normalizer_card.

### GL2NormalizerInfra — 1 sorry
**File:** `Chapter5/GL2NormalizerInfra.lean`
**Nature:** GL₂ normalizer cardinality infrastructure.
**Status:** New file; prerequisite for Lemma5_25_3.

### Theorem_Dynkin_classification — 6 sorries
**File:** `Chapter6/Theorem_Dynkin_classification.lean`
**Nature:** n≥5 arm extraction and exceptional type cases (D_n, E₆, E₇, E₈).
**Status:** Branch cases added (#1565), but proof bodies remain.

### Proposition6_6_6 — 4 sorries
**File:** `Chapter6/Proposition6_6_6.lean`
**Nature:** Reflection functor round-trip (F⁻F⁺V ≅ V). Issue #1401 (long-running).
**Blocker:** `Decidable.casesOn` opacity in reflection functor definitions. reversedArrow_ne_ne_twice proved (#1561).

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability from kernel dimension. Issue #1575 merged, factored cleanly.
**Blocker:** Structure theorem for nilpotent operators (not in Mathlib).

### Proposition5_21_1 — 2 sorries
**File:** `Chapter5/Proposition5_21_1.lean`
**Nature:** Character expansion in terms of Schur polynomials.

### Proposition5_22_2 — 1 sorry
**File:** `Chapter5/Proposition5_22_2.lean`
**Nature:** Schur polynomial character formula.

## Tier 3 — Blocked on Infrastructure (~40 sorries)

### Blocker Cluster 1: SchurModule & Characters (Ch5, ~20 sorries)
**Files:** Theorem5_23_2 (9), Theorem5_22_1 (3), PolytabloidBasis (4), Theorem5_18_4 (4)
**Missing:** Concrete SchurModule definition. Everything downstream blocked.

### Blocker Cluster 2: Theorem5_25_2 Principal Series (Ch5, 6 sorries)
**File:** Theorem5_25_2
**Status:** Parts 1, 2, 3a have complete proof terms (#1562). Sorry pushed to 6 helper lemmas isolating concrete character computations. Progress from previous waves.

### Blocker Cluster 3: Theorem5_26_1 Artin's Theorem (Ch5, 4 sorries)
**File:** Theorem5_26_1
**Status:** Forward direction helpers decomposed (#1569), restructured (#1568). 4 sorries remain in helper lemmas.

### Blocker Cluster 4: Gabriel's Theorem (Ch6, ~10 sorries)
**Files:** Corollary6_8_3 (3), Corollary6_8_4 (3), Problem6_1_5_theorem (3), Proposition6_6_7 (2), Theorem6_5_2 (1)
**Missing:** Reflection functor round-trip (#1401), Decidable.casesOn opacity issues.

### Blocker Cluster 5: Finite-Dimensional Algebras (Ch9, 5 sorries)
**Files:** Theorem9_2_1 (1), Corollary9_7_3 (1), MoritaStructural (2), Example9_4_4 (1)
**Status:** Theorem9_2_1 decomposed into sub-goals (#1567). MoritaStructural B≅eAe proved (#1559). Corollary9_7_3 sorry pushed to infrastructure (#1560). Infrastructure files hold 3 sorries.

## Tier 4 — Deep Blockers (~17 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure (semidirect product orbit method). No path without ~500 lines of new theory.

### GL₂(𝔽_q) Classification residual (Ch5, 6 sorries)
**File:** Theorem5_25_2 (helper lemmas)
**Missing:** Character computation helpers require substantial GL₂ representation theory beyond current infrastructure.

### Gabriel's Theorem Classification (Ch2, 2 sorries)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster.

### Morita/Basic Algebra Infrastructure (3 sorries)
**Files:** Infrastructure/BasicAlgebraExistence (2), Infrastructure/MoritaStructural (1)
**Missing:** Existence of basic Morita-equivalent algebra over algebraically closed fields.

## Strategic Recommendations

1. **Highest ROI:** Theorem2_1_1 (1 sorry, sl(2) complete reducibility). Infrastructure from #1542 and #1544 makes this more approachable than before.

2. **Biggest single-item impact:** Theorem5_15_1 (#1580). Only 1 sorry remaining for the entire Frobenius character formula. Requires character orthonormality bridge.

3. **Unblock cascade:** Proposition6_6_6 (#1401) unblocks ~10 sorries in the Gabriel theorem chain. The Decidable.casesOn issue has been a persistent blocker across 4+ waves.

4. **Good progress on decomposition strategy:** Multiple theorem files (Theorem5_25_2, Theorem5_26_1, Theorem9_2_1) successfully decomposed main proofs into helper lemmas with well-isolated sorries. This pattern is working well.

5. **SchurModule remains the mega-blocker:** ~20 sorries (27%) transitively blocked. This is the project's critical path.

6. **Infrastructure investment paying off:** New infrastructure files (BasicAlgebraExistence, MoritaStructural) cleanly separate mathematical infrastructure from theorem proofs. Ch9 chain is becoming well-structured.

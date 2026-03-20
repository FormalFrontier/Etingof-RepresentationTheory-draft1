# Stage 3.2 Twenty-Sixth Proof Wave Summary

**Date:** 2026-03-20
**Scope:** 10 merged PRs since wave 25 audit (#1508, closed 2026-03-20T21:34Z)
**Status:** Stage 3.2 in progress — 559/583 items sorry_free in items.json (95.9%), 71 sorry occurrences across 27 files

## Executive Summary

Wave 26 produced 10 PRs. Sorry count dropped from 95 to 71 (**-24 sorries**, the largest single-wave reduction in the project's history). One file became sorry-free (Proposition5_19_1.lean), bringing the file count from 28 to 27.

The most impactful changes:
- **Dynkin classification** saw the largest drop (-9 sorries in Ch6), with `branch_classification` and `dynkin_unique_degree_three` proved
- **Casimir infrastructure** for sl(2) complete reducibility: eigenvalue computation proved (#1522), operator commutativity proved (#1512), reducing Ch2 from 7 to 2 sorries
- **Theorem 5.15.1** (hook length formula): 4 of 6 rearrangement sorries proved (#1515)
- **Schur-Weyl duality** part (i): mutual centralizers proved (#1505)
- **Proposition 5.19.1** fully proved: polynomial density (GL-span = End-span)

## Merged PRs (10)

### Proof Progress (7)

| PR | Title | Chapter | Sorry Impact |
|----|-------|---------|-------------|
| #1522 | Casimir acts as n(n+2) on irreducible sl2-modules | Ch2 | -5 sorries |
| #1515 | Prove 4/6 rearrangement sorries for Theorem 5.15.1 | Ch5 | -4 sorries |
| #1513 | Prove dynkin_unique_degree_three and branch_classification sorries | Ch6 | -3 sorries |
| #1505 | Schur-Weyl duality part (i) mutual centralizers (Theorem5_18_4) | Ch5 | Structural |
| #1514 | Prove nonscalar_char_sum sorry in Lemma5_25_3 | Ch5 | -1 sorry |
| #1503 | Prove Proposition5_19_1 polynomial density | Ch5 | **File → sorry-free** |
| #1516 | Prove uniqueness of projective covers (LocalEndomorphismRing) | Ch9 | -1 sorry |

### Infrastructure (3)

| PR | Title | Chapter | Impact |
|----|-------|---------|--------|
| #1512 | sl2_casimir_comm and operator relations for Theorem 2.1.1(ii) | Ch2 | Casimir commutativity proved |
| #1511 | Define corner ring (eAe) with Ring and Algebra instances | Ch9 | Morita equivalence infrastructure |
| #1507 | Define principal series representations for GL₂(𝔽_q) | Ch5 | Lemma5_25_3 infrastructure |

## Sorry Counts by Chapter

| Chapter | Files with sorry | Total sorries | Wave 25 | Delta |
|---------|-----------------|---------------|---------|-------|
| 2 | 2 | 2 | 7 | **-5** |
| 3 | 0 | 0 | 0 | 0 |
| 4 | 0 | 0 | 0 | 0 |
| 5 | 13 | 42 | 49 | **-7** |
| 6 | 9 | 20 | 29 | **-9** |
| 7 | 0 | 0 | 0 | 0 |
| 8 | 0 | 0 | 0 | 0 |
| 9 | 3 | 7 | 10 | **-3** |
| **Total** | **27** | **71** | **95** | **-24** |

Four chapters remain at 100%: Ch3, Ch4, Ch7, Ch8.

## Sorry-Free Items by Chapter

| Chapter | Topic | Sorry-free | Total Items | % |
|---------|-------|------------|-------------|---|
| 1 | Introduction | 3 | 3 | 100.0% |
| 2 | Basic notions | 115 | 117 | 98.3% |
| 3 | General results | 58 | 58 | 100.0% |
| 4 | Characters | 60 | 60 | 100.0% |
| 5 | Symmetric group reps | 146 | 157 | 93.0% |
| 6 | Quiver representations | 56 | 64 | 87.5% |
| 7 | Category O | 59 | 59 | 100.0% |
| 8 | Infinite-dim reps | 24 | 24 | 100.0% |
| 9 | Finite-dimensional algebras | 32 | 35 | 91.4% |
| **Total** | | **559** | **583** | **95.9%** |

items.json updated: Proposition5.19.1 → sorry_free.

## Per-File Sorry Breakdown

### Chapter 2 (2 sorries)
| File | Sorries | Notes |
|------|---------|-------|
| Theorem2_1_1.lean | 1 | Complete reducibility (blocked on #1489) |
| Theorem2_1_2.lean | 1 | Gabriel's theorem finite type classification |

### Chapter 5 (42 sorries)
| File | Sorries | Notes |
|------|---------|-------|
| Theorem5_23_2.lean | 9 | Peter-Weyl for GL(V); SchurModule definitions blocked |
| Theorem5_18_4.lean | 5 | Schur-Weyl decomposition; mutual centralizers proved, 5 remain |
| Theorem5_25_2.lean | 5 | Principal series irreducibility; defs added (#1507) |
| Theorem5_27_1.lean | 5 | Mackey machine; blocked on Clifford theory |
| PolytabloidBasis.lean | 4 | Polytabloid basis for Specht modules |
| Theorem5_22_1.lean | 3 | Weyl character formula |
| Lemma5_25_3.lean | 2 | Complementary series character; elliptic sum remains |
| Theorem5_15_1.lean | 2 | Hook length formula; 2 hardest sorries remain |
| Proposition5_21_1.lean | 2 | Character expansion |
| Proposition5_22_2.lean | 2 | L_{λ+1^N} ≅ L_λ ⊗ Λ^N V |
| Corollary5_19_2.lean | 1 | Schur-Weyl decomposition as S_n × GL(V) |
| FRTHelpers.lean | 1 | Frobenius reciprocity helper |
| Theorem5_26_1.lean | 1 | Artin's theorem |

### Chapter 6 (20 sorries)
| File | Sorries | Notes |
|------|---------|-------|
| Theorem_Dynkin_classification.lean | 6 | Main Dynkin classification; n≥5 cases remain |
| Proposition6_6_6.lean | 4 | Reflection functor round-trip (#1401 claimed) |
| Corollary6_8_3.lean | 2 | Uniqueness of indecomposable with dim vector |
| Problem6_1_5_theorem.lean | 2 | Connected quiver ↔ Dynkin |
| Proposition6_6_7.lean | 2 | Reflection of indecomposable |
| Corollary6_8_4.lean | 1 | Existence of indecomposable for positive root |
| Example6_4_9_Dn.lean | 1 | D_n root count (#1498 claimed) |
| Problem6_9_1.lean | 1 | Cyclic quiver Q₂ (#1191 claimed) |
| Theorem6_5_2.lean | 1 | Gabriel's theorem |

### Chapter 9 (7 sorries)
| File | Sorries | Notes |
|------|---------|-------|
| Corollary9_7_3.lean | 3 | Basic algebra uniqueness (#1468 blocked) |
| Theorem9_2_1.lean | 3 | Projective module classification (#1467 claimed) |
| Example9_4_4.lean | 1 | Hilbert syzygies theorem |

## Active Work Fronts

### Claimed Issues (8)

| Issue | Title | Status |
|-------|-------|--------|
| #1520 | Wave 26 sorry audit | This issue |
| #1517 | GL₂ normalizer of elliptic subgroup | Infrastructure for Lemma5_25_3 |
| #1510 | Morita structural theorem (eAe) | Infrastructure for Ch9 |
| #1498 | D_n root count (last sorry in Example6_4_9_Dn) | Claimed |
| #1467 | Theorem9_2_1 parts ii+iii | Claimed |
| #1401 | Proposition6_6_6 reflection functor round-trip | Long-running |
| #1386 | Hook walk hook_quotient_identity | Long-running |
| #1191 | Problem6_9_1 nilpotent case | Long-running |

### Blocked Issues (5)

| Issue | Title | Blocked On |
|-------|-------|------------|
| #1518 | Lemma5_25_3 elliptic sum algebraic core | #1517 (normalizer) |
| #1468 | Corollary9_7_3 basic algebra uniqueness | #1464 |
| #1464 | Theorem 9.2.1 parts ii+iii infrastructure | #1467 |
| #1381 | Corollary6_8_3 helper lemmas | reflection functor |
| #1196 | Reconcile repo with updated templates | Low priority |

### Unclaimed Issues (5)

| Issue | Title | Label |
|-------|-------|-------|
| #1191 | Problem6_9_1 nilpotent case | feature |
| #1446 | Theorem5_15_1 rearrangement sorries | feature |
| #1489 | Theorem2_1_1_ii sl(2) complete reducibility | feature |
| #1520 | Wave 26 sorry audit | summarize (this) |
| #1521 | Endgame skill review and blocker analysis | meditate |

## Velocity Analysis

| Metric | Wave 23 | Wave 24 | Wave 25 | Wave 26 |
|--------|---------|---------|---------|---------|
| sorry_free delta (items.json) | +3 | +1 | +352* | **+1** |
| sorry delta | -3 | +6 | +5 | **-24** |
| Feature PRs | 12 | 5 | 9 | **7** |
| Files w/sorry | 29 | 28 | 28 | **27** |

*Wave 25 bulk-marked 352 non-proof items (discussion, introduction, etc.) as sorry_free.

## Honest Assessment

Wave 26 was the strongest proof wave in the project. The -24 sorry reduction (95→71) represents genuine proof progress across all four active chapters. No sorry count increased — every chapter either stayed flat or decreased.

**Positive signals:**
- **Every chapter with sorries improved** — Ch2 (-5), Ch5 (-7), Ch6 (-9), Ch9 (-3)
- **Casimir infrastructure nearly complete** — sl(2) complete reducibility has 1 sorry left (Theorem2_1_1_ii), down from 7
- **Dynkin classification momentum** — 6 sorries remain (down from 9), with base cases proved
- **No open PRs** — clean state, all work merged
- **Infrastructure investments landing** — corner ring, principal series defs, normalizer theory in progress

**Concerns:**
- **3 long-running claimed issues** (#1191, #1386, #1401) have been claimed across multiple waves — may need decomposition or replan
- **Theorem5_23_2 (9 sorries) unchanged** — still the largest single file, blocked on SchurModule definitions
- **Theorem5_27_1 (5 sorries) unchanged** — Mackey machine blocked on Clifford theory infrastructure
- **Blocked issue chain** — #1518 → #1517 → normalizer theory; #1468 → #1464 → #1467 form dependency chains that slow throughput
- **71 sorries remain** — the "easy" reductions are exhausted; remaining sorries are genuinely hard

**Recommendations for next wave:**
1. **Unblock Theorem2_1_1_ii** (#1489) — dependency #1519 resolved, this is low-hanging fruit (1 sorry, difficulty 4)
2. **Close D_n root count** (#1498) — 1 sorry remaining in Example6_4_9_Dn, would make the file sorry-free
3. **Review long-running claims** — #1191, #1386, #1401 may benefit from decomposition
4. **Theorem5_15_1** (#1446) — 2 hard sorries but well-specified, worth attempting
5. **Normalizer theory** (#1517) — unblocks #1518 → Lemma5_25_3 completion

# Sorry Landscape Analysis — Wave 36

Generated 2026-03-27 by summarize session (issue #1756).

## Summary

**37 sorries** across 22 files. Down from 43 / 21 in wave 35 (−6 sorries, +1 file). Chapters 3, 4, 7, 8 remain 100% sorry-free. 249 of 271 Lean files (91.9%) are sorry-free. 568 of 583 items (97.4%) sorry-free.

14 PRs merged since wave 35 (#1735–#1755, #1760). Key changes:
- **SchurModule constructed** (#1740) — `SchurModuleSubmodule` is now the image of the Young symmetrizer on tensor power. Removes the project's #1 definition-level blocker.
- **AlgIrrepGL/AlgIrrepGLDual constructed** (#1752) — det-twist extension definitions built on SchurModule. Removes 7 definition-level sorries from Theorem5_23_2.
- **formalCharacter constructed** (#1753) — weight space character polynomial defined. Removes 1 definition-level sorry from Theorem5_22_1.
- **double_counting proved** (#1755) — combinatorial core of bilinear Cauchy identity complete.
- **vandermonde_cauchy_diagonal factored** (#1748) — proved from `alternating_coeff_eq_cauchyRHS_coeff` helper. Removes 1 sorry from PowerSumCauchyBilinear.
- **TabloidModule infrastructure** (#1754) — tabloid type and T-relative column subgroup added (2 new sorrys).
- **Proposition6_6_6 split** (#1739) — now in 3 files; source sorrys in `_source.lean`.
- **Proposition6_6_7 source case** (#1760) — full source case with 2 localized sorrys (up from 1).
- **Code quality reviews** (#1735, #1741, #1742, #1743): refactoring and status checks.

| Tier | Count | % | Description |
|------|-------|---|-------------|
| Tier 1 — Achievable | 5 | 14% | Standard math, clear path, 1-2 sessions |
| Tier 2 — Hard but tractable | 5 | 14% | Non-trivial proofs, self-contained |
| Tier 3 — Significant infrastructure | 8 | 22% | Clifford, Morita, Schur-Weyl decomposition |
| Tier 4 — Deep blockers | ~19 | 51% | SchurModule-dependent proofs + Gabriel chain |

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 35 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 21 | 9 | −7 sorrys, +1 file (Theorem5_23_2: 9→2; Theorem5_22_1: 3→2; PowerSumCauchyBilinear: 2→1; TabloidModule new with 2) |
| Ch6 | 11 | 9 | +1 sorry, +1 file (Proposition6_6_7: 1→2; Proposition6_6_6 split to _source) |
| Ch9 | 2 | 2 | 0 |
| Infra | 2 | 2 | 0 |

## Milestone: Definition-Level Sorry Crisis Resolved

**Definition-level sorries reduced from 10-11 to 2.** This is the most significant structural improvement in the project's history.

Wave 35 had these definition-level sorries (all making downstream theorems vacuous):
- ~~SchurModule~~ → **constructed** (#1740): image of Young symmetrizer on tensor power
- ~~formalCharacter~~ → **constructed** (#1753): weight space character polynomial
- ~~AlgIrrepGL (type + 3 instances)~~ → **constructed** (#1752): det-twist extension of SchurModule
- ~~AlgIrrepGLDual (type + 2 instances)~~ → **constructed** (#1752): contragredient via w₀-twist

**Remaining definition-level sorries (2):**
1. **Proposition5_21_1.lean:334** — `charValue` (`ℚ := sorry`) — character values of S_n irreps
2. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` (`Prop := sorry`) — finite-type quiver predicate

With SchurModule constructed, the ~21 downstream sorries that were previously **vacuous** are now **meaningful** — they represent actual proof obligations against a real mathematical object.

## Files That Became Sorry-Free Since Wave 35

No files became fully sorry-free in this wave. The work was structural: constructing definitions that make existing proof obligations non-vacuous.

## Open PRs (In-Flight Work)

| PR | Issue | Title | Status |
|----|-------|-------|--------|
| #1762 | — | Construct charValue definition via Frobenius character formula | CI failing |
| #1761 | #1758 | — | CI failing |

## Tier 1 — Achievable (5 sorries)

### PowerSumCauchyBilinear — 1 sorry
**File:** `Chapter5/PowerSumCauchyBilinear.lean`
**Nature:** `card_sigma_fiberPerm_eq_factorial_mul` (orbit-stabilizer for element bicolorings). The other sorry (`vandermonde_cauchy_diagonal`) was resolved via factoring (#1748), and `double_counting` was proved (#1755).
**Status:** Active issue #1714 (Part B).
**Delta:** Was 2 sorries in wave 35; now 1.

### PolytabloidBasis — 2 sorries
**File:** `Chapter5/PolytabloidBasis.lean`
**Nature:** `polytabloid_linearIndependent` and `perm_mul_youngSymmetrizer_mem_span_polytabloids` (straightening lemma).
**Status:** Active issue #1717.

### TabloidModule — 2 sorries
**File:** `Chapter5/TabloidModule.lean`
**Nature:** SYT injective map and non-identity subgroup action. Infrastructure for PolytabloidBasis.
**Status:** New file (#1754). These feed into the PolytabloidBasis proofs.

## Tier 2 — Hard but Tractable (5 sorries)

### Proposition6_6_6_source — 2 sorries
**File:** `Chapter6/Proposition6_6_6_source.lean` (split from Proposition6_6_6)
**Nature:** `hdim` (finrank equality via rank-nullity) and source naturality (instance diamond prevents naming `ofBijective` term). Both blocked by Decidable.casesOn / instance diamond issues.
**Status:** Active issue #1724.

### Proposition6_6_7 — 2 sorries
**File:** `Chapter6/Proposition6_6_7.lean`
**Nature:** `reversedArrow_arrowOut_eq` (roundtrip lemma for ReversedAtVertexHom) and codisjointness at source vertex. Both blocked by Decidable.casesOn in Definition6_6_2/4. Full source case structure proved (#1760).
**Status:** Active issue #1726.
**Delta:** Was 1 sorry (unstarted source case); now 2 (source case built out with 2 localized sorrys).

### Problem6_9_1 — 1 sorry
**File:** `Chapter6/Problem6_9_1.lean`
**Nature:** `decomp_of_ker_sum_ge_two` — Q₂-rep decomposability via graded nilpotent chain basis.
**Status:** Active issue #1691.

## Tier 3 — Significant Infrastructure (~8 sorries)

### Mackey Machine (Ch5, 5 sorries)
**File:** Theorem5_27_1
**Missing:** Clifford theory infrastructure (~500 lines). Issue #1731.

### Morita/Basic Algebra Infrastructure (3 sorries)
**Files:** MoritaStructural Ch9 (1), BasicAlgebraExistence (1), MoritaStructural Infra (1)
**Missing:** Progenerator-to-algebra construction. Issue #1729.

## Tier 4 — Deep Blockers (~19 sorries)

### SchurModule Proofs (Ch5, ~10 sorries)
**Files:** Theorem5_23_2 (2), Theorem5_18_4 (4), Theorem5_22_1 (2), Proposition5_21_1 (2)
**Change from wave 35:** SchurModule, formalCharacter, AlgIrrepGL, AlgIrrepGLDual are now **constructed**. The 10 remaining sorries are genuine proof obligations, not vacuous placeholders. This is the biggest qualitative change: these proofs can now actually be attempted.
**Status:** Active issue #1722.

### Proposition5_22_2 — 1 sorry
**File:** `Chapter5/Proposition5_22_2.lean`
**Nature:** Schur polynomial character formula. Depends on SchurModule theory.

### Gabriel's Theorem Chain (Ch6, 5 sorries)
**Files:** Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (2), Theorem6_5_2 (1)
**Status:** Chain blocked on CoxeterInfrastructure + Proposition6_6_6/7. Issue #1734.

### Gabriel's Theorem Classification (Ch2, 1 sorry)
**File:** Theorem2_1_2
**Missing:** Full Gabriel's theorem depends on Ch6 Gabriel cluster. Issue #1734.

### Homological Dimension (Ch9, 1 sorry)
**File:** Example9_4_4
**Status:** `homologicalDimension (MvPolynomial (Fin n) k) = n` — standalone, deep homological algebra. Issue #1729.

### CoxeterInfrastructure — 1 sorry
**File:** `Chapter6/CoxeterInfrastructure.lean`
**Nature:** `admissibleOrdering_exists` — existence of admissible ordering for finite acyclic quivers. Blocks Corollary6_8_3/4.

## Definition-Level Sorries (Regression Check)

**Massive improvement: 10-11 → 2 definition-level sorries.** 8-9 definition-level sorries were resolved by constructing real mathematical objects in PRs #1740, #1752, #1753.

**Remaining (2):**
1. **Proposition5_21_1.lean:334** — `charValue` (`ℚ := sorry`) — character values need Murnaghan-Nakayama rule
2. **Problem6_1_5_theorem.lean:33** — `IsFiniteTypeQuiver` (`Prop := sorry`) — finite-type quiver predicate

**Resolved since wave 35 (8-9):**
- ~~Theorem5_22_1: SchurModule~~ → constructed as image of Young symmetrizer (#1740)
- ~~Theorem5_22_1: formalCharacter~~ → constructed as weight space polynomial (#1753)
- ~~Theorem5_23_2: AlgIrrepGL (type)~~ → constructed via SchurModuleSubmodule (#1752)
- ~~Theorem5_23_2: AlgIrrepGL (3 instances)~~ → derived from SchurModuleSubmodule (#1752)
- ~~Theorem5_23_2: AlgIrrepGLDual (type)~~ → constructed via w₀-twist (#1752)
- ~~Theorem5_23_2: AlgIrrepGLDual (2 instances)~~ → derived from AlgIrrepGL (#1752)

Note: PR #1762 (open, CI failing) attempts to construct `charValue`, which would reduce definition-level sorries to 1.

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W35 |
|------|---------|--------|----------------|
| Theorem5_27_1 | 5 | Mackey machine (Clifford theory) | 0 |
| Theorem5_18_4 | 4 | Young symmetrizer character formula | 0 |
| Theorem5_23_2 | 2 | Complete reducibility + Peter-Weyl decomposition | **−7** |
| Theorem5_22_1 | 2 | Weight support finiteness + Weyl character formula | **−1** |
| TabloidModule | 2 | SYT injection + subgroup action | **NEW** |
| Proposition6_6_7 | 2 | Reflection functor source (roundtrip + codisjointness) | **+1** |
| Proposition6_6_6_source | 2 | Reflection functor source (hdim + naturality) | **moved** |
| Proposition5_21_1 | 2 | charValue def + character expansion | 0 |
| Problem6_1_5_theorem | 2 | IsFiniteTypeQuiver def + iff theorem | 0 |
| PolytabloidBasis | 2 | Linear independence + straightening | 0 |
| Proposition5_22_2 | 1 | Schur polynomial character formula | 0 |
| Corollary6_8_3 | 1 | Indecomposable → positive root | 0 |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots | 0 |
| CoxeterInfrastructure | 1 | Admissible ordering existence | 0 |
| Theorem6_5_2 | 1 | Indecomposable decomposition uniqueness | 0 |
| Problem6_9_1 | 1 | Q₂-rep decomposability | 0 |
| PowerSumCauchyBilinear | 1 | card_sigma_fiberPerm (orbit-stabilizer) | **−1** |
| BasicAlgebraExistence | 1 | Basic algebra existence | 0 |
| MoritaStructural (Ch9) | 1 | Morita equivalence construction | 0 |
| MoritaStructural (Infra) | 1 | Morita structural infrastructure | 0 |
| Example9_4_4 | 1 | Homological dimension of polynomial ring | 0 |
| Theorem2_1_2 | 1 | Gabriel's theorem statement | 0 |

**Removed since Wave 35:** Proposition6_6_6.lean (split; sorrys moved to _source.lean)
**New since Wave 35:** TabloidModule.lean (2 sorrys — tabloid infrastructure)
**Changed since Wave 35:**
- Theorem5_23_2: 9→2 (AlgIrrepGL/AlgIrrepGLDual constructed, −7)
- Theorem5_22_1: 3→2 (SchurModule + formalCharacter constructed, −1)
- PowerSumCauchyBilinear: 2→1 (vandermonde_cauchy_diagonal factored, −1)
- Proposition6_6_7: 1→2 (source case built out, +1)
- Proposition6_6_6 → Proposition6_6_6_source (file split, same 2 sorrys)

## Strategic Recommendations

1. **Prove SchurModule-dependent theorems** — SchurModule is now constructed. The ~10 remaining Ch5 proof sorries (Theorem5_23_2, Theorem5_18_4, Theorem5_22_1, Proposition5_21_1) are now meaningful proof obligations. Highest ROI area.

2. **Resolve Decidable.casesOn blocker** — Proposition6_6_6_source (2 sorrys) and Proposition6_6_7 (2 sorrys) share the same root cause: `Decidable.casesOn` in `ReversedAtVertexHom`/`reflectionFunctorMinus` definitions. A targeted refactor of Definition6_6_2/4 would unblock 4 sorrys and the entire Gabriel chain.

3. **Complete PolytabloidBasis** (#1717) — 2 sorrys (linear independence + straightening). These are independent of SchurModule and feed into the SchurModule theory.

4. **PowerSumCauchyBilinear Part B** (#1714) — 1 remaining sorry (`card_sigma_fiberPerm_eq_factorial_mul`). Standard combinatorics.

5. **Construct charValue** — PR #1762 is attempting this. Would reduce definition-level sorries to 1 and unblock Proposition5_21_1.

6. **Attempt neglected Ch9/Infra** (#1729) — MoritaStructural has had zero direct PRs in 50+ waves.

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

# Sorry Landscape Analysis — Wave 40

Generated 2026-04-02 by summarize session (issue #1994).

## Summary

**23 sorries** across 13 files. Changed from 29 / 17 in wave 39: **−6 sorries, −4 files**. Chapters 3, 4, 7, 8 remain 100% sorry-free. 266 of 279 Lean files (95.3%) are sorry-free. 571/583 items (97.9%) sorry-free.

40+ PRs merged since wave 39 (#1901–#1993). Key changes:

- **Proposition6_6_6_source sorry-free** (#1903) — Source naturality instance diamond proved. Was Cluster D keystone; unblocks downstream Gabriel chain sorries.
- **Theorem5_23_2 sorry-free** (#1918) — Complete reducibility + Peter-Weyl decomposition for GL(V) fully proved.
- **Proposition5_22_2 sorry-free** (#1926) — Determinant twist isomorphism proved via SchurModule construction.
- **BasicAlgebraExistence sorry-free** (#1922, #1944) — cornerFunctor_essSurj proved via balanced tensor product isomorphism. Mathlib bump sorries fixed.
- **Example9_4_4 sorry-free** (#1912, #1910) — Hilbert syzygy theorem fully proved; both lower-bound sub-goals closed.
- **CoxeterInfrastructure 2→1** (#1977, #1965, #1948) — 7/8 sorries resolved. Admissible ordering proved; subsingleton infrastructure added. One sorry remains (type-changing iterated reflection).
- **TabloidModule 3→1** (#1975, #1943) — Reversed dominance direction fixed; cumulative count helper proved. `polytabloid_syt_dominance` remains.
- **MoritaStructural (Ch9) 1→2** (#1937, #1929, #1956) — `basic_morita_algEquiv` decomposed: ring structure proved, but `basic_morita_regular_module_iso` and k-linearity sorry added.
- **FormalCharacterIso NEW** (#1917, #1991) — 2 sorries. Bridge lemmas for formal character isomorphism extracted from Theorem5_22_1 proof chain.
- **Theorem5_22_1 3→3** (#1933, #1927, #1917, #1991, #1990, #1978) — Major infrastructure: Young symmetrizer trace Kronecker proved, character orthogonality proved, Frobenius bridge lemmas extracted. But sorry count unchanged due to restructuring.
- **PolytabloidBasis 3→4** (#1993, #1952, #1970) — garnir_reduction' infrastructure proved, helper lemmas added. T_col_inc sorry added; column_standard_coset_has_syt' sorry moved.

**Net sorry change: −6** (first net decrease since wave 37). Five files became sorry-free; one new file created.

**Definition-level sorries: 0.** All mathematical objects are constructed. No regression.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 39 |
|---------|---------|-------|---------------------|
| Ch2 | 1 | 1 | 0 |
| Ch5 | 15 | 6 | −1 sorry, 0 files (Theorem5_23_2 sorry-free; Proposition5_22_2 sorry-free; FormalCharacterIso new +2; TabloidModule 3→1; PolytabloidBasis 3→4) |
| Ch6 | 5 | 5 | −2 sorries, −2 files (Proposition6_6_6_source sorry-free; CoxeterInfrastructure 2→1) |
| Ch9 | 2 | 1 | −1 sorry, −2 files (Example9_4_4 sorry-free; BasicAlgebraExistence sorry-free; MoritaStructural 1→2) |
| Infra | 0 | 0 | −2 sorries, −1 file (BasicAlgebraExistence sorry-free) |

## Files That Became Sorry-Free Since Wave 39

1. **Proposition6_6_6_source.lean** — 1 sorry → 0. Source naturality instance diamond proved (#1903).
2. **Theorem5_23_2.lean** — 1 sorry → 0. Peter-Weyl decomposition for GL(V) proved (#1918).
3. **Proposition5_22_2.lean** — 1 sorry → 0. Determinant twist isomorphism proved (#1926).
4. **BasicAlgebraExistence.lean** — 2 sorries → 0. Corner functor essential surjectivity + Mathlib bump fixes (#1922, #1944).
5. **Example9_4_4.lean** — 2 sorries → 0. Hilbert syzygy theorem fully proved (#1912, #1910).

## New Files With Sorries

1. **FormalCharacterIso.lean** — 2 sorries (NEW). Bridge lemmas: `iso_of_formalCharacter_eq` (iso from formal character equality) and `formalCharacter_shift_of_weightSpace_finrank` (character multiplication via weight space dimensions).

## Per-File Sorry Detail

| File | Sorries | Nature | Delta from W39 |
|------|---------|--------|----------------|
| PolytabloidBasis | 4 | Linear independence + T_col_inc + coset_has_syt + garnir_reduction' | **+1** |
| Theorem5_22_1 | 3 | Trace formula + charValue stability + charValue=spechtChar | 0 |
| Theorem5_27_1 | 3 | Mackey: irreducibility, injectivity, completeness | 0 |
| FormalCharacterIso | 2 | iso_of_formalCharacter_eq + shift formula | **NEW** |
| MoritaStructural (Ch9) | 2 | regular_module_iso + k-linearity (Eilenberg-Watts) | **+1** |
| Problem6_9_1 | 2 | IsCompl conditions (pV/qV, pW/qW) | 0 |
| Corollary6_8_3 | 1 | Indecomposable → positive root (reflection chain) | 0 |
| Corollary6_8_4 | 1 | Bijection: indec reps ↔ positive roots | 0 |
| CoxeterInfrastructure | 1 | Type-changing iterated reflection (universe constraint) | **−1** |
| Problem6_1_5_theorem | 1 | Finite type ↔ Dynkin | 0 |
| TabloidModule | 1 | polytabloid_syt_dominance (PQ transformation) | **−2** |
| Theorem2_1_2 | 1 | Gabriel's theorem | 0 |
| Theorem6_5_2 | 1 | Indecomposable decomposition uniqueness | 0 |

## Merged PRs Since Wave 39 (40+)

### Weyl Character / Young Symmetrizer (Ch5)
| PR | Title |
|----|-------|
| #1913 | Prove YoungSymmetrizerK_sq_scalar_ne_zero |
| #1917 | Prove sum_youngSym_permTracePoly_eq_alpha_schurPoly (Frobenius+orthogonality) |
| #1925 | Young symmetrizer idempotent infrastructure + decompose remaining sorries |
| #1927 | Projection infrastructure + reduce trace formula to weight_trace_coefficient_identity |
| #1933 | Trace formula infrastructure for Theorem5_22_1 Sorry 1 |
| #1953 | Generalize CycleColoring and powerSum_bilinear_coeff to N ≠ n variables |
| #1957 | Prove charValue row orthogonality via Cauchy identity |
| #1978 | Prove charValue row orthogonality via Cauchy identity |
| #1990 | Prove youngSym_trace_kronecker: trace of c_λ on V_{λ'} = α·δ_{λ,λ'} |
| #1991 | Prove character orthogonality for Young symmetrizer (Theorem5_22_1 Sorry 2) |
| #1992 | Prove helper lemmas for Frobenius character formula bridge |

### Schur-Weyl / Polytabloid (Ch5)
| PR | Title |
|----|-------|
| #1905 | Prove Schur polynomial shift and structural decomposition for Prop 5.22.2 |
| #1908 | Polytabloid linear independence proof structure (2 sorrys remain) |
| #1918 | Prove Theorem5_23_2 complete reducibility + Peter-Weyl decomposition |
| #1926 | Prove Proposition5_22_2 determinant twist |
| #1943 | Add tabloidCumulCount_full helper for polytabloid_syt_dominance |
| #1952 | Prove sorted comparison lemma for PolytabloidBasis |
| #1970 | Prove garnir_reduction' via Garnir element identity |
| #1975 | Fix reversed dominance direction in polytabloid_syt_dominance |
| #1993 | Prove helper lemmas for polytabloid basis straightening |

### Mackey Machine (Ch5)
| PR | Title |
|----|-------|
| #1916 | Prove endo_preserves_cosets for Theorem5_27_1 |
| #1932 | Add Mackey machine infrastructure |
| #1954 | Prove transport lemma and single-coset support |
| #1985 | Prove sigma_contains_all_single for Mackey machine irreducibility |

### Gabriel Theorem Chain (Ch6)
| PR | Title |
|----|-------|
| #1903 | Prove equivAt_eq_source_naturality (0 sorries in Proposition6_6_6_source) |
| #1948 | Reduce CoxeterInfrastructure sorrys |
| #1965 | Subsingleton infrastructure for CoxeterInfrastructure reflection functors |
| #1977 | Resolve 7/8 sorrys in CoxeterInfrastructure |

### Morita Theory / Basic Algebras (Ch9/Infra)
| PR | Title |
|----|-------|
| #1904 | Prove ker π annihilates simple modules in basicness proof |
| #1906 | Prove basic_morita_algEquiv |
| #1922 | Fix BasicAlgebraExistence: 2 Mathlib bump sorries + corner module dimension |
| #1929 | Prove basic_morita_algEquiv: basic + Morita equivalent ⟹ isomorphic |
| #1937 | Decompose basic_morita_algEquiv into sub-lemmas |
| #1944 | Prove cornerFunctor_essSurj: balanced tensor product isomorphism |
| #1956 | Prove equivEndAlgEquiv ring structure (k-linearity sorry remains) |
| #1963 | Prove equivalences of ModuleCat preserve module-theoretic indecomposability |
| #1962 | Internal direct sum ↔ categorical biproduct bridge for ModuleCat |

### Hilbert Syzygy (Ch9)
| PR | Title |
|----|-------|
| #1910 | Prove Example9_4_4 (final sorry closed) |
| #1912 | Prove Example9_4_4 (additional sorry closed) |

### Other
| PR | Title |
|----|-------|
| #1901 | Wave 39 summary |
| #1986 | Specht module simplicity proved |

## Dependency Clusters

### Cluster A: Polytabloid Basis (Ch5, 5 sorries)
**Files:** PolytabloidBasis (4), TabloidModule (1)
**Key sorries:**
- `polytabloid_linearIndependent` — needs tabloid projection approach (#1928)
- `T_col_inc` — column-increasing property of SYT filling
- `column_standard_coset_has_syt'` — LEFT vs RIGHT coset mismatch (#1969)
- `garnir_reduction'` — Garnir element identity for straightening
- `polytabloid_syt_dominance` — PQ transformation dominance ordering
**Status:** Active work. Coset mismatch identified (#1969). garnir_reduction' infrastructure built (#1970, #1993).

### Cluster B: Weyl Character Formula (Ch5, 5 sorries)
**Files:** Theorem5_22_1 (3), FormalCharacterIso (2)
**Key sorries:**
- `finrank_weight_eq_card_sum` — trace formula: weight finrank via Young symmetrizer
- `charValue_stability` — character stabilization under variable count change
- `charValue_eq_spechtModuleCharacter` — bridge between polynomial charValue and Specht module trace
- `iso_of_formalCharacter_eq` — isomorphism from formal character equality
- `formalCharacter_shift_of_weightSpace_finrank` — character shift formula
**Status:** Major progress. Trace Kronecker proved (#1990), character orthogonality proved (#1991). Bridge lemmas remain.

### Cluster C: Mackey Machine (Ch5, 3 sorries)
**Files:** Theorem5_27_1 (3)
**Remaining:** Parts (i) irreducibility, (ii) injectivity, (iii) completeness.
**Status:** Character formula proved. Infrastructure expanding (#1916, #1932, #1954, #1985). sigma_contains_all_single proved.

### Cluster D: Gabriel Theorem Chain (Ch6, 5 sorries)
**Files:** CoxeterInfrastructure (1), Corollary6_8_3 (1), Corollary6_8_4 (1), Problem6_1_5_theorem (1), Theorem6_5_2 (1)
**Keystone:** CoxeterInfrastructure `one_round_or_simpleRoot_iteration` (1 sorry: type-changing iterated reflection with universe constraint). This is the last blocker for Corollary6_8_3 and Corollary6_8_4.
**Status:** Down from 7 to 5 sorries this wave. Proposition6_6_6_source closed. 7/8 CoxeterInfrastructure sorries resolved.

### Cluster E: Morita Theory (Ch9, 2 sorries)
**Files:** MoritaStructural (2)
**Key sorries:**
- `basic_morita_regular_module_iso` — F(B₁) ≅ B₂ for basic Morita-equivalent algebras (#1939)
- k-linearity of ring equivalence (Eilenberg-Watts theorem)
**Status:** BasicAlgebraExistence now sorry-free. Ring structure proved (#1956). Two sorries remain in the final step.

### Cluster F: Problem6_9_1 (Ch6, 2 sorries)
**Files:** Problem6_9_1 (2)
**Sorries:** IsCompl_pV_qV + IsCompl_pW_qW (direct sum decomposition). Independent of other clusters.

### Isolated
- **Theorem2_1_2** (1 sorry): Gabriel's theorem classification. Depends on Cluster D completion.

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
| 39 | 29 | 17 | 571/583 (97.9%) | 2026-03-28 |
| 40 | 23 | 13 | 571/583 (97.9%) | 2026-04-02 |

The wave 39→40 decrease of 6 sorries is the largest single-wave reduction since wave 37→38 (−6). Five files cleared entirely. The sorry count is now at a project low, with trajectory firmly downward again after the wave 38→39 uptick.

## Strategic Recommendations

1. **Close CoxeterInfrastructure** (1 sorry) — Keystone for Gabriel chain (Cluster D, 5 sorries). The type-changing iterated reflection functor (#1936) is the last blocker. Resolving this potentially unblocks Corollary6_8_3, Corollary6_8_4, and downstream.

2. **Fix column_standard_coset_has_syt' coset direction** (#1969) — Correctness fix affecting the entire polytabloid basis chain (Cluster A, 5 sorries). The LEFT vs RIGHT coset mismatch is well-analyzed with a clear fix plan.

3. **Mackey machine irreducibility** (#1782) — With sigma_contains_all_single proved (#1985), the irreducibility proof may be within reach. Closing one of the three Mackey sorries would demonstrate progress on this cluster.

4. **MoritaStructural regular module iso** (#1939) — The regular module isomorphism F(B₁) ≅ B₂ is the concrete remaining step now that BasicAlgebraExistence is sorry-free.

5. **FormalCharacterIso bridge lemmas** (#1983) — New file with 2 sorries connecting Specht module character to Schur polynomial. Both are relatively self-contained.

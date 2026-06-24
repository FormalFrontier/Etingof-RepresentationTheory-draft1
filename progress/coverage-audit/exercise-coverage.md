# Exercise / Problem coverage (as-of audit)

- Total exercise/problem items: 102
- With a *name-matched* Lean file: 3 (Chapter6/Problem6.1.1, 6.1.5, 6.9.1)
- All 102 are marked `sorry_free` in items.json. **This status is unreliable for exercises:**
  it is vacuously true wherever no Lean file exists, and real coverage is obscured two ways:
  (1) naming aliases — Problem 2.15.1's sl(2) content lives in `Chapter2/Sl2Irrep.lean`, not a
  `Problem2_15_1`-named file; (2) content folded into adjacent theorems. So 3/102 is a *lower
  bound* on coverage and the blanket `sorry_free` is not evidence of completion.
- Same root cause as the prose-blob gap: exercises were marked done without a coverage audit.

## The sl(2) problem (Problem 2.15.1, parts a-n) — PARTIAL

Covered (sorry-free):
- `Chapter2/Sl2Irrep.lean`: constructs the d-dimensional irrep V_d (E, F, H, the sl(2)-triple
  relations, `irrep_finrank`, `irrep_isIrreducible`). Backbone of parts (a)-(f) existence/irreducibility.
- `Chapter2/Theorem2_1_1.lean`: classification of irreps of U(sl(2)); references the Casimir.

NOT covered (the famous payoffs):
- (g) Casimir eigenvalue lambda(lambda+2)/2 on V_lambda
- (h)-(k) complete reducibility: every fin-dim rep is a direct sum of V_lambda. `Sl2Irrep.lean`'s
  own docstring flags this needs Weyl's complete-reducibility theorem, not in Mathlib.
- (l) Jacobson-Morozov lemma (the "Jacobson" Lean hits are Jacobson *radical*, unrelated)
- (m) Clebsch-Gordan decomposition of V_lambda ⊗ V_mu (ABSENT)
- (n) Jordan-normal-form application
- (f) uniqueness of the d-dimensional irrep

Rough estimate: existence/irreducibility backbone done (~30%); complete reducibility,
Clebsch-Gordan, Jacobson-Morozov open.

## Per-item

- [ ] `Chapter2/Problem2.3.15`
- [ ] `Chapter2/Problem2.3.16`
- [ ] `Chapter2/Problem2.3.17`
- [ ] `Chapter2/Problem2.3.18`
- [ ] `Chapter2/Problem2.4.1`
- [ ] `Chapter2/Problem2.5.1`
- [ ] `Chapter2/Problem2.5.2`
- [ ] `Chapter2/Problem2.7.4`
- [ ] `Chapter2/Problem2.7.5`
- [ ] `Chapter2/Problem2.8.6`
- [ ] `Chapter2/Problem2.8.11`
- [ ] `Chapter2/Exercise2.9.5`
- [ ] `Chapter2/Exercise2.9.11`
- [ ] `Chapter2/Exercise2.11.2`
- [ ] `Chapter2/Problem2.11.3`
- [ ] `Chapter2/Exercise2.11.5`
- [ ] `Chapter2/Problem2.11.6`
- [ ] `Chapter2/Exercise2.11.7`
- [ ] `Chapter2/Problem2.13.1`
- [ ] `Chapter2/Problem2.14.3`
- [ ] `Chapter2/Problem2.15.1`
- [ ] `Chapter2/Problem2.16.1`
- [ ] `Chapter2/Problem2.16.2`
- [ ] `Chapter2/Problem2.16.3`
- [ ] `Chapter2/Problem2.16.4`
- [ ] `Chapter2/Problem2.16.5`
- [ ] `Chapter3/Problem3.3.3`
- [ ] `Chapter3/Exercise3.6.1`
- [ ] `Chapter3/Problem3.8.3`
- [ ] `Chapter3/Problem3.8.4`
- [ ] `Chapter3/Problem3.8.5`
- [ ] `Chapter3/Problem3.9.1`
- [ ] `Chapter3/Problem3.9.2`
- [ ] `Chapter3/Problem3.9.3`
- [ ] `Chapter3/Problem3.9.4`
- [ ] `Chapter3/Problem3.9.5`
- [ ] `Chapter3/Exercise3.10.1`
- [ ] `Chapter4/Problem4.1.4`
- [ ] `Chapter4/Exercise4.2.3`
- [ ] `Chapter4/Exercise4.3.1`
- [ ] `Chapter4/Problem4.5.2`
- [ ] `Chapter4/Problem4.12.1`
- [ ] `Chapter4/Problem4.12.2`
- [ ] `Chapter4/Problem4.12.3`
- [ ] `Chapter4/Problem4.12.4`
- [ ] `Chapter4/Problem4.12.5`
- [ ] `Chapter4/Problem4.12.6`
- [ ] `Chapter4/Problem4.12.7`
- [ ] `Chapter4/Problem4.12.8`
- [ ] `Chapter4/Problem4.12.9`
- [ ] `Chapter4/Problem4.12.10`
- [ ] `Chapter4/Problem4.12.11`
- [ ] `Chapter5/Problem5.1.2`
- [ ] `Chapter5/Exercise5.1.7`
- [ ] `Chapter5/Problem5.2.7`
- [ ] `Chapter5/Exercise5.3.3`
- [ ] `Chapter5/Problem5.8.4`
- [ ] `Chapter5/Exercise5.8.5`
- [ ] `Chapter5/Problem5.10.2`
- [ ] `Chapter5/Discussion_Problem5.10.2_parts`
- [ ] `Chapter5/Problem5.11.1`
- [ ] `Chapter5/Problem5.12.5`
- [ ] `Chapter5/Problem5.16.1`
- [ ] `Chapter5/Problem5.16.2`
- [ ] `Chapter5/Problem5.16.3`
- [ ] `Chapter5/Problem5.24.1`
- [ ] `Chapter5/Problem5.24.2`
- [ ] `Chapter5/Exercise5.27.2`
- [ ] `Chapter5/Exercise5.27.3`
- [x] `Chapter6/Problem6.1.1` -> Problem6_1_1
- [ ] `Chapter6/Problem6.1.2`
- [ ] `Chapter6/Problem6.1.3`
- [ ] `Chapter6/Problem6.1.3_continued_E7_E8`
- [ ] `Chapter6/Problem6.1.3_continued_tildeE`
- [x] `Chapter6/Problem6.1.5` -> Problem6_1_5_PosDef;Problem6_1_5_OrbitSpace;Problem6_1_5_DenseOrbit;Problem6_1_5_OrbitFiniteness;Problem6_1_5_OrbitInjective;Problem6_1_5_theorem;Problem6_1_5_FieldEmbedding;Problem6_1_5_OrbitComorphism;Problem6_1_5_DimBound;Problem6_1_5_TitsBridge;Problem6_1_5_StrictDimBound
- [ ] `Chapter6/Problem6.1.5_parts`
- [ ] `Chapter6/Problem6.1.6`
- [x] `Chapter6/Problem6.9.1` -> Problem6_9_1
- [ ] `Chapter6/Problem6.9.2`
- [ ] `Chapter6/Problem6.9.3`
- [ ] `Chapter7/Problem7.7.3`
- [ ] `Chapter7/Exercise7.8.4`
- [ ] `Chapter7/Problem7.8.5`
- [ ] `Chapter7/Problem7.8.7`
- [ ] `Chapter7/Exercise7.9.7`
- [ ] `Chapter7/Exercise7.9.8`
- [ ] `Chapter8/Problem8.1.3`
- [ ] `Chapter8/Exercise8.1.4`
- [ ] `Chapter8/Exercise8.2.2`
- [ ] `Chapter8/Problem8.2.5`
- [ ] `Chapter8/Problem8.2.6`
- [ ] `Chapter8/Problem8.2.7`
- [ ] `Chapter8/Problem8.2.8`
- [ ] `Chapter8/Exercise8.2.9`
- [ ] `Chapter8/Problem8.2.10`
- [ ] `Chapter9/Problem9.3.2`
- [ ] `Chapter9/Problem9.4.2`
- [ ] `Chapter9/Problem9.4.5`
- [ ] `Chapter9/Problem9.4.6`
- [ ] `Chapter9/Problem9.5.3`
- [ ] `Chapter9/Exercise9.6.3`
- [ ] `Chapter9/Problem9.6.5`

# Formalization Planning Report (Stage 2.5)

Generated retroactively during template reconciliation (2026-03-27). This is a
historical planning snapshot, not a current status report. The mathematical
formalization reached its documented completion gate on 2026-07-29; see
`PROGRESS.md` and `progress/reviews/2026-07-29-project-completion.md`.

## Suggested formalization order

The book was formalized roughly in chapter order, with definitions scaffolded
first and proofs filled in via parallel agent waves. The dependency structure
largely follows chapter order: Chapters 2–4 (basic representation theory) →
Chapter 5 (symmetric groups, Schur–Weyl) → Chapter 6 (quivers) →
Chapters 7–8 (Lie algebras) → Chapter 9 (Hopf algebras/tensor categories).

At the time of this snapshot, Chapters 3, 4, 7, and 8 were fully sorry-free and
the remaining proof work was concentrated in Chapters 5, 6, and 9. Those proof
gaps were subsequently closed.

## Dependency gaps

Most textbook dependencies are internal (earlier results in the book). The main
external gaps encountered during formalization:

- **Schur modules / Schur functors**: Not in Mathlib. Built from scratch in
  `EtingofRepresentationTheory/Chapter5/` (SchurModule, TabloidModule, etc.).
- **Coxeter groups and root systems**: Partial Mathlib coverage. Extended in
  `Chapter6/CoxeterInfrastructure.lean`.
- **Morita equivalence**: Not fully in Mathlib. Infrastructure built in
  `Infrastructure/MoritaStructural.lean`.
- **Power-sum / Cauchy identity machinery**: Built in
  `Chapter5/PowerSumCauchyBilinear.lean`.

## Hardest items at the time of the snapshot

22 files still contain `sorry` (approximately 33 proof obligations):

### Chapter 5 — Symmetric groups and Schur–Weyl (highest priority)
- **Theorem5_18_4**: Schur–Weyl duality centralizer computation
- **Theorem5_22_1**: Formal character / decomposition
- **Theorem5_23_2**: Complete reducibility + Peter–Weyl for GL(V)
- **Theorem5_27_1**: Mackey machine (4 sorrys: irreducibility, injectivity, completeness, character)
- **PolytabloidBasis**: Straightening lemma / linear independence
- **Proposition5_22_2**: Schur polynomial coefficient identity

### Chapter 6 — Quiver representations
- **Theorem6_5_2**, **Corollary6_8_3/4**: Gabriel's theorem consequences
- **Proposition6_6_6**: Source naturality / reflection functors
- **Theorem_Dynkin_classification**: Dynkin diagram classification

### Chapter 9 — Hopf algebras
- **Theorem9_2_1**, **Corollary9_7_3**, **Example9_4_4**: Structural results
- **MoritaStructural**: Infrastructure lemmas

### Infrastructure
- **BasicAlgebraExistence**: Existence of basic algebras
- **Theorem2_1_2**: Density theorem (1 sorry)

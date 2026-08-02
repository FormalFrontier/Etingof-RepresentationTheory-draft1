# References: Character of U_lambda as coefficient of x^lambda in product of power sums

## External Dependencies

- **Symmetric group: permutations, cycle decomposition, conjugacy classes of S_n, sign homomorphism** (undergraduate_prerequisite)
  Mathlib (exact): `Equiv.Perm`, `Equiv.Perm.cycleType`, `Equiv.Perm.sign`
  Symmetric group as `Equiv.Perm (Fin n)`. Cycle decomposition, sign homomorphism, and conjugacy class characterization all present.
- **Combinatorics of partitions and Young diagrams: partitions of integers, Young tableaux, hook lengths, content of a cell** (undergraduate_prerequisite)
  Mathlib (partial): `Nat.Partition`, `YoungDiagram`, `SemistandardYoungTableau`
  `Nat.Partition`, `YoungDiagram`, and `SemistandardYoungTableau` cover partitions, diagrams, and semistandard tableaux. Standard tableaux specialized to a fixed finite alphabet, hook lengths, and cell content still require project definitions.
  External source [natural_language]: Fulton, 'Young Tableaux' — Chapters 1-4
  External source [natural_language]: Sagan, 'The Symmetric Group' — Chapter 2
  External source [lean_library]: Mathlib Nat.Partition and YoungDiagram — partial coverage
- **Symmetric polynomials and power sums: elementary symmetric polynomials, power sum symmetric polynomials, Newton's identities** (undergraduate_prerequisite)
  Mathlib (exact): `MvPolynomial.esymm`, `MvPolynomial.psum`, `MvPolynomial.psum_eq_mul_esymm_sub_sum`
  `MvPolynomial.esymm` and `MvPolynomial.psum` provide the two polynomial families, and `MvPolynomial.psum_eq_mul_esymm_sub_sum` is Newton's recurrence relating them. Schur polynomials themselves are not in Mathlib and remain project-local.
  External source [natural_language]: Macdonald, 'Symmetric Functions and Hall Polynomials' — Chapter I
  External source [natural_language]: Stanley, 'Enumerative Combinatorics Vol. 2' — Chapter 7

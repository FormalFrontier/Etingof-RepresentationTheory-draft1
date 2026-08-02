# References: Classification of irreducible representations of S_n via Specht modules V_lambda

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

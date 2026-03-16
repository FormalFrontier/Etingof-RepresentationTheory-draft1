# References: Definition 6.1.4: Dynkin diagram

## Mathlib Coverage (partial)

- `CoxeterMatrix`

Mathlib has `CoxeterMatrix` and `CoxeterSystem` for Coxeter-Dynkin data. The specific `DynkinDiagram` inductive type may not exist; instead Dynkin types are encoded via their Cartan/Coxeter matrices. Partial coverage — the classification of positive-definite graphs as Dynkin diagrams would need custom work.

## External Sources (definition gap)

- **[natural_language]** Schiffler, 'Quiver Representations' — Chapter 4
  Dynkin diagrams in context of Gabriel's theorem; classification of positive-definite graphs
- **[natural_language]** Humphreys, 'Introduction to Lie Algebras and Representation Theory' — Section 11
  Classification of Dynkin diagrams via Cartan matrices

## External Dependencies

- **Graph theory basics: undirected graphs, connected components, trees, adjacency matrix, positive definite quadratic forms** (undergraduate_prerequisite)
  Mathlib (exact): `SimpleGraph`, `SimpleGraph.Connected`, `SimpleGraph.IsTree`, `SimpleGraph.adjMatrix`, `QuadraticMap.PosDef`
  `SimpleGraph` covers undirected graphs. Connectivity, trees, and adjacency matrices present. Positive definite quadratic forms via `QuadraticMap.PosDef`.
- **Quadratic forms: positive definiteness, Sylvester's criterion, relationship between quadratic forms and symmetric bilinear forms** (undergraduate_prerequisite)
  Mathlib (exact): `QuadraticForm`, `QuadraticMap.PosDef`, `QuadraticForm.associated`
  `QuadraticForm` with `QuadraticMap.PosDef` for positive definiteness. `QuadraticForm.associated` gives the correspondence with bilinear forms. Sylvester's criterion may not be explicitly stated but the positive definiteness framework is complete.

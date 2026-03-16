# References: Theorem: Classification of Dynkin diagrams

## External Dependencies

- **Graph theory basics: undirected graphs, connected components, trees, adjacency matrix, positive definite quadratic forms** (undergraduate_prerequisite)
  Mathlib (exact): `SimpleGraph`, `SimpleGraph.Connected`, `SimpleGraph.IsTree`, `SimpleGraph.adjMatrix`, `QuadraticMap.PosDef`
  `SimpleGraph` covers undirected graphs. Connectivity, trees, and adjacency matrices present. Positive definite quadratic forms via `QuadraticMap.PosDef`.
- **Dynkin diagram classification: the complete list of positive definite Cartan matrices / Dynkin diagrams (A_n, D_n, E_6, E_7, E_8)** (external_result)
  Dynkin diagrams and their classification are NOT in Mathlib. This will need to be formalized from scratch or worked around. The graph theory and quadratic form infrastructure exists but the classification theorem itself is absent.
- **Quadratic forms: positive definiteness, Sylvester's criterion, relationship between quadratic forms and symmetric bilinear forms** (undergraduate_prerequisite)
  Mathlib (exact): `QuadraticForm`, `QuadraticMap.PosDef`, `QuadraticForm.associated`
  `QuadraticForm` with `QuadraticMap.PosDef` for positive definiteness. `QuadraticForm.associated` gives the correspondence with bilinear forms. Sylvester's criterion may not be explicitly stated but the positive definiteness framework is complete.

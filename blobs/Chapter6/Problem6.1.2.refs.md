# References: Problem 6.1.2: Some algebraic geometry

## External Dependencies

- **Graph theory basics: undirected graphs, connected components, trees, adjacency matrix, positive definite quadratic forms** (undergraduate_prerequisite)
  Mathlib (exact): `SimpleGraph`, `SimpleGraph.Connected`, `SimpleGraph.IsTree`, `SimpleGraph.adjMatrix`, `QuadraticMap.PosDef`
  `SimpleGraph` covers undirected graphs. Connectivity, trees, and adjacency matrices present. Positive definite quadratic forms via `QuadraticMap.PosDef`.
- **Quadratic forms: positive definiteness, Sylvester's criterion, relationship between quadratic forms and symmetric bilinear forms** (undergraduate_prerequisite)
  Mathlib (exact): `QuadraticForm`, `QuadraticMap.PosDef`, `QuadraticForm.associated`
  `QuadraticForm` with `QuadraticMap.PosDef` for positive definiteness. `QuadraticForm.associated` gives the correspondence with bilinear forms. Sylvester's criterion may not be explicitly stated but the positive definiteness framework is complete.

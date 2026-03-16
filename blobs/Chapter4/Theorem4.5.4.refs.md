# References: Column orthogonality of characters

## External Dependencies

- **Bilinear forms and inner products: Hermitian inner product on complex vector spaces, orthogonality** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap.BilinForm`, `InnerProductSpace`, `inner`, `Orthogonal`
  Inner products via `InnerProductSpace`. Bilinear forms via `LinearMap.BilinForm`. Complex Hermitian inner product supported via `RCLike` typeclass.
- **Generalized Schur orthogonality relations: orthogonality of matrix coefficients of irreducible representations over compact or finite groups** (folklore)
  Mathlib (missing): `FDRep.character`, `Representation`
  Schur orthogonality relations are NOT proved in Mathlib. The character infrastructure exists (`FDRep.character`) but the orthogonality results (both for matrix coefficients and characters) are absent.

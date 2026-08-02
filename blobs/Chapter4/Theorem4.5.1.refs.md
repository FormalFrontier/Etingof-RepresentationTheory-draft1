# References: Orthogonality of characters: inner product equals dim Hom

## External Dependencies

- **Linear maps and endomorphisms: kernel, image, isomorphism theorems, linear operators on finite-dimensional spaces** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap`, `LinearMap.ker`, `LinearMap.range`, `LinearEquiv`, `Module.End`
  Complete coverage. `Module.End R M` is the endomorphism ring. Isomorphism theorems available. Rank-nullity via `LinearMap.rank_range_add_rank_ker`.
- **Bilinear forms and inner products: Hermitian inner product on complex vector spaces, orthogonality** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap.BilinForm`, `InnerProductSpace`, `inner`, `LinearMap.BilinForm.orthogonal`
  Inner products via `InnerProductSpace`. Bilinear forms via `LinearMap.BilinForm`. Complex Hermitian inner product supported via `RCLike` typeclass.
- **Tensor product of vector spaces: construction, universal property, tensor product of linear maps** (undergraduate_prerequisite)
  Mathlib (exact): `TensorProduct`, `TensorProduct.map`, `TensorProduct.mk`
  Full tensor product support. Universal property via `TensorProduct.lift`. Tensor product of maps via `TensorProduct.map`.
- **Dual vector space V* and natural pairing, dual maps (transpose/adjoint of linear maps)** (undergraduate_prerequisite)
  Mathlib (exact): `Module.Dual`, `Module.evalEquiv`, `LinearMap.dualMap`
  `Module.Dual R M` is `M →ₗ[R] R`. `Module.evalEquiv` gives the canonical isomorphism `M ≃ₗ[R] (M*)* ` for reflexive modules. `LinearMap.dualMap` is the transpose/dual map.
- **Characters of representations are class functions; character of a direct sum is sum of characters; character of a tensor product is product of characters** (folklore)
  Mathlib (partial): `FDRep.character`, `FDRep.char_conj`, `FDRep.char_tensor`
  `FDRep.char_conj` proves the class-function property and `FDRep.char_tensor` proves tensor multiplicativity. A general direct-sum additivity theorem is not packaged in Mathlib, so that remaining clause is supplied in the project.
  External source [natural_language]: Serre, 'Linear Representations of Finite Groups' — Section 2.1
  External source [other_formal]: MathComp (Coq) — character.v, classfun.v
- **Properties of the trace: tr(AB) = tr(BA), trace of identity is dimension, trace is basis-independent** (folklore)
  Mathlib (exact): `Matrix.trace`, `Matrix.trace_mul_comm`
  `Matrix.trace_mul_comm` gives tr(AB) = tr(BA). Trace of identity equals dimension. Basis independence follows from the linear map trace.
- **Generalized Schur orthogonality relations: orthogonality of matrix coefficients of irreducible representations over compact or finite groups** (folklore)
  Mathlib (partial): `FDRep.character`, `FDRep.char_orthonormal`, `FDRep.average_char_eq_finrank_invariants`
  `FDRep.char_orthonormal` proves irreducible-character orthonormality for finite groups, and `FDRep.average_char_eq_finrank_invariants` supplies the averaging identity. General matrix-coefficient orthogonality, especially for compact groups, is not packaged.
- **Averaging (Reynolds) operator for finite group actions: (1/|G|) Σ_g ρ(g) is the projection onto invariants when char k does not divide |G|** (folklore)
  Mathlib (exact): `Representation.averageMap`, `Representation.isProj_averageMap`
  `Representation.averageMap` is the Reynolds operator and `Representation.isProj_averageMap` proves that it is the projection onto invariants under the invertibility hypothesis on the group order.
  External source [natural_language]: Serre, 'Linear Representations of Finite Groups' — Section 1.3

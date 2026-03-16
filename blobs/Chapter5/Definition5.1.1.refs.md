# References: Complex, real, and quaternionic type of irreducible representations

## Mathlib Coverage (gap)

The classification of irreducible representations into complex/real/quaternionic types (based on V ≅ V* and existence of invariant bilinear forms) is not in Mathlib. Needs to be defined from scratch.

## External Sources (definition gap)

- **[natural_language]** Serre, 'Linear Representations of Finite Groups' — Section 13.2
  Classification of irreducible representations into real/complex/quaternionic types via Frobenius-Schur indicator; complete proofs
- **[natural_language]** Fulton & Harris, 'Representation Theory' — Section 3.5
  Real and quaternionic structures on complex representations
- **[other_formal]** MathComp (Coq) — character.v has Frobenius-Schur indicator and real/complex classification
  Complete formalization in Coq; can guide Lean approach to Frobenius-Schur classification

## External Dependencies

- **Bilinear forms and inner products: Hermitian inner product on complex vector spaces, orthogonality** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap.BilinForm`, `InnerProductSpace`, `inner`, `Orthogonal`
  Inner products via `InnerProductSpace`. Bilinear forms via `LinearMap.BilinForm`. Complex Hermitian inner product supported via `RCLike` typeclass.

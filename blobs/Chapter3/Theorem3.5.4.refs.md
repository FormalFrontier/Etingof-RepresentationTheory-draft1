# References: Structure of finite dimensional algebras modulo radical

## External Dependencies

- **Matrix algebra: matrix multiplication, trace, determinant, similarity, matrix units** (undergraduate_prerequisite)
  Mathlib (exact): `Matrix`, `Matrix.mul_apply`, `Matrix.trace`, `Matrix.det`, `Matrix.single`, `Matrix.trace_mul_comm`
  Full matrix algebra. `Matrix.single` provides matrix units. `Matrix.trace_mul_comm` gives tr(AB) = tr(BA).
- **Jordan-Hölder theorem: any two composition series of a finite-length module have the same length and the same composition factors (up to reordering and isomorphism)** (external_result)
  Mathlib (exact): `CompositionSeries`, `JordanHolderLattice`, `JordanHolderModule.instJordanHolderLattice`, `CompositionSeries.jordan_holder`
  `JordanHolderModule.instJordanHolderLattice` instantiates the composition-series framework for submodules, and `CompositionSeries.jordan_holder` proves equivalence of any two series with the same endpoints.
  External source [natural_language]: Lang, 'Algebra' — Chapter III, Section 3
- **Wedderburn-Artin theorem: a semisimple artinian ring is isomorphic to a finite direct product of matrix rings over division rings** (external_result)
  Mathlib (exact): `IsSemisimpleRing`, `IsArtinianRing`, `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`
  `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing` states the Wedderburn-Artin decomposition as a finite product of matrix rings over division rings.
  External source [natural_language]: Lam, 'A First Course in Noncommutative Rings' — Chapter 1
  External source [other_formal]: MathComp (Coq) — mxalgebra.v has some Wedderburn-type decompositions for matrix algebras

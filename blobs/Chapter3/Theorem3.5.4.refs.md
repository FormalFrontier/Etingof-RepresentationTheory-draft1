# References: Structure of finite dimensional algebras modulo radical

## External Dependencies

- **Matrix algebra: matrix multiplication, trace, determinant, similarity, matrix units** (undergraduate_prerequisite)
  Mathlib (exact): `Matrix`, `Matrix.mul`, `Matrix.trace`, `Matrix.det`, `Matrix.StdBasisMatrix`, `Matrix.trace_mul_comm`
  Full matrix algebra. `Matrix.StdBasisMatrix` provides matrix units. `Matrix.trace_mul_comm` gives tr(AB) = tr(BA).
- **Jordan-Hölder theorem: any two composition series of a finite-length module have the same length and the same composition factors (up to reordering and isomorphism)** (external_result)
  Mathlib (partial): `CompositionSeries`, `JordanHolderLattice`
  `CompositionSeries` and `JordanHolderLattice` provide the framework. The Jordan-Hölder theorem is stated in terms of lattices satisfying `JordanHolderLattice`. The connection to module composition series requires showing modules form a `JordanHolderLattice`.
- **Wedderburn-Artin theorem: a semisimple artinian ring is isomorphic to a finite direct product of matrix rings over division rings** (external_result)
  Mathlib (partial): `IsSemisimpleRing`, `IsArtinianRing`
  `IsSemisimpleRing` exists as a typeclass. The full Wedderburn-Artin structure theorem (decomposition into matrix rings over division rings) may not be fully stated as a single theorem. The semisimplicity API provides many consequences.

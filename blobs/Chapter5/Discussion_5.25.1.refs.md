# References: Conjugacy classes in GL_2(F_q): scalar, parabolic, hyperbolic, elliptic

## External Dependencies

- **Fields: definition, algebraically closed fields, field extensions, finite fields, characteristic of a field** (undergraduate_prerequisite)
  Mathlib (exact): `Field`, `IsAlgClosed`, `IntermediateField`, `CharP`, `GaloisField`
  All core field theory is well-covered. `Field`, `IsAlgClosed`, `CharP` are standard typeclasses. Finite fields via `GaloisField` and `FiniteField.card`.
- **Matrix algebra: matrix multiplication, trace, determinant, similarity, matrix units** (undergraduate_prerequisite)
  Mathlib (exact): `Matrix`, `Matrix.mul`, `Matrix.trace`, `Matrix.det`, `Matrix.StdBasisMatrix`, `Matrix.trace_mul_comm`
  Full matrix algebra. `Matrix.StdBasisMatrix` provides matrix units. `Matrix.trace_mul_comm` gives tr(AB) = tr(BA).
- **Eigenvalues and eigenvectors: characteristic polynomial, eigenspaces, diagonalization** (undergraduate_prerequisite)
  Mathlib (exact): `Module.End.HasEigenvalue`, `Module.End.eigenspace`, `Matrix.charpoly`
  Eigenvalues and eigenspaces well-covered. Characteristic polynomial via `Matrix.charpoly`. Diagonalization results available.
- **Polynomial rings k[x]: division algorithm, irreducible polynomials, minimal polynomial of a linear operator** (undergraduate_prerequisite)
  Mathlib (exact): `Polynomial`, `Polynomial.IsRoot`, `Polynomial.divByMonic`, `Irreducible`, `minpoly`
  Complete polynomial ring support. Division algorithm, irreducibility, and minimal polynomial of an element all present.
- **Finite fields: existence and uniqueness of F_q, multiplicative group, quadratic residues, field extensions of finite fields** (undergraduate_prerequisite)
  Mathlib (exact): `GaloisField`, `FiniteField.card`, `legendreSym`
  `GaloisField p n` constructs F_{p^n}. `FiniteField.card` proves the cardinality is a prime power. Quadratic residues via `legendreSym`. Field extensions of finite fields well-supported.

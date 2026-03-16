# References: Schur's lemma for algebraically closed fields

## External Dependencies

- **Fields: definition, algebraically closed fields, field extensions, finite fields, characteristic of a field** (undergraduate_prerequisite)
  Mathlib (exact): `Field`, `IsAlgClosed`, `IntermediateField`, `CharP`, `GaloisField`
  All core field theory is well-covered. `Field`, `IsAlgClosed`, `CharP` are standard typeclasses. Finite fields via `GaloisField` and `FiniteField.card`.
- **Eigenvalues and eigenvectors: characteristic polynomial, eigenspaces, diagonalization** (undergraduate_prerequisite)
  Mathlib (exact): `Module.End.HasEigenvalue`, `Module.End.eigenspace`, `Matrix.charpoly`
  Eigenvalues and eigenspaces well-covered. Characteristic polynomial via `Matrix.charpoly`. Diagonalization results available.
- **Polynomial rings k[x]: division algorithm, irreducible polynomials, minimal polynomial of a linear operator** (undergraduate_prerequisite)
  Mathlib (exact): `Polynomial`, `Polynomial.IsRoot`, `Polynomial.divByMonic`, `Irreducible`, `minpoly`
  Complete polynomial ring support. Division algorithm, irreducibility, and minimal polynomial of an element all present.

# References: Section 5.25.2: 1-dimensional representations heading

## External Dependencies

- **Fields: definition, algebraically closed fields, field extensions, finite fields, characteristic of a field** (undergraduate_prerequisite)
  Mathlib (exact): `Field`, `IsAlgClosed`, `IntermediateField`, `CharP`, `GaloisField`
  All core field theory is well-covered. `Field`, `IsAlgClosed`, `CharP` are standard typeclasses. Finite fields via `GaloisField` and `FiniteField.card`.
- **Finite fields: existence and uniqueness of F_q, multiplicative group, quadratic residues, field extensions of finite fields** (undergraduate_prerequisite)
  Mathlib (exact): `GaloisField`, `FiniteField.card`, `legendreSym`
  `GaloisField p n` constructs F_{p^n}. `FiniteField.card` proves the cardinality is a prime power. Quadratic residues via `legendreSym`. Field extensions of finite fields well-supported.

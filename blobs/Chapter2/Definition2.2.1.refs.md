# References: Associative algebra

## Mathlib Coverage (exact)

- `Algebra`

Mathlib's `Algebra R A` typeclass models an associative R-algebra. Over a field k, `Algebra k A` with `Ring A` gives exactly an associative k-algebra.

## External Dependencies

- **Fields: definition, algebraically closed fields, field extensions, finite fields, characteristic of a field** (undergraduate_prerequisite)
  Mathlib (exact): `Field`, `IsAlgClosed`, `IntermediateField`, `CharP`, `GaloisField`
  All core field theory is well-covered. `Field`, `IsAlgClosed`, `CharP` are standard typeclasses. Finite fields via `GaloisField` and `FiniteField.card`.
- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.
- **Rings and ideals: definition of rings, two-sided ideals, quotient rings, nilpotent ideals, Jacobson radical** (undergraduate_prerequisite)
  Mathlib (exact): `Ring`, `Ideal`, `Ideal.Quotient`, `IsNilpotent`, `Ideal.jacobson`
  Complete ring theory. `IsNilpotent` for elements; nilpotent ideals expressible as `∀ x ∈ I, IsNilpotent x` or via `I ^ n = ⊥`. Jacobson radical via `Ideal.jacobson`.

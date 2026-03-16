# References: Homomorphism (intertwining operator) of representations

## Mathlib Coverage (exact)

- `LinearMap`
- `Module.End`

`LinearMap` (notation `M →ₗ[R] N`) is an R-module homomorphism. For group representations, `Representation.linHom` and related constructions exist.

## External Dependencies

- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.

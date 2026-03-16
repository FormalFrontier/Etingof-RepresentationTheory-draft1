# References: Semisimple (completely reducible) representation

## Mathlib Coverage (exact)

- `IsSemisimpleModule`

`IsSemisimpleModule R M` asserts that every submodule has a complement, i.e., M is completely reducible.

## External Dependencies

- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.

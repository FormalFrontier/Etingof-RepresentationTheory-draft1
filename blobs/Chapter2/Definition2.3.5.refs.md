# References: Irreducible (simple) representation

## Mathlib Coverage (exact)

- `IsSimpleModule`

`IsSimpleModule R M` asserts that the module M has exactly two submodules (⊥ and ⊤), i.e., is irreducible/simple.

## External Dependencies

- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.

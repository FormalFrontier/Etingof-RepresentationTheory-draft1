# References: Representation of an algebra (left A-module)

## Mathlib Coverage (exact)

- `Module`

A left A-module is `Module A V`. For representation-theoretic context, `Representation k G V` exists for group representations. For algebra representations, `Module A V` is the standard approach.

## External Dependencies

- **Fields: definition, algebraically closed fields, field extensions, finite fields, characteristic of a field** (undergraduate_prerequisite)
  Mathlib (exact): `Field`, `IsAlgClosed`, `IntermediateField`, `CharP`, `GaloisField`
  All core field theory is well-covered. `Field`, `IsAlgClosed`, `CharP` are standard typeclasses. Finite fields via `GaloisField` and `FiniteField.card`.
- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.
- **Linear maps and endomorphisms: kernel, image, isomorphism theorems, linear operators on finite-dimensional spaces** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap`, `LinearMap.ker`, `LinearMap.range`, `LinearEquiv`, `Module.End`
  Complete coverage. `Module.End R M` is the endomorphism ring. Isomorphism theorems available. Rank-nullity via `LinearMap.rank_range_add_rank_ker`.
- **Modules over rings: left modules, right modules, submodules, quotient modules, free modules, simple modules** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `Submodule`, `Submodule.Quotient`, `Module.Free`, `IsSimpleModule`
  Full module theory. Mathlib uses left modules by convention. `IsSimpleModule` for simple modules. Free modules via `Module.Free`.

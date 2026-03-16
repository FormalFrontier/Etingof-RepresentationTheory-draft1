# References: Overview of representation theory: associative algebras, representations, subrepresentations, direct sums

## External Dependencies

- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.
- **Linear maps and endomorphisms: kernel, image, isomorphism theorems, linear operators on finite-dimensional spaces** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap`, `LinearMap.ker`, `LinearMap.range`, `LinearEquiv`, `Module.End`
  Complete coverage. `Module.End R M` is the endomorphism ring. Isomorphism theorems available. Rank-nullity via `LinearMap.rank_range_add_rank_ker`.
- **Modules over rings: left modules, right modules, submodules, quotient modules, free modules, simple modules** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `Submodule`, `Submodule.Quotient`, `Module.Free`, `IsSimpleModule`
  Full module theory. Mathlib uses left modules by convention. `IsSimpleModule` for simple modules. Free modules via `Module.Free`.

# References: Direct sum of representations

## Mathlib Coverage (exact)

- `DirectSum`
- `Module.directSum`

`DirectSum ι M` gives the direct sum of a family of modules. Binary direct sum via `M × N` with product module structure.

## External Dependencies

- **Linear maps and endomorphisms: kernel, image, isomorphism theorems, linear operators on finite-dimensional spaces** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap`, `LinearMap.ker`, `LinearMap.range`, `LinearEquiv`, `Module.End`
  Complete coverage. `Module.End R M` is the endomorphism ring. Isomorphism theorems available. Rank-nullity via `LinearMap.rank_range_add_rank_ker`.

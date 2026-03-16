# References: The density theorem

## External Dependencies

- **Linear maps and endomorphisms: kernel, image, isomorphism theorems, linear operators on finite-dimensional spaces** (undergraduate_prerequisite)
  Mathlib (exact): `LinearMap`, `LinearMap.ker`, `LinearMap.range`, `LinearEquiv`, `Module.End`
  Complete coverage. `Module.End R M` is the endomorphism ring. Isomorphism theorems available. Rank-nullity via `LinearMap.rank_range_add_rank_ker`.
- **Dimension counting arguments: if V = W ⊕ W' as vector spaces then dim V = dim W + dim W'; rank-nullity theorem** (folklore)
  Mathlib (exact): `LinearMap.rank_range_add_rank_ker`, `Submodule.finrank_sup_add_finrank_inf_eq`, `Module.finrank`
  Rank-nullity via `LinearMap.rank_range_add_rank_ker`. Dimension of direct sums available. `Module.finrank` for finite-dimensional spaces.

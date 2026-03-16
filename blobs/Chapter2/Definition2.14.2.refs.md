# References: Dual representation of a Lie algebra

## Mathlib Coverage (exact)

- `Module.Dual`
- `LieModule`

The dual of a Lie module uses `Module.Dual R M` with the contragredient Lie action. Mathlib has `LieModule.dualLieModule` or equivalent constructions.

## External Dependencies

- **Dual vector space V* and natural pairing, dual maps (transpose/adjoint of linear maps)** (undergraduate_prerequisite)
  Mathlib (exact): `Module.Dual`, `Module.evalEquiv`, `LinearMap.dualMap`
  `Module.Dual R M` is `M →ₗ[R] R`. `Module.evalEquiv` gives the canonical isomorphism `M ≃ₗ[R] (M*)* ` for reflexive modules. `LinearMap.dualMap` is the transpose/dual map.

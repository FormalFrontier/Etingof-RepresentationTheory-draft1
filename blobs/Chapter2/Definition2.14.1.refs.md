# References: Tensor product of Lie algebra representations

## Mathlib Coverage (exact)

- `TensorProduct`
- `LieModule`

Mathlib has both `TensorProduct` and `LieModule`. The Lie module structure on tensor products (via the Leibniz rule) may exist under `Mathlib.Algebra.Lie.TensorProduct` or similar. Exact instance name needs verification.

## External Dependencies

- **Dual vector space V* and natural pairing, dual maps (transpose/adjoint of linear maps)** (undergraduate_prerequisite)
  Mathlib (exact): `Module.Dual`, `Module.evalEquiv`, `LinearMap.dualMap`
  `Module.Dual R M` is `M →ₗ[R] R`. `Module.evalEquiv` gives the canonical isomorphism `M ≃ₗ[R] (M*)* ` for reflexive modules. `LinearMap.dualMap` is the transpose/dual map.

# References: Frobenius character formula for Specht modules V_lambda

## External Dependencies

- **Symmetric group: permutations, cycle decomposition, conjugacy classes of S_n, sign homomorphism** (undergraduate_prerequisite)
  Mathlib (exact): `Equiv.Perm`, `Equiv.Perm.cycleType`, `Equiv.Perm.sign`
  Symmetric group as `Equiv.Perm (Fin n)`. Cycle decomposition, sign homomorphism, and conjugacy class characterization all present.
- **Complex analysis basics: roots of unity, absolute values of complex numbers, triangle inequality for sums of roots of unity** (undergraduate_prerequisite)
  Mathlib (exact): `IsPrimitiveRoot`, `rootsOfUnity`, `Complex.normSq`, `Complex.instNorm`
  Roots of unity via `IsPrimitiveRoot` and `rootsOfUnity`. Complex absolute value via the norm instance `Complex.instNorm` (using `‖z‖`). Triangle inequality available through the normed field instance.
- **Vandermonde determinant formula: det(x_i^{N-j}) = product_{i<j}(x_i - x_j)** (folklore)
  Mathlib (exact): `Matrix.vandermonde`, `Matrix.det_vandermonde`
  `Matrix.det_vandermonde` gives the exact formula: `det(vandermonde v) = ∏ i, ∏ j ∈ Finset.Ioi i, (v j - v i)`.

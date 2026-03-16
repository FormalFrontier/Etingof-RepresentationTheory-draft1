# References: Start of proof of Theorem 5.15.1 (Frobenius character formula)

## External Dependencies

- **Vandermonde determinant formula: det(x_i^{N-j}) = product_{i<j}(x_i - x_j)** (folklore)
  Mathlib (exact): `Matrix.vandermonde`, `Matrix.det_vandermonde`
  `Matrix.det_vandermonde` gives the exact formula: `det(vandermonde v) = ∏ i, ∏ j ∈ Finset.Ioi i, (v j - v i)`.

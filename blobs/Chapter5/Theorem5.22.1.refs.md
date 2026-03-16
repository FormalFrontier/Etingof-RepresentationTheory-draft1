# References: Weyl character formula: character of L_lambda is the Schur polynomial

## External Dependencies

- **Vandermonde determinant formula: det(x_i^{N-j}) = product_{i<j}(x_i - x_j)** (folklore)
  Mathlib (exact): `Matrix.vandermonde`, `Matrix.det_vandermonde`
  `Matrix.det_vandermonde` gives the exact formula: `det(vandermonde v) = ∏ i, ∏ j ∈ Finset.Ioi i, (v j - v i)`.
- **Schur-Weyl duality: the commuting actions of GL(V) and S_n on V^{⊗n} give a double centralizer relationship** (external_result)
  Schur-Weyl duality is NOT in Mathlib. The ingredients (representations, symmetric group, tensor products) exist, but the double centralizer theorem and Schur-Weyl duality are absent.

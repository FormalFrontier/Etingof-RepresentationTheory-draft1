# References: Character expansion in terms of Schur polynomials

## External Dependencies

- **Symmetric polynomials and power sums: elementary symmetric polynomials, power sum symmetric polynomials, Newton's identities** (undergraduate_prerequisite)
  Mathlib (exact): `MvPolynomial.esymm`, `MvPolynomial.psum`, `MvPolynomial.psum_eq_mul_esymm_sub_sum`
  `MvPolynomial.esymm` and `MvPolynomial.psum` provide the two polynomial families, and `MvPolynomial.psum_eq_mul_esymm_sub_sum` is Newton's recurrence relating them. Schur polynomials themselves are not in Mathlib and remain project-local.
  External source [natural_language]: Macdonald, 'Symmetric Functions and Hall Polynomials' — Chapter I
  External source [natural_language]: Stanley, 'Enumerative Combinatorics Vol. 2' — Chapter 7
- **Schur-Weyl duality: the commuting actions of GL(V) and S_n on V^{⊗n} give a double centralizer relationship** (external_result)
  Schur-Weyl duality is NOT in Mathlib. The ingredients (representations, symmetric group, tensor products) exist, but the double centralizer theorem and Schur-Weyl duality are absent.

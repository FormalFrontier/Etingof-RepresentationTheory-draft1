import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# The Schur polynomial shift identity `S_{λ+(1,…,1)} = (∏ Xᵢ) · S_λ`

The Schur-polynomial (alternant) identity underlying the determinant shift.

Adding `1` to every part of a partition multiplies the Schur polynomial by the
monomial `x₁ ⋯ x_N`. This is the alternant row-scaling identity: incrementing all
exponents multiplies row `i` of the alternant matrix by `Xᵢ`, hence the
determinant by `∏ᵢ Xᵢ`.
-/

noncomputable section

namespace Etingof

open MvPolynomial

/-! ### Schur polynomial shift identity

The Schur polynomial for the shifted partition `λ + (1,…,1)` equals
`(∏ Xᵢ) · S_λ`. This follows from the alternant determinant row-scaling
identity: multiplying each row i by `Xᵢ` shifts all exponents by 1. -/

/-- The shifted exponents for `λ + (1,…,1)` equal the original shifted exponents plus 1. -/
private lemma shiftedExps_shift (N : ℕ) (lam : Fin N → ℕ) :
    shiftedExps N (fun i => lam i + 1) = fun j => shiftedExps N lam j + 1 := by
  ext j; simp [shiftedExps]; omega

/-- The alternant matrix with all exponents incremented by 1 equals the diagonal matrix
`diag(X₀, …, X_{N-1})` times the original alternant matrix. -/
private lemma alternantMatrix_shift (N : ℕ) (e : Fin N → ℕ) :
    alternantMatrix N (fun j => e j + 1) =
      Matrix.diagonal (fun i => MvPolynomial.X i) * alternantMatrix N e := by
  ext i j
  simp [alternantMatrix, Matrix.of_apply, Matrix.diagonal_mul, pow_succ, mul_comm]

/-- Row-scaling identity: incrementing all exponents multiplies the alternant
determinant by `∏ Xᵢ`. -/
private lemma alternant_det_shift (N : ℕ) (e : Fin N → ℕ) :
    (alternantMatrix N (fun j => e j + 1)).det =
      (∏ i : Fin N, MvPolynomial.X i) * (alternantMatrix N e).det := by
  rw [alternantMatrix_shift, Matrix.det_mul, Matrix.det_diagonal]

/-- **Schur polynomial shift**: `S_{λ+(1,…,1)} = (∏ Xᵢ) · S_λ`.
Adding 1 to every part of the partition multiplies the Schur polynomial
by the monomial `x₁ · x₂ · ⋯ · x_N`. -/
theorem schurPoly_shift (N : ℕ) (lam : Fin N → ℕ) :
    schurPoly N (fun i => lam i + 1) =
      (∏ i : Fin N, MvPolynomial.X i) * schurPoly N lam := by
  have hΔ := alternantMatrix_vandermondeExps_det_ne_zero N
  apply mul_right_cancel₀ hΔ
  rw [mul_assoc, schurPoly_mul_vandermonde, schurPoly_mul_vandermonde,
      ← alternant_det_shift, shiftedExps_shift]

end Etingof

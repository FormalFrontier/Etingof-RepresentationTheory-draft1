/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.GeneralLinearGroup.WeightCharacter

set_option linter.style.header false

noncomputable section

namespace RepresentationTheory.MvPolynomial.UniformIndexShift

open MvPolynomial

private lemma addStaircase_shift (N : ℕ) (lam : Fin N → ℕ) :
    RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N (fun i => lam i + 1) =
      fun j => RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j + 1 := by
  ext j; simp [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]; omega

private lemma alternantMatrix_shift (N : ℕ) (e : Fin N → ℕ) :
    RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (fun j => e j + 1) =
      Matrix.diagonal (fun i => MvPolynomial.X i) *
        RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e := by
  ext i j
  simp [RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.of_apply,
    Matrix.diagonal_mul, pow_succ, mul_comm]

private lemma alternant_det_shift (N : ℕ) (e : Fin N → ℕ) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N
      (fun j => e j + 1)).det =
      (∏ i : Fin N, MvPolynomial.X i) *
        (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e).det := by
  rw [alternantMatrix_shift, Matrix.det_mul, Matrix.det_diagonal]

/-- Auxiliary equality relating the value at the function obtained by adding one to each index
with the product of all variables times the original value. -/
theorem auxiliary_eq_prod_variables_mul (N : ℕ) (lam : Fin N → ℕ) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N
        (fun i => lam i + 1) =
      (∏ i : Fin N, MvPolynomial.X i) *
        RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam := by
  have hΔ := RepresentationTheory.GeneralLinearGroup.WeightCharacter.Auxiliary.det_ne_zero N
  apply mul_right_cancel₀ hΔ
  rw [mul_assoc,
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase,
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase,
    ← alternant_det_shift, addStaircase_shift]

end RepresentationTheory.MvPolynomial.UniformIndexShift

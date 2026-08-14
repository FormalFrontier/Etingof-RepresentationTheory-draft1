/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

set_option linter.style.longLine false

namespace RepresentationTheory.Auxiliary.AuxiliaryPolynomialSubrepresentation

open MvPolynomial

variable {k : Type*} [Field k] {N : ℕ}

/-- Substituting a matrix into the variables of the auxiliary polynomial scales that polynomial by the constant determinant of the matrix. -/
theorem matrix_substitution_auxiliary_polynomial (M : Matrix (Fin N) (Fin N) k) :
    RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.mvPolynomialRightMul M (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N) = MvPolynomial.C M.det * RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N :=
  RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.mvPolynomialRightMul_apply_det M

/-- A linear endomorphism of the matrix-entry polynomial ring associated with the auxiliary polynomial. -/
noncomputable def mul_auxiliary_polynomial_linearMap (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  LinearMap.mulLeft k (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N)

/-- The auxiliary linear endomorphism sends a polynomial to the auxiliary matrix polynomial multiplied by that polynomial. -/
@[simp] theorem mul_auxiliary_polynomial_linearMap_apply (Q : MvPolynomial (Fin N × Fin N) k) :
    mul_auxiliary_polynomial_linearMap k N Q = RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N * Q :=
  rfl

/-- Multiplication by the auxiliary polynomial intertwines the two displayed general linear group actions. -/
theorem mul_auxiliary_polynomial_linearMap_equivariant (g : Matrix.GeneralLinearGroup (Fin N) k)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    mul_auxiliary_polynomial_linearMap k N (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N) (RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N) g Q)
      = RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g (mul_auxiliary_polynomial_linearMap k N Q) := by
  have happ : ∀ f, RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g f = RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.mvPolynomialRightMul (↑g) f := fun _ => rfl
  have hdet : ((RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N g : kˣ) : k) = (↑g : Matrix (Fin N) (Fin N) k).det := by
    rw [RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits]; exact Matrix.GeneralLinearGroup.val_det_apply g
  simp only [mul_auxiliary_polynomial_linearMap_apply, RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply]
  rw [happ (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N * Q), map_mul, matrix_substitution_auxiliary_polynomial, ← happ Q, hdet,
    MvPolynomial.smul_eq_C_mul]
  ring

/-- Multiplication by the auxiliary matrix polynomial is injective on the matrix-entry polynomial ring. -/
theorem mul_auxiliary_polynomial_linearMap_injective : Function.Injective (mul_auxiliary_polynomial_linearMap k N) := by
  intro a b h
  exact mul_right_injective₀ RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial_ne_zero (by simpa only [mul_auxiliary_polynomial_linearMap_apply] using h)

/-- The range of multiplication by the auxiliary matrix polynomial is the displayed polynomial submodule. -/
theorem range_mul_auxiliary_polynomial_linearMap : LinearMap.range (mul_auxiliary_polynomial_linearMap k N) = RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.matrixIndexedPolynomialSubmodule k N := by
  ext x
  simp only [LinearMap.mem_range, mul_auxiliary_polynomial_linearMap_apply, RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.matrixIndexedPolynomialSubmodule, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨Q, rfl⟩; exact dvd_mul_right _ _
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩

/-- A subrepresentation of the displayed representation on matrix-entry polynomials. -/
noncomputable def auxiliary_polynomial_subrepresentation (k : Type*) [Field k] (N : ℕ) :
    Subrepresentation (RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N) where
  toSubmodule := RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.matrixIndexedPolynomialSubmodule k N
  apply_mem_toSubmodule g _ hf := RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.matrixIndexedPolynomialSubmodule_stable g hf

/-- The underlying submodule of the auxiliary polynomial subrepresentation is the displayed polynomial submodule. -/
@[simp] theorem auxiliary_polynomial_subrepresentation_toSubmodule :
    (auxiliary_polynomial_subrepresentation k N).toSubmodule = RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.matrixIndexedPolynomialSubmodule k N :=
  rfl

/-- The matrix-entry polynomial ring is linearly equivalent to the subtype of the displayed submodule. -/
noncomputable def polynomial_equiv_auxiliary_submodule (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) k ≃ₗ[k] ↥(RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.matrixIndexedPolynomialSubmodule k N) :=
  (LinearEquiv.ofInjective (mul_auxiliary_polynomial_linearMap k N) mul_auxiliary_polynomial_linearMap_injective).trans
    (LinearEquiv.ofEq _ _ range_mul_auxiliary_polynomial_linearMap)

/-- The underlying polynomial of the submodule equivalence is the auxiliary matrix polynomial multiplied by the input polynomial. -/
@[simp] theorem coe_polynomial_equiv_auxiliary_submodule (Q : MvPolynomial (Fin N × Fin N) k) :
    (polynomial_equiv_auxiliary_submodule k N Q : MvPolynomial (Fin N × Fin N) k) = RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k N * Q := by
  simp only [polynomial_equiv_auxiliary_submodule, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply, mul_auxiliary_polynomial_linearMap_apply]

/-- The polynomial equivalence with the auxiliary submodule intertwines the displayed general linear group representations. -/
theorem polynomial_equiv_auxiliary_submodule_equivariant (g : Matrix.GeneralLinearGroup (Fin N) k)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    polynomial_equiv_auxiliary_submodule k N (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N) (RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N) g Q)
      = (auxiliary_polynomial_subrepresentation k N).toRepresentation g (polynomial_equiv_auxiliary_submodule k N Q) := by
  apply Subtype.ext
  change (polynomial_equiv_auxiliary_submodule k N (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N) (RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N) g Q)
        : MvPolynomial (Fin N × Fin N) k)
      = RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix.generalLinearGroupMvPolynomialRightMul k N g (polynomial_equiv_auxiliary_submodule k N Q)
  rw [coe_polynomial_equiv_auxiliary_submodule, coe_polynomial_equiv_auxiliary_submodule, ← mul_auxiliary_polynomial_linearMap_apply, ← mul_auxiliary_polynomial_linearMap_apply,
    mul_auxiliary_polynomial_linearMap_equivariant]

end RepresentationTheory.Auxiliary.AuxiliaryPolynomialSubrepresentation

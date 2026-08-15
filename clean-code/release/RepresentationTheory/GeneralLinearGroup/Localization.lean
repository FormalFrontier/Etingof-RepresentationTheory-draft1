/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction
import RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
import RepresentationTheory.MatrixPolynomialHomogeneity

noncomputable section

namespace RepresentationTheory.GeneralLinearGroup.Localization

open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
  RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
  RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction
  RepresentationTheory.MatrixPolynomialHomogeneity

variable {k : Type*} [Field k] {N : ℕ}

/-- Substitution induced by a square matrix does not increase total degree. -/
theorem totalDegree_substitute_le (M : Matrix (Fin N) (Fin N) k)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    (mvPolynomialRightMul M Q).totalDegree ≤ Q.totalDegree := by
  conv_lhs => rw [← Q.sum_homogeneousComponent]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  exact (matrixMap_preserves_isHomogeneous M
    (MvPolynomial.homogeneousComponent_isHomogeneous i Q)).totalDegree_le.trans hi

/-- The action of an invertible matrix on the distinguished inverse is scalar multiplication by
the inverse determinant. -/
theorem invSelf_action (g : Matrix.GeneralLinearGroup (Fin N) k) :
    generalLinearGroupLocalizationMap g
        (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)) =
      ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ •
        IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) :=
  generalLinearGroupLocalizationRepresentation_apply_invSelf g

/-- Describes the matrix action on a polynomial times a power of the distinguished inverse. -/
theorem action_map_mul_invSelf_pow (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    generalLinearGroupLocalizationRepresentation k N g
        (algebraMap _ _ Q *
          IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r) =
      ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
        (algebraMap _ _ (generalLinearGroupMvPolynomialRightMul k N g Q) *
          IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r) := by
  rw [generalLinearGroupLocalizationRepresentation_apply_eq_map, map_mul,
    generalLinearGroupLocalizationMap_algebraMap_apply, map_pow, invSelf_action,
    smul_pow, mul_smul_comm, ← generalLinearGroupMvPolynomialRightMul_apply]

/-- The linear map sending a polynomial to its image multiplied by a chosen power of the
distinguished inverse. -/
def localizationDenominatorPower (r : ℕ) :
    MvPolynomial (Fin N × Fin N) k →ₗ[k]
      Localization.Away (auxiliary_matrix_polynomial k N) :=
  (LinearMap.mulRight k
    (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r)).comp
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N))).toLinearMap

/-- Evaluating the denominator-power linear map gives the polynomial image times the specified
inverse power. -/
@[simp] theorem localizationDenominatorPower_apply
    (r : ℕ) (p : MvPolynomial (Fin N × Fin N) k) :
    localizationDenominatorPower r p =
      algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) p *
        IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r :=
  rfl

/-- The submodule of the localization associated to a chosen element. -/
def Auxiliary (φ : Localization.Away (auxiliary_matrix_polynomial k N)) :
    Submodule k (Localization.Away (auxiliary_matrix_polynomial k N)) :=
  Submodule.span k
    (Set.range (fun g : Matrix.GeneralLinearGroup (Fin N) k =>
      generalLinearGroupLocalizationRepresentation k N g φ))

/-- The chosen localization element belongs to its associated submodule. -/
theorem Auxiliary.self_mem (φ : Localization.Away (auxiliary_matrix_polynomial k N)) :
    φ ∈ Auxiliary φ := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- Membership in the submodule associated to an element is preserved by the matrix action. -/
theorem auxiliary_action_mem (φ : Localization.Away (auxiliary_matrix_polynomial k N))
    (h : Matrix.GeneralLinearGroup (Fin N) k)
    {x : Localization.Away (auxiliary_matrix_polynomial k N)}
    (hx : x ∈ Auxiliary φ) :
    generalLinearGroupLocalizationRepresentation k N h x ∈ Auxiliary φ := by
  have hmap :
      Submodule.map (generalLinearGroupLocalizationRepresentation k N h) (Auxiliary φ) ≤
        Auxiliary φ := by
    simp only [Auxiliary, Submodule.map_span]
    apply Submodule.span_le.2
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨h * g, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
  exact hmap ⟨x, hx, rfl⟩

/-- The subrepresentation associated to a chosen element of the localization. -/
def Auxiliary.subrepresentation
    (φ : Localization.Away (auxiliary_matrix_polynomial k N)) :
    Subrepresentation (generalLinearGroupLocalizationRepresentation k N) where
  toSubmodule := Auxiliary φ
  apply_mem_toSubmodule g _ hv := auxiliary_action_mem φ g hv

/-- The submodule associated to an element is finite dimensional over the base field. -/
theorem Auxiliary.finiteDimensional
    (φ : Localization.Away (auxiliary_matrix_polynomial k N)) :
    FiniteDimensional k (Auxiliary φ) := by
  obtain ⟨r, Q, hQ⟩ := exists_localization_presentation φ
  set S := MvPolynomial.restrictTotalDegree (Fin N × Fin N) k Q.totalDegree with hS
  set F : S →ₗ[k] Localization.Away (auxiliary_matrix_polynomial k N) :=
    (localizationDenominatorPower r).comp S.subtype with hF
  have hfd : FiniteDimensional k (LinearMap.range F) := inferInstance
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range F) ?_
  rw [Auxiliary]
  apply Submodule.span_le.2
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_range]
  refine ⟨⟨((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
    generalLinearGroupMvPolynomialRightMul k N g Q, ?_⟩, ?_⟩
  · apply Submodule.smul_mem
    rw [hS, MvPolynomial.mem_restrictTotalDegree,
      generalLinearGroupMvPolynomialRightMul_apply]
    exact totalDegree_substitute_le _ _
  · rw [hF, LinearMap.comp_apply]
    change localizationDenominatorPower r
        (((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
          generalLinearGroupMvPolynomialRightMul k N g Q) =
      generalLinearGroupLocalizationRepresentation k N g φ
    rw [map_smul, localizationDenominatorPower_apply, hQ, action_map_mul_invSelf_pow]

end RepresentationTheory.GeneralLinearGroup.Localization

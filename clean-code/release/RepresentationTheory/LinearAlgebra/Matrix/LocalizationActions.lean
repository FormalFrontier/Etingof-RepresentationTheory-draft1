/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Matrix.MvPolynomialAction
import RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction

/-!
# Actions on a matrix-coordinate localization

This module extends a matrix-parameterized polynomial transformation to the localization at the
matrix determinant, packages the resulting endomorphisms as representations, and describes their
interaction with evaluation.
-/

open scoped Matrix

namespace RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions

open MvPolynomial
open RepresentationTheory.Matrix.MvPolynomialAction.Matrix
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
open RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction

variable {k : Type*} [Field k] {N : ℕ}

/-- Builds a representation of a direct-product monoid from two pointwise commuting
representations. -/
noncomputable def Representation.ofCommuting
    {k G H V : Type*} [CommSemiring k] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module k V]
    (ρ : _root_.Representation k G V) (σ : _root_.Representation k H V)
    (hcomm : ∀ (g : G) (h : H), ρ g * σ h = σ h * ρ g) :
    _root_.Representation k (G × H) V where
  toFun gh := ρ gh.1 * σ gh.2
  map_one' := by simp
  map_mul' x y := by
    change ρ (x * y).1 * σ (x * y).2 = (ρ x.1 * σ x.2) * (ρ y.1 * σ y.2)
    rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul,
      mul_assoc (ρ x.1) (ρ y.1), ← mul_assoc (ρ y.1) (σ x.2) (σ y.2),
      hcomm y.1 x.2, mul_assoc (σ x.2) (ρ y.1) (σ y.2),
      ← mul_assoc (ρ x.1) (σ x.2)]

/-- The direct-product representation acts by applying the second representation and then the
first. -/
@[simp] theorem Representation.ofCommuting_apply
    {k G H V : Type*} [CommSemiring k] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module k V]
    (ρ : _root_.Representation k G V) (σ : _root_.Representation k H V)
    (hcomm : ∀ (g : G) (h : H), ρ g * σ h = σ h * ρ g)
    (g : G) (h : H) (v : V) :
    Representation.ofCommuting ρ σ hcomm (g, h) v = ρ g (σ h v) :=
  rfl

/-- An algebra homomorphism from a multivariable polynomial algebra to a localization,
parametrized by a matrix. -/
noncomputable def matrixPolynomialMapToLocalization (M : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k]
      Localization.Away (auxiliary_matrix_polynomial k N) :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (auxiliary_matrix_polynomial k N))).comp
    (transposeMulMvPolynomialAlgHom M)

/-- The homomorphism sends a polynomial to the canonical localization image of its image under the
matrix-parameterized polynomial map. -/
@[simp] theorem matrixPolynomialMapToLocalization_apply
    (M : Matrix (Fin N) (Fin N) k) (a : MvPolynomial (Fin N × Fin N) k) :
    matrixPolynomialMapToLocalization M a =
      algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
        (transposeMulMvPolynomialAlgHom M a) :=
  rfl

/-- The matrix polynomial map sends the localized polynomial to its determinant scalar
multiple. -/
theorem matrixPolynomialMap_localizationPolynomial (M : Matrix (Fin N) (Fin N) k) :
    transposeMulMvPolynomialAlgHom M (auxiliary_matrix_polynomial k N) =
      MvPolynomial.C M.det * auxiliary_matrix_polynomial k N := by
  simpa only [auxiliary_matrix_polynomial] using
    transposeMulMvPolynomialAlgHom_det_mvPolynomialX M

/-- For an invertible matrix, the associated algebra homomorphism sends every element of the
indicated powers submonoid to a unit. -/
theorem matrixPolynomialMapToLocalization_isUnit_of_mem_powers
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (y : Submonoid.powers (auxiliary_matrix_polynomial k N)) :
    IsUnit (matrixPolynomialMapToLocalization (g : Matrix (Fin N) (Fin N) k)
      (y : MvPolynomial (Fin N × Fin N) k)) := by
  obtain ⟨n, hn⟩ := y.2
  rw [← hn]
  change IsUnit (matrixPolynomialMapToLocalization (g : Matrix (Fin N) (Fin N) k)
    (auxiliary_matrix_polynomial k N ^ n))
  rw [matrixPolynomialMapToLocalization_apply, map_pow, map_pow]
  refine IsUnit.pow n ?_
  rw [matrixPolynomialMap_localizationPolynomial, map_mul]
  refine IsUnit.mul ?_ ?_
  · have hdet : IsUnit ((g : Matrix (Fin N) (Fin N) k).det) :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
    exact (hdet.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)).map
      (algebraMap (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)))
  · exact IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (auxiliary_matrix_polynomial k N))
      (auxiliary_matrix_polynomial k N)

/-- A self-map of the general linear group. -/
noncomputable def transposeInverse (g : Matrix.GeneralLinearGroup (Fin N) k) :
    Matrix.GeneralLinearGroup (Fin N) k :=
  ⟨((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)ᵀ,
   ((g : Matrix (Fin N) (Fin N) k))ᵀ,
   by rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one],
   by rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one]⟩

/-- The underlying matrix of this map is the transpose of the inverse matrix. -/
@[simp] theorem transposeInverse_apply (g : Matrix.GeneralLinearGroup (Fin N) k) :
    ((transposeInverse g : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)ᵀ :=
  rfl

/-- A monoid homomorphism from a general linear group to itself. -/
noncomputable def transposeInverseMonoidHom :
    Matrix.GeneralLinearGroup (Fin N) k →* Matrix.GeneralLinearGroup (Fin N) k where
  toFun := transposeInverse
  map_one' := by
    apply Units.ext
    rw [transposeInverse_apply, inv_one, Matrix.GeneralLinearGroup.coe_one,
      Matrix.transpose_one]
  map_mul' g₁ g₂ := by
    apply Units.ext
    rw [Units.val_mul, transposeInverse_apply, transposeInverse_apply, transposeInverse_apply,
      mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul]

/-- The monoid homomorphism acts by transposing the inverse matrix. -/
@[simp] theorem transposeInverseMonoidHom_apply (g : Matrix.GeneralLinearGroup (Fin N) k) :
    ((transposeInverseMonoidHom g : Matrix.GeneralLinearGroup (Fin N) k) :
        Matrix (Fin N) (Fin N) k) =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)ᵀ :=
  rfl

/-- A general-linear-indexed algebra endomorphism of the localization. -/
noncomputable def matrixLocalizationFirstAction
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    Localization.Away (auxiliary_matrix_polynomial k N) →ₐ[k]
      Localization.Away (auxiliary_matrix_polynomial k N) :=
  IsLocalization.liftAlgHom
    (f := matrixPolynomialMapToLocalization
      ((transposeInverseMonoidHom g : Matrix.GeneralLinearGroup (Fin N) k) :
        Matrix (Fin N) (Fin N) k))
    (matrixPolynomialMapToLocalization_isUnit_of_mem_powers (transposeInverseMonoidHom g))

/-- On canonical polynomial images in the localization, the first action applies the
matrix-parameterized polynomial transform associated with the transformed invertible matrix. -/
@[simp] theorem matrixLocalizationFirstAction_algebraMap_apply
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    matrixLocalizationFirstAction g
        (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) a) =
      algebraMap _ _
        (transposeMulMvPolynomialAlgHom
          ((transposeInverseMonoidHom g : Matrix.GeneralLinearGroup (Fin N) k) :
            Matrix (Fin N) (Fin N) k) a) := by
  simp only [matrixLocalizationFirstAction, IsLocalization.coe_liftAlgHom,
    IsLocalization.lift_eq]
  rfl

/-- The first action at the identity is the identity algebra homomorphism. -/
theorem matrixLocalizationFirstAction_one :
    matrixLocalizationFirstAction (1 : Matrix.GeneralLinearGroup (Fin N) k) =
      AlgHom.id k (Localization.Away (auxiliary_matrix_polynomial k N)) := by
  apply IsLocalization.algHom_ext (R := k)
    (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (auxiliary_matrix_polynomial k N))
    (B := Localization.Away (auxiliary_matrix_polynomial k N))
    (Submonoid.powers (auxiliary_matrix_polynomial k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change matrixLocalizationFirstAction (1 : Matrix.GeneralLinearGroup (Fin N) k)
      (algebraMap (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)) a) =
    AlgHom.id k (Localization.Away (auxiliary_matrix_polynomial k N))
      (algebraMap (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)) a)
  rw [matrixLocalizationFirstAction_algebraMap_apply, AlgHom.id_apply, map_one,
    Units.val_one, transposeMulMvPolynomialAlgHom_one, AlgHom.id_apply]

/-- The first action takes group multiplication to composition of algebra endomorphisms. -/
theorem matrixLocalizationFirstAction_mul
    (g₁ g₂ : Matrix.GeneralLinearGroup (Fin N) k) :
    matrixLocalizationFirstAction (g₁ * g₂) =
      (matrixLocalizationFirstAction g₁).comp (matrixLocalizationFirstAction g₂) := by
  apply IsLocalization.algHom_ext (R := k)
    (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (auxiliary_matrix_polynomial k N))
    (B := Localization.Away (auxiliary_matrix_polynomial k N))
    (Submonoid.powers (auxiliary_matrix_polynomial k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change matrixLocalizationFirstAction (g₁ * g₂)
      (algebraMap (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)) a) =
    (matrixLocalizationFirstAction g₁).comp (matrixLocalizationFirstAction g₂)
      (algebraMap (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)) a)
  rw [matrixLocalizationFirstAction_algebraMap_apply, AlgHom.comp_apply,
    matrixLocalizationFirstAction_algebraMap_apply,
    matrixLocalizationFirstAction_algebraMap_apply, map_mul, Units.val_mul,
    transposeMulMvPolynomialAlgHom_mul, AlgHom.comp_apply]

/-- A representation of the general linear group on the localization. -/
noncomputable def matrixLocalizationFirstRepresentation (k : Type*) [Field k] (N : ℕ) :
    _root_.Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (Localization.Away (auxiliary_matrix_polynomial k N)) where
  toFun g := (matrixLocalizationFirstAction g).toLinearMap
  map_one' := by
    change (matrixLocalizationFirstAction
      (1 : Matrix.GeneralLinearGroup (Fin N) k)).toLinearMap = _
    rw [matrixLocalizationFirstAction_one]
    rfl
  map_mul' g₁ g₂ := by
    change (matrixLocalizationFirstAction (g₁ * g₂)).toLinearMap = _
    rw [matrixLocalizationFirstAction_mul]
    rfl

/-- The representation and the first action give the same endomorphism on every localization
element. -/
@[simp] theorem matrixLocalizationFirstRepresentation_apply
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (auxiliary_matrix_polynomial k N)) :
    matrixLocalizationFirstRepresentation k N g x = matrixLocalizationFirstAction g x :=
  rfl

/-- On polynomial images in the localization, the representation agrees with the canonical image
of the indicated polynomial transform. -/
theorem matrixLocalizationFirstRepresentation_algebraMap_apply
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    matrixLocalizationFirstRepresentation k N g
        (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) a) =
      algebraMap _ _
        (GeneralLinearGroup.transposeMulMvPolynomialRepresentation k N
          (transposeInverseMonoidHom g) a) := by
  rw [GeneralLinearGroup.transposeMulMvPolynomialRepresentation_apply]
  exact matrixLocalizationFirstAction_algebraMap_apply g a

/-- The first action commutes with the companion algebra endomorphism. -/
theorem matrixLocalizationFirstAction_commutes
    (g h : Matrix.GeneralLinearGroup (Fin N) k) :
    (matrixLocalizationFirstAction g).comp (generalLinearGroupLocalizationMap h) =
      (generalLinearGroupLocalizationMap h).comp (matrixLocalizationFirstAction g) := by
  apply IsLocalization.algHom_ext (R := k)
    (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (auxiliary_matrix_polynomial k N))
    (B := Localization.Away (auxiliary_matrix_polynomial k N))
    (Submonoid.powers (auxiliary_matrix_polynomial k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change (matrixLocalizationFirstAction g).comp (generalLinearGroupLocalizationMap h)
      (algebraMap (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)) a) =
    (generalLinearGroupLocalizationMap h).comp (matrixLocalizationFirstAction g)
      (algebraMap (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N)) a)
  rw [AlgHom.comp_apply, AlgHom.comp_apply,
    generalLinearGroupLocalizationMap_algebraMap_apply,
    matrixLocalizationFirstAction_algebraMap_apply,
    matrixLocalizationFirstAction_algebraMap_apply,
    generalLinearGroupLocalizationMap_algebraMap_apply]
  have hcomm := AlgHom.congr_fun
    (transposeMulMvPolynomialAlgHom_commute_auxiliary
      ((transposeInverseMonoidHom g : Matrix.GeneralLinearGroup (Fin N) k) :
        Matrix (Fin N) (Fin N) k)
      (h : Matrix (Fin N) (Fin N) k)) a
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at hcomm
  rw [hcomm]

/-- The two indicated representations commute. -/
theorem matrixLocalizationFirstRepresentation_commutes
    (g h : Matrix.GeneralLinearGroup (Fin N) k) :
    matrixLocalizationFirstRepresentation k N g *
        generalLinearGroupLocalizationRepresentation k N h =
      generalLinearGroupLocalizationRepresentation k N h *
        matrixLocalizationFirstRepresentation k N g := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, Module.End.mul_apply,
    matrixLocalizationFirstRepresentation_apply,
    generalLinearGroupLocalizationRepresentation_apply_eq_map,
    generalLinearGroupLocalizationRepresentation_apply_eq_map,
    matrixLocalizationFirstRepresentation_apply]
  exact AlgHom.congr_fun (matrixLocalizationFirstAction_commutes g h) x

/-- A representation of a product of two general linear groups on a localization. -/
noncomputable def matrixLocalizationProductRepresentation (k : Type*) [Field k] (N : ℕ) :
    _root_.Representation k
      (Matrix.GeneralLinearGroup (Fin N) k × Matrix.GeneralLinearGroup (Fin N) k)
      (Localization.Away (auxiliary_matrix_polynomial k N)) :=
  Representation.ofCommuting (matrixLocalizationFirstRepresentation k N)
    (generalLinearGroupLocalizationRepresentation k N)
    matrixLocalizationFirstRepresentation_commutes

/-- The product representation applies the first and second factor endomorphisms in
succession. -/
@[simp] theorem matrixLocalizationProductRepresentation_apply
    (g h : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (auxiliary_matrix_polynomial k N)) :
    matrixLocalizationProductRepresentation k N (g, h) x =
      matrixLocalizationFirstAction g (generalLinearGroupLocalizationMap h x) :=
  rfl

/-- Evaluating the matrix polynomial transform agrees with evaluating the original polynomial
after multiplication by the transposed matrix. -/
lemma matrixPolynomialMap_eval (M g : Matrix (Fin N) (Fin N) k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2)
        (transposeMulMvPolynomialAlgHom M p) =
      MvPolynomial.eval (fun ij : Fin N × Fin N => (Mᵀ * g) ij.1 ij.2) p := by
  classical
  suffices halgs :
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => g ij.1 ij.2)).comp
          (transposeMulMvPolynomialAlgHom M) =
        (MvPolynomial.aeval (fun ij : Fin N × Fin N => (Mᵀ * g) ij.1 ij.2) :
          MvPolynomial (Fin N × Fin N) k →ₐ[k] k) by
    have := AlgHom.congr_fun halgs p
    simpa [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using this
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, transposeMulMvPolynomialAlgHom_X, map_sum,
    MvPolynomial.aeval_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, MvPolynomial.aeval_X, smul_eq_mul, Matrix.transpose_apply]

/-- Evaluating the first general-linear representation translates the evaluation argument by left
division. -/
lemma matrixLocalizationFirstRepresentation_eval
    (g₀ g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (auxiliary_matrix_polynomial k N)) :
    localization_evaluation_ringHom (matrixLocalizationFirstRepresentation k N g₀ x) g =
      localization_evaluation_ringHom x (g₀⁻¹ * g) := by
  have key : ∀ a : MvPolynomial (Fin N × Fin N) k,
      localization_evaluation_ringHom
          (matrixLocalizationFirstRepresentation k N g₀
            (algebraMap (MvPolynomial (Fin N × Fin N) k) _ a)) g =
        localization_evaluation_ringHom (algebraMap _ _ a) (g₀⁻¹ * g) := by
    intro a
    rw [matrixLocalizationFirstRepresentation_apply,
      matrixLocalizationFirstAction_algebraMap_apply,
      localization_evaluation_algebraMap, localization_evaluation_algebraMap,
      matrix_polynomial_evaluation_apply, matrix_polynomial_evaluation_apply]
    show MvPolynomial.eval
        (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (transposeMulMvPolynomialAlgHom
          ((transposeInverseMonoidHom g₀ : Matrix.GeneralLinearGroup (Fin N) k) :
            Matrix (Fin N) (Fin N) k) a) = _
    rw [matrixPolynomialMap_eval]
    rfl
  let F : Localization.Away (auxiliary_matrix_polynomial k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) g).comp
      ((localization_evaluation_ringHom (k := k) (N := N)).comp
        (matrixLocalizationFirstAction g₀).toRingHom)
  let G : Localization.Away (auxiliary_matrix_polynomial k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) (g₀⁻¹ * g)).comp
      localization_evaluation_ringHom
  have hFG : F = G := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (auxiliary_matrix_polynomial k N))
    apply RingHom.ext
    intro a
    simp only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
    rw [← matrixLocalizationFirstRepresentation_apply]
    exact key a
  have hx := RingHom.congr_fun hFG x
  simpa only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, ← matrixLocalizationFirstRepresentation_apply] using hx

end RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions

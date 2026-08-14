/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction
import RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

namespace RepresentationTheory.Auxiliary.GeneralLinearLocalizationFiltration

open MvPolynomial
open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
open RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

variable {k : Type*} [Field k] {N : ℕ}

/-- The linear map sending a matrix-entry polynomial into the localization at a specified
inverse-power degree. -/
noncomputable def denominator_power_embedding (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    MvPolynomial (Fin N × Fin N) k →ₗ[k]
      Localization.Away (auxiliary_matrix_polynomial k N) :=
  (LinearMap.mulRight k
    (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r)).comp
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (auxiliary_matrix_polynomial k N))).toLinearMap

/-- The degree-`r` embedding sends a polynomial to its canonical localized image multiplied by
the `r`-th power of the distinguished inverse. -/
@[simp] theorem denominator_power_embedding_apply
    (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k) :
    denominator_power_embedding k N r Q =
      algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
        * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r := by
  rw [denominator_power_embedding, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']

/-- The degree-indexed linear embedding of matrix-entry polynomials into the localization is
injective. -/
theorem denominator_power_embedding_injective (r : ℕ) :
    Function.Injective (denominator_power_embedding (k := k) (N := N) r) := by
  intro Q₁ Q₂ h
  rw [denominator_power_embedding_apply, denominator_power_embedding_apply] at h
  apply matrix_polynomial_algebraMap_injective
  have key := congrArg
    (· * algebraMap (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (auxiliary_matrix_polynomial k N))
        (auxiliary_matrix_polynomial k N) ^ r) h
  simpa only [mul_assoc,
    mul_comm (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r),
    algebraMap_pow_mul_invSelf_pow, mul_one] using key

/-- A natural-number-indexed family of submodules in the localization away from the auxiliary
matrix polynomial. -/
noncomputable def localization_degree_filtration
    (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    Submodule k (Localization.Away (auxiliary_matrix_polynomial k N)) :=
  LinearMap.range (denominator_power_embedding k N r)

/-- Membership in filtration level `r` is equivalent to having a polynomial-numerator
presentation with inverse exponent `r`. -/
theorem mem_localization_degree_filtration_iff_exists_presentation
    (r : ℕ) (f : Localization.Away (auxiliary_matrix_polynomial k N)) :
    f ∈ localization_degree_filtration k N r ↔
      ∃ Q : MvPolynomial (Fin N × Fin N) k,
        f = algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q
          * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r := by
  simp only [localization_degree_filtration, LinearMap.mem_range,
    denominator_power_embedding_apply]
  exact ⟨fun ⟨Q, hQ⟩ => ⟨Q, hQ.symm⟩, fun ⟨Q, hQ⟩ => ⟨Q, hQ.symm⟩⟩

/-- A localized element belongs to filtration level `r` exactly when its denominator order is at
most `r`. -/
theorem mem_localization_degree_filtration_iff_order_le
    (r : ℕ) (f : Localization.Away (auxiliary_matrix_polynomial k N)) :
    f ∈ localization_degree_filtration k N r ↔ localization_denominator_order f ≤ r := by
  rw [mem_localization_degree_filtration_iff_exists_presentation]
  constructor
  · rintro ⟨Q, hQ⟩
    exact denominator_order_le_of_exists_presentation ⟨Q, hQ⟩
  · intro hle
    obtain ⟨Q, hQ⟩ := exists_numerator_at_denominator_order f
    obtain ⟨s, hs⟩ : ∃ s, localization_denominator_order f = s := ⟨_, rfl⟩
    rw [hs] at hQ hle
    refine ⟨Q * auxiliary_matrix_polynomial k N ^ (r - s), ?_⟩
    rw [hQ, map_mul, map_pow, mul_assoc,
      show IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ r =
          IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (r - s)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ s
        from by rw [← pow_add]; congr 1; omega,
      ← mul_assoc (algebraMap (MvPolynomial (Fin N × Fin N) k) _
        (auxiliary_matrix_polynomial k N) ^ (r - s)),
      algebraMap_pow_mul_invSelf_pow, one_mul]

/-- The degree-zero polynomial embedding is the linear map underlying the canonical algebra
homomorphism into the localization. -/
theorem denominator_power_embedding_zero :
    denominator_power_embedding k N 0 =
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N))).toLinearMap :=
  LinearMap.ext fun Q => by
    rw [denominator_power_embedding_apply, pow_zero, mul_one, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom']

/-- The zeroth filtered submodule is the range of the canonical linear map from the matrix-entry
polynomial ring. -/
theorem localization_degree_filtration_zero :
    localization_degree_filtration k N 0 = LinearMap.range
      (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
        (Localization.Away (auxiliary_matrix_polynomial k N))).toLinearMap := by
  rw [localization_degree_filtration, denominator_power_embedding_zero]

/-- The degree filtration on the localization is monotone in its natural-number index. -/
theorem localization_degree_filtration_monotone :
    Monotone (localization_degree_filtration k N) := by
  intro r₁ r₂ hr f hf
  rw [mem_localization_degree_filtration_iff_order_le] at hf ⊢
  omega

/-- The supremum of all levels of the localization degree filtration is the full localization. -/
theorem iSup_localization_degree_filtration :
    (⨆ r, localization_degree_filtration k N r) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  exact Submodule.mem_iSup_of_mem (localization_denominator_order f)
    ((mem_localization_degree_filtration_iff_order_le _ f).mpr le_rfl)

/-- Acting on a degree-indexed polynomial embedding produces the embedded transformed polynomial
scaled by the matching inverse determinant power. -/
theorem action_denominator_power_embedding
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    generalLinearGroupLocalizationRepresentation k N g
        (denominator_power_embedding k N r Q) =
      ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
        denominator_power_embedding k N r
          (generalLinearGroupMvPolynomialRightMul k N g Q) := by
  rw [denominator_power_embedding_apply, denominator_power_embedding_apply,
    generalLinearGroupLocalizationRepresentation_apply_eq_map, map_mul,
    generalLinearGroupLocalizationMap_algebraMap_apply, map_pow,
    ← generalLinearGroupLocalizationRepresentation_apply_eq_map,
    generalLinearGroupLocalizationRepresentation_apply_invSelf, smul_pow, mul_smul_comm]
  rfl

/-- Every level of the localization degree filtration is stable under the displayed general
linear group action. -/
theorem localization_degree_filtration_stable
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    {x : Localization.Away (auxiliary_matrix_polynomial k N)}
    (hx : x ∈ localization_degree_filtration k N r) :
    generalLinearGroupLocalizationRepresentation k N g x ∈
      localization_degree_filtration k N r := by
  obtain ⟨Q, rfl⟩ := LinearMap.mem_range.mp hx
  rw [action_denominator_power_embedding]
  exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

/-- A matrix-entry polynomial belongs to the displayed submodule exactly when it is divisible by
the auxiliary matrix polynomial. -/
theorem mem_auxiliary_polynomial_submodule_iff_dvd
    (Q : MvPolynomial (Fin N × Fin N) k) :
    Q ∈ matrixIndexedPolynomialSubmodule k N ↔ auxiliary_matrix_polynomial k N ∣ Q := by
  rw [matrixIndexedPolynomialSubmodule, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  exact Iff.rfl

/-- At positive degree, an embedded polynomial lies in the preceding filtration level exactly
when the auxiliary polynomial divides it. -/
theorem denominator_power_embedding_mem_previous_iff_dvd
    (r : ℕ) (hr : 1 ≤ r) (Q : MvPolynomial (Fin N × Fin N) k) :
    denominator_power_embedding k N r Q ∈ localization_degree_filtration k N (r - 1) ↔
      auxiliary_matrix_polynomial k N ∣ Q := by
  rw [mem_localization_degree_filtration_iff_exists_presentation]
  constructor
  · rintro ⟨Q', hQ'⟩
    have e1 : algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q =
        denominator_power_embedding k N r Q
          * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
            (auxiliary_matrix_polynomial k N) ^ r :=
      algebraMap_eq_mul_pow_of_eq_mul_invSelf_pow (denominator_power_embedding_apply r Q)
    have e2 : algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q' =
        denominator_power_embedding k N r Q
          * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
            (auxiliary_matrix_polynomial k N) ^ (r - 1) :=
      algebraMap_eq_mul_pow_of_eq_mul_invSelf_pow hQ'
    refine ⟨Q', matrix_polynomial_algebraMap_injective ?_⟩
    have hpow :
        algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
            (auxiliary_matrix_polynomial k N) ^ r =
          algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
              (auxiliary_matrix_polynomial k N)
            * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
              (auxiliary_matrix_polynomial k N) ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e1, map_mul, e2, hpow]; ring
  · rintro ⟨Q', rfl⟩
    refine ⟨Q', ?_⟩
    have hsucc :
        (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) :
          Localization.Away (auxiliary_matrix_polynomial k N)) ^ r =
          IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [denominator_power_embedding_apply, map_mul, hsucc,
      show algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
            (auxiliary_matrix_polynomial k N)
          * algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q'
          * (IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (r - 1)) =
        (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N))
            (auxiliary_matrix_polynomial k N)
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N))
          * (algebraMap _ (Localization.Away (auxiliary_matrix_polynomial k N)) Q'
            * IsLocalization.Away.invSelf (auxiliary_matrix_polynomial k N) ^ (r - 1))
        from by ring,
      IsLocalization.Away.mul_invSelf, one_mul]

/-- The matrix-entry polynomial ring is linearly equivalent to each filtered localization
subtype. -/
noncomputable def polynomial_equiv_localization_filtration
    (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    MvPolynomial (Fin N × Fin N) k ≃ₗ[k] ↥(localization_degree_filtration k N r) :=
  LinearEquiv.ofInjective (denominator_power_embedding k N r)
    (denominator_power_embedding_injective r)

/-- The underlying localized element of the filtration equivalence is the degree-indexed
polynomial embedding. -/
@[simp] theorem coe_polynomial_equiv_localization_filtration
    (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k) :
    ((polynomial_equiv_localization_filtration k N r Q :
      ↥(localization_degree_filtration k N r)) :
        Localization.Away (auxiliary_matrix_polynomial k N)) =
      denominator_power_embedding k N r Q :=
  rfl

/-- The linear map from a filtered localization submodule to the quotient of the matrix-entry
polynomial ring by the displayed submodule. -/
noncomputable def filtration_to_polynomial_quotient
    (k : Type*) [Field k] (N : ℕ) (r : ℕ) :
    ↥(localization_degree_filtration k N r) →ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
  (matrixIndexedPolynomialSubmodule k N).mkQ.comp
    (polynomial_equiv_localization_filtration k N r).symm.toLinearMap

/-- The quotient map sends the degree-indexed polynomial embedding to the canonical class of the
polynomial. -/
@[simp] theorem filtration_to_polynomial_quotient_map_denominator_embedding
    (r : ℕ) (Q : MvPolynomial (Fin N × Fin N) k) :
    filtration_to_polynomial_quotient k N r
        ⟨denominator_power_embedding k N r Q, LinearMap.mem_range_self _ _⟩ =
      Submodule.Quotient.mk Q := by
  rw [filtration_to_polynomial_quotient, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.mkQ_apply]
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext (coe_polynomial_equiv_localization_filtration r Q).symm

/-- The linear map from each filtration level to the polynomial quotient is surjective. -/
theorem filtration_to_polynomial_quotient_surjective (r : ℕ) :
    Function.Surjective (filtration_to_polynomial_quotient k N r) :=
  (Submodule.mkQ_surjective _).comp
    (polynomial_equiv_localization_filtration k N r).symm.surjective

/-- At positive degree, the kernel of the map to the polynomial quotient is the preceding
filtration level pulled back to the current subtype. -/
theorem ker_filtration_to_polynomial_quotient (r : ℕ) (hr : 1 ≤ r) :
    LinearMap.ker (filtration_to_polynomial_quotient k N r) =
      (localization_degree_filtration k N (r - 1)).comap
        (localization_degree_filtration k N r).subtype := by
  ext x
  obtain ⟨Q, rfl⟩ := (polynomial_equiv_localization_filtration k N r).surjective x
  rw [LinearMap.mem_ker,
    show filtration_to_polynomial_quotient k N r
        (polynomial_equiv_localization_filtration k N r Q) = Submodule.Quotient.mk Q
      from filtration_to_polynomial_quotient_map_denominator_embedding r Q,
    Submodule.Quotient.mk_eq_zero, mem_auxiliary_polynomial_submodule_iff_dvd,
    Submodule.mem_comap, Submodule.coe_subtype,
    coe_polynomial_equiv_localization_filtration,
    denominator_power_embedding_mem_previous_iff_dvd r hr]

/-- For positive degree, the quotient of one filtration level by the preceding level is linearly
equivalent to the matrix-polynomial quotient by the displayed submodule. -/
noncomputable def filtration_quotient_equiv_polynomial_quotient
    (k : Type*) [Field k] (N : ℕ) (r : ℕ) (hr : 1 ≤ r) :
    (↥(localization_degree_filtration k N r) ⧸
      (localization_degree_filtration k N (r - 1)).comap
        (localization_degree_filtration k N r).subtype) ≃ₗ[k]
      (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
  (Submodule.quotEquivOfEq _ _
    (ker_filtration_to_polynomial_quotient (k := k) (N := N) r hr).symm).trans
      (LinearMap.quotKerEquivOfSurjective (filtration_to_polynomial_quotient k N r)
        (filtration_to_polynomial_quotient_surjective r))

/-- Evaluating the indicated negative power at a general linear matrix yields the corresponding
power of the inverse determinant. -/
theorem auxiliary_negative_power_apply
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ) :
    ((generalLinearGroupToUnits k N ^ (-(r : ℤ))) g : k) =
      ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r := by
  have happ :
      (generalLinearGroupToUnits k N ^ (-(r : ℤ))) g =
        (generalLinearGroupToUnits k N g) ^ (-(r : ℤ)) := rfl
  rw [happ, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, ← inv_pow]
  rfl

/-- The map from a filtration level to the polynomial quotient intertwines the displayed general
linear group actions. -/
theorem filtration_to_polynomial_quotient_equivariant
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ)
    (x : ↥(localization_degree_filtration k N r)) :
    filtration_to_polynomial_quotient k N r
        ⟨generalLinearGroupLocalizationRepresentation k N g
            (x : Localization.Away (auxiliary_matrix_polynomial k N)),
          localization_degree_filtration_stable g r x.2⟩ =
      naturalIndexedQuotientRepresentation k N r g
        (filtration_to_polynomial_quotient k N r x) := by
  obtain ⟨Q, rfl⟩ := (polynomial_equiv_localization_filtration k N r).surjective x
  have hval :
      generalLinearGroupLocalizationRepresentation k N g
          ((polynomial_equiv_localization_filtration k N r Q :
            ↥(localization_degree_filtration k N r)) :
              Localization.Away (auxiliary_matrix_polynomial k N)) =
        denominator_power_embedding k N r
          (((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
            generalLinearGroupMvPolynomialRightMul k N g Q) := by
    rw [coe_polynomial_equiv_localization_filtration,
      action_denominator_power_embedding, map_smul]
  rw [show (⟨generalLinearGroupLocalizationRepresentation k N g
          ((polynomial_equiv_localization_filtration k N r Q :
            ↥(localization_degree_filtration k N r)) :
              Localization.Away (auxiliary_matrix_polynomial k N)),
        localization_degree_filtration_stable g r
          (polynomial_equiv_localization_filtration k N r Q).2⟩ :
          ↥(localization_degree_filtration k N r)) =
      ⟨denominator_power_embedding k N r
          (((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r •
            generalLinearGroupMvPolynomialRightMul k N g Q),
        LinearMap.mem_range_self _ _⟩ from Subtype.ext hval,
    filtration_to_polynomial_quotient_map_denominator_embedding,
    show filtration_to_polynomial_quotient k N r
        (polynomial_equiv_localization_filtration k N r Q) = Submodule.Quotient.mk Q
      from filtration_to_polynomial_quotient_map_denominator_embedding r Q,
    naturalIndexedQuotientRepresentation, twistByCharacter_apply,
    auxiliary_negative_power_apply, matrixPolynomialQuotientRepresentation_apply_mk,
    Submodule.Quotient.mk_smul]

end RepresentationTheory.Auxiliary.GeneralLinearLocalizationFiltration

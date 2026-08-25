/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
import RepresentationTheory.AuxiliaryInvariantBilinearPairings
import RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions
import RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation



open scoped TensorProduct

noncomputable section

namespace RepresentationTheory.GeneralLinearGroup.TensorLocalization

open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization
  RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation







/-- The auxiliary map on multivariate polynomials commutes with natural powers. -/
theorem auxiliaryPolynomialMap_pow {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k) (s : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (p ^ s) = (RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g p) ^ s := by
  simp only [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation, map_pow]


/-- If a family of linear endomorphisms indexed by the general linear group satisfies the auxiliary property, then pointwise scaling it by any natural power of the inverse determinant preserves that property. -/
theorem _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty.detInvPow_smul {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ) (s : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N
      (fun g : Matrix.GeneralLinearGroup (Fin N) k =>
        (((g : Matrix (Fin N) (Fin N) k).det)⁻¹) ^ s • ρ g) := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b, fun a c => (MvPolynomial.X (Sum.inr ())) ^ s * P a c, fun g a c => ?_⟩
  rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hP g a c,
    RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_mul, auxiliaryPolynomialMap_pow, RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.evaluate_X_unit]




/-- Evaluating a negative natural integer power of the auxiliary unit-valued map gives the corresponding natural power of the inverse determinant. -/
theorem auxiliaryUnitMap_zpow_neg_nat_apply {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (r : ℕ) :
    ((RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ (-(r : ℤ))) g : k) = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ ^ r := by
  have happ : (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N ^ (-(r : ℤ))) g = (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k N g) ^ (-(r : ℤ)) := rfl
  rw [happ, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    ← inv_pow]
  rfl



variable (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]


/-- The displayed family of linear endomorphisms indexed by the general linear group satisfies the auxiliary property over an algebraically closed field of characteristic zero. -/
theorem auxiliaryLinearEndomorphismFamily_condition :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n (fun g => RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g) := by
  have hfun : (fun g => RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g)
      = (fun g : Matrix.GeneralLinearGroup (Fin n) k =>
          (((g : Matrix (Fin n) (Fin n) k).det)⁻¹) ^ lam.toNat •
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k n lam.toNatAt).ρ g) := by
    funext g
    change ((RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ))) g : k) • RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n lam.toNatAt g = _
    rw [auxiliaryUnitMap_zpow_neg_nat_apply]
    rfl
  rw [hfun]
  exact (RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation.auxiliaryFDRep_property n lam.toNatAt).detInvPow_smul lam.toNat




/-- There exists a map on the tensor product such that, after applying the displayed auxiliary evaluator to its value on a pure tensor, evaluation at a group element equals the displayed auxiliary tensor map with the indexed linear endomorphism applied to the second factor. -/
theorem exists_tensorMap_tmul_apply :
    ∃ psm : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k]
        Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n),
      ∀ (u : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
        (g : Matrix.GeneralLinearGroup (Fin n) k),
        RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (psm (u ⊗ₜ[k] v)) g
          = RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) := by
  obtain ⟨d, b, P, hP⟩ := auxiliaryLinearEndomorphismFamily_condition n lam k
  set B2 : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k →ₗ[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k]
      Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) :=
    ∑ a, ∑ c,
      LinearMap.smulRight
        ((RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k) ∘ₗ
          (TensorProduct.mk k (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)).flip (b a))
        (LinearMap.smulRight (b.coord c) (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c))) with hB2
  refine ⟨TensorProduct.lift B2, ?_⟩
  intro u v g

  have hmap : TensorProduct.lift B2 (u ⊗ₜ[k] v)
      = ∑ a, ∑ c,
          (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c) • RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c) := by
    rw [TensorProduct.lift.tmul, hB2]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      Module.Basis.coord_apply, smul_smul]
  rw [hmap]

  have hLHS : RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (∑ a, ∑ c,
        (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c) • RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c)) g
      = ∑ a, ∑ c,
          (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c)
            * RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P a c) := by
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization.localization_evaluation_smul (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] b a) * b.repr v c)
        (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom (P a c)), Pi.smul_apply, smul_eq_mul,
      ← RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_localization_ringHom_action_apply]
  rw [hLHS]

  let Bu : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] k :=
    (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k).comp
      (TensorProduct.mk k (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) u)
  have hBu : ∀ w, Bu w = RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] w) := fun w => rfl
  have step1 : RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v
      = ∑ c, b.repr v c • RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g (b c) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [map_smul]

  have hBuc : ∀ c, Bu (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g (b c))
      = ∑ a, RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P a c)
          * RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] b a) := by
    intro c
    conv_lhs => rw [← b.sum_repr (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g (b c))]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul, hBu, hP]

  have hexp : RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v)
      = ∑ c, ∑ a, b.repr v c *
          (RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g (P a c)
            * RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] b a)) := by
    have e1 : RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v)
        = Bu (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) := (hBu _).symm
    rw [e1, step1, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul, hBuc, Finset.mul_sum]
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring


/-- A linear map from the tensor product of two auxiliary modules to the localization away from the distinguished element. -/
noncomputable def tensorToLocalization :
    RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k]
      Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) :=
  (exists_tensorMap_tmul_apply n lam k).choose


/-- After applying the displayed auxiliary evaluator to the tensor-to-localization image of a pure tensor, its value at a group element equals the displayed auxiliary tensor map with the indexed linear endomorphism applied to the second factor. -/
theorem tensorToLocalization_tmul_apply (u : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k)
    (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) (g : Matrix.GeneralLinearGroup (Fin n) k) :
    RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (tensorToLocalization n lam k (u ⊗ₜ[k] v)) g
      = RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u ⊗ₜ[k] RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) :=
  (exists_tensorMap_tmul_apply n lam k).choose_spec u v g




/-- Applying the tensor-to-localization map to a pure tensor after the displayed group-indexed endomorphisms are applied to its factors equals applying the displayed product-indexed map to the tensor-to-localization image of the original pure tensor. -/
theorem tensorToLocalization_tmul_transform
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (u : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    tensorToLocalization n lam k
        (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace n lam k g u ⊗ₜ[k] RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k h v)
      = RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n (g, h) (tensorToLocalization n lam k (u ⊗ₜ[k] v)) := by

  have hinv : ∀ (g₀ : Matrix.GeneralLinearGroup (Fin n) k)
      (u' : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) (w : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace n lam k g₀ u' ⊗ₜ[k] w)
        = RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k (u' ⊗ₜ[k] RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g₀⁻¹ w) := by
    intro g₀ u' w
    have key := RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing_apply_groupMaps n lam k g₀ u' (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g₀⁻¹ w)
    have hww : RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g₀ (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g₀⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rwa [hww] at key

  apply RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_injective
  funext y

  rw [tensorToLocalization_tmul_apply]

  have hyh : RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k y (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k h v)
      = RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k (y * h) v := by
    rw [← Module.End.mul_apply, ← map_mul]
  rw [hyh, hinv g u (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k (y * h) v)]

  have hgyh : RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g⁻¹ (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k (y * h) v)
      = RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k (g⁻¹ * (y * h)) v := by
    rw [← Module.End.mul_apply, ← map_mul]
  rw [hgyh]

  have hbi : RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n (g, h) (tensorToLocalization n lam k (u ⊗ₜ[k] v))
      = RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationFirstRepresentation k n g (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n h
          (tensorToLocalization n lam k (u ⊗ₜ[k] v))) := by
    rw [RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation_apply, RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationFirstRepresentation_apply, RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation_apply_eq_map]
  rw [hbi,
    RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationFirstRepresentation_eval g y (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n h (tensorToLocalization n lam k (u ⊗ₜ[k] v))),
    RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization.localization_evaluation_action_apply h (g⁻¹ * y) (tensorToLocalization n lam k (u ⊗ₜ[k] v)),
    tensorToLocalization_tmul_apply]

  rw [mul_assoc]




/-- For an equivariant linear map into the indicated localization, each value is obtained by applying the tensor-to-localization map to a pure tensor with the same second factor. -/
theorem exists_tensorToLocalization_tmul_eq_of_equivariant
    (ι : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
    (hι : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      ι (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) = RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (ι v))
    (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    ∃ u : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k,
      ι v = tensorToLocalization n lam k (u ⊗ₜ[k] v) := by

  let epsIota : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] k :=
    { toFun := fun w => RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (ι w) 1
      map_add' := fun w w' => by rw [map_add, map_add]; rfl
      map_smul' := fun c w => by
        rw [map_smul, RingHom.id_apply, RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization.localization_evaluation_smul, Pi.smul_apply, smul_eq_mul] }

  refine ⟨(RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).symm epsIota, ?_⟩

  have hpair : ∀ w, RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing n lam k
      ((RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).symm epsIota ⊗ₜ[k] w) = RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (ι w) 1 := by
    intro w
    rw [RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing_eq_contractLeft, LinearEquiv.apply_symm_apply, contractLeft_apply]
    rfl

  apply RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_injective
  funext g
  rw [tensorToLocalization_tmul_apply, hpair (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v), hι,
    RepresentationTheory.Auxiliary.GeneralLinearPolynomialRealization.localization_evaluation_action_apply, one_mul]


/-- The range of an equivariant linear map into the indicated localization is contained in the range of the tensor-to-localization map. -/
theorem range_le_tensorToLocalization_range_of_equivariant
    (ι : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
    (hι : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      ι (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) = RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (ι v)) :
    LinearMap.range ι ≤ LinearMap.range (tensorToLocalization n lam k) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := exists_tensorToLocalization_tmul_eq_of_equivariant n lam k ι hι v
  exact ⟨u ⊗ₜ[k] v, hu.symm⟩

end RepresentationTheory.GeneralLinearGroup.TensorLocalization

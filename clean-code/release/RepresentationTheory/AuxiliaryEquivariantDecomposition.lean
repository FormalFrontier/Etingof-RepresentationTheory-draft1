/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
import RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions
import RepresentationTheory.GeneralLinearGroup.TensorLocalization
import RepresentationTheory.Representation.AlgebraDensity
import RepresentationTheory.TensorCoefficientIndependence
import RepresentationTheory.AuxiliaryRepresentationParameters
import RepresentationTheory.GeneralLinearGroup.Localization
import RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations
import RepresentationTheory.Auxiliary.EquivariantMaps
import RepresentationTheory.LinearEquivCompatibility
import RepresentationTheory.Alignment.Attribute

set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

noncomputable section

namespace RepresentationTheory.AuxiliaryEquivariantDecomposition

open RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

variable {k : Type*}

/-- An auxiliary representation on a direct sum of tensor products. -/
noncomputable def auxiliaryTensorDirectSumRepresentation (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] :
    Representation k
      (Matrix.GeneralLinearGroup (Fin n) k × Matrix.GeneralLinearGroup (Fin n) k)
      (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
        (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) :=
  Representation.directSum fun lam =>
    Representation.tprod
      ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace n lam k).comp (MonoidHom.fst _ _))
      ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).comp (MonoidHom.snd _ _))

/-- The auxiliary tensor direct-sum representation acts componentwise. -/
@[simp] theorem auxiliaryTensorDirectSumRepresentation_apply (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k]
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (x : DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
      (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) :
    auxiliaryTensorDirectSumRepresentation n k (g, h) x =
      DirectSum.lmap (fun lam =>
        TensorProduct.map (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace n lam k g) (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k h)) x :=
  rfl

/-- An auxiliary predicate on two representations and a linear equivalence. -/
def Auxiliary.IsRepresentationRelation {G W₁ W₂ : Type*} [Monoid G] [Field k]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    (ρ₁ : Representation k G W₁) (ρ₂ : Representation k G W₂)
    (e : W₁ ≃ₗ[k] W₂) : Prop :=
  ∀ (g : G) (x : W₁), e (ρ₁ g x) = ρ₂ g (e x)

/-- Equivariance of a linear equivalence is preserved by taking its inverse. -/
theorem Auxiliary.IsRepresentationRelation.symm {G W₁ W₂ : Type*} [Monoid G] [Field k]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    {ρ₁ : Representation k G W₁} {ρ₂ : Representation k G W₂}
    {e : W₁ ≃ₗ[k] W₂} (he : Auxiliary.IsRepresentationRelation ρ₁ ρ₂ e) :
    Auxiliary.IsRepresentationRelation ρ₂ ρ₁ e.symm := by
  intro g y
  apply e.injective
  rw [e.apply_symm_apply, he g (e.symm y), e.apply_symm_apply]

instance instDecidableEqAuxiliaryIndex (n : ℕ) : DecidableEq (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :=
  inferInstanceAs (DecidableEq {lam : Fin n → ℤ // Antitone lam})

/-- The auxiliary linear map from an indexed direct sum to the displayed localization. -/
noncomputable def auxiliaryDirectSumMap (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
        (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) →ₗ[k]
      Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) :=
  DirectSum.toModule k (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) _ (fun lam => RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k)

/-- On each direct-sum component, the auxiliary map agrees with the corresponding displayed map. -/
@[simp] theorem auxiliaryDirectSumMap_of (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (y : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    auxiliaryDirectSumMap n k (DirectSum.of _ lam y) = RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k y := by
  unfold auxiliaryDirectSumMap
  erw [DirectSum.toModule_lof]

/-- Each auxiliary component map commutes with the displayed action. -/
theorem auxiliary_map_intertwines (n : ℕ) (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k]
    (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (y : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k
        (TensorProduct.map (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace n lam k g) (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k h) y)
      = RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n (g, h) (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [TensorProduct.map_tmul]
      exact RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization_tmul_transform n lam k g h u v
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The auxiliary direct-sum map commutes with the displayed pair action. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.23.2" (role := primary)]
theorem auxiliaryDirectSumMap_intertwines (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (x : DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
        (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) :
    auxiliaryDirectSumMap n k (auxiliaryTensorDirectSumRepresentation n k (g, h) x)
      = RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n (g, h) (auxiliaryDirectSumMap n k x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of lam y =>
      rw [auxiliaryTensorDirectSumRepresentation_apply, DirectSum.lmap_of, auxiliaryDirectSumMap_of, auxiliaryDirectSumMap_of]
      exact auxiliary_map_intertwines n k lam g h y
  | add x₁ x₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-- Bijectivity of the auxiliary direct-sum map yields the indicated auxiliary predicate. -/
theorem auxiliary_nonempty_representationRelation_of_bijective
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (hbij : Function.Bijective (auxiliaryDirectSumMap n k)) :
    Nonempty { e : Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) ≃ₗ[k]
        (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
          (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) //
      Auxiliary.IsRepresentationRelation (RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n) (auxiliaryTensorDirectSumRepresentation n k) e } := by
  let e := LinearEquiv.ofBijective (auxiliaryDirectSumMap n k) hbij
  have he : Auxiliary.IsRepresentationRelation (auxiliaryTensorDirectSumRepresentation n k) (RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n) e := by
    intro gh x
    obtain ⟨g, h⟩ := gh
    change auxiliaryDirectSumMap n k (auxiliaryTensorDirectSumRepresentation n k (g, h) x)
      = RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n (g, h) (auxiliaryDirectSumMap n k x)
    exact auxiliaryDirectSumMap_intertwines n k g h x
  exact ⟨e.symm, he.symm⟩

/-- The map from a direct sum is injective when the component maps are injective and their ranges are independent. -/
theorem directSumToModule_injective_of_iSupIndep
    {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι]
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    {M : Type*} [AddCommGroup M] [Module R M]
    (f : ∀ i, N i →ₗ[R] M) (hf : ∀ i, Function.Injective (f i))
    (hindep : iSupIndep (fun i => LinearMap.range (f i))) :
    Function.Injective (DirectSum.toModule R ι M f) := by

  have hfeq : (fun i => ((LinearMap.range (f i)).subtype).comp ((f i).rangeRestrict)) = f := by
    funext i; exact LinearMap.subtype_comp_codRestrict (f i) _ _

  have hcomp : ∀ x, DirectSum.toModule R ι M f x
      = (DFinsupp.lsum ℕ (fun i => (LinearMap.range (f i)).subtype))
          (DFinsupp.mapRange.linearMap (fun i => (f i).rangeRestrict) x) := by
    intro x
    rw [DFinsupp.sum_mapRange_index.linearMap, hfeq]
    rfl

  have h1 : Function.Injective
      (DFinsupp.lsum ℕ (fun i => (LinearMap.range (f i)).subtype)) :=
    hindep.dfinsupp_lsum_injective

  have h2 : Function.Injective
      (DFinsupp.mapRange.linearMap (fun i => (f i).rangeRestrict)) := by
    have hcoe : ⇑(DFinsupp.mapRange.linearMap (fun i => (f i).rangeRestrict))
        = DFinsupp.mapRange (fun i => ⇑((f i).rangeRestrict)) (fun i => map_zero _) := rfl
    rw [hcoe, DFinsupp.mapRange_injective]
    refine fun i => LinearMap.ker_eq_bot.mp ?_
    rw [LinearMap.ker_rangeRestrict]
    exact LinearMap.ker_eq_bot.mpr (hf i)
  intro a b hab
  apply h2
  apply h1
  rw [← hcomp, ← hcomp, hab]

/-- The range of a direct-sum map is the supremum of its component ranges. -/
theorem directSumToModule_range
    {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (f : ∀ i, N i →ₗ[R] M) :
    LinearMap.range (DirectSum.toModule R ι M f) = ⨆ i, LinearMap.range (f i) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨a, rfl⟩ := hx
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i y =>
        have hval : DirectSum.toModule R ι M f (DirectSum.of N i y) = f i y := by
          erw [DirectSum.toModule_lof]
        rw [hval]
        exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ _)
    | add a b ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  · rw [iSup_le_iff]
    intro i
    have hfi : f i = (DirectSum.toModule R ι M f).comp (DirectSum.lof R ι N i) :=
      LinearMap.ext fun y => (DirectSum.toModule_lof R i y).symm
    rw [hfi]
    exact LinearMap.range_comp_le_range _ _

/-- The auxiliary representation gives a simple module. -/
@[source_ref "Chapter5/Discussion_after_Definition5.23.1" (role := primary),
  source_ref "Chapter5/Discussion_after_Definition5.23.1/Derived01" (role := supporting)]
theorem auxiliary_isSimpleModule (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModule := by
  haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Representation.asModule (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n lam.toNatAt)) :=
    RepresentationTheory.Representation.ModuleEquivAndTraceSeparation.isSimpleModule_fdRep_of_antitone k n lam.toNatAt lam.toNatWeight_antitone
  unfold RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
  exact RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.isSimpleModule_auxiliaryRepresentationConstruction _ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n lam.toNatAt)

/-- Each displayed auxiliary map is injective. -/
theorem auxiliary_injective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) :
    Function.Injective (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k) := by

  haveI hsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModule := auxiliary_isSimpleModule n k lam
  rw [injective_iff_map_eq_zero]
  intro z hz

  set z' : Module.Dual k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k :=
    TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap LinearMap.id z with hz'

  have key : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k)
      (w : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      contractLeft k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
          (TensorProduct.map LinearMap.id (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g)
            (TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap LinearMap.id w))
        = RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k w) g := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
          RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization_tmul_apply, RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing_eq_contractLeft]
        rfl
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

  have hcond : ∀ g, contractLeft k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
      (TensorProduct.map LinearMap.id (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g) z') = 0 := by
    intro g
    rw [hz', key g z, hz, map_zero, Pi.zero_apply]

  have hz'0 : z' = 0 :=
    RepresentationTheory.Representation.AlgebraDensity.eq_zero_of_contractLeft_representation_map_eq_zero (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k) z' hcond
  have hinj : Function.Injective (TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap
      (LinearMap.id : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) := by
    have hmap : TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap
        (LinearMap.id : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
        = (TensorProduct.congr (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k)
            (LinearEquiv.refl k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k))).toLinearMap := by
      rw [TensorProduct.toLinearMap_congr]; rfl
    rw [hmap]
    exact (TensorProduct.congr (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k) _).injective
  apply hinj
  rw [map_zero]
  exact hz'.symm.trans hz'0

/-- An auxiliary contraction is compatible with the displayed group action. -/
theorem auxiliary_contractLeft_map
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (w : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    contractLeft k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
        (TensorProduct.map LinearMap.id (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g)
          (TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap LinearMap.id w))
      = RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k w) g := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
        RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization_tmul_apply, RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryTensorPairing_eq_contractLeft]
      rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/-- If a finite auxiliary sum vanishes, then every indexed summand vanishes. -/
theorem auxiliary_component_eq_zero_of_sum_eq_zero
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (s : Finset (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n))
    (z : ∀ lam, RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
    (hsum : ∑ lam ∈ s, RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k (z lam) = 0) :
    ∀ lam ∈ s, RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k (z lam) = 0 := by

  have hzero : ∀ lam ∈ s,
      TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap LinearMap.id (z lam) = 0 := by
    intro lam0 hlam0
    refine RepresentationTheory.TensorCoefficientIndependence.tensor_eq_zero_on_finset_of_sum_contractions_eq_zero (k := k)
      (G := Matrix.GeneralLinearGroup (Fin n) k)
      (fun lam => RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) (fun lam => RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k) s
      (fun lam => auxiliary_isSimpleModule n k lam)
      (fun lam _ mu _ hne => RepresentationTheory.AuxiliaryRepresentationParameters.auxiliaryRepresentation_not_linearEquiv_of_parameters_ne n k hne)
      (fun lam => TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap LinearMap.id (z lam))
      ?_ lam0 hlam0
    intro g
    have hterm : ∀ lam ∈ s, contractLeft k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
        (TensorProduct.map LinearMap.id (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g)
          (TensorProduct.map (RepresentationTheory.AuxiliaryInvariantBilinearPairings.auxiliaryLinearEquivToDual n lam k).toLinearMap LinearMap.id (z lam)))
        = RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_ringHom (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k (z lam)) g :=
      fun lam _ => auxiliary_contractLeft_map n lam k g (z lam)
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_apply, ← map_sum, hsum, map_zero]
    rfl

  intro lam0 hlam0
  apply RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.localization_evaluation_injective
  funext g
  rw [← auxiliary_contractLeft_map n lam0 k g (z lam0), hzero lam0 hlam0]
  simp

/-- The ranges of the auxiliary component maps form an independent family. -/
theorem auxiliary_iSupIndep_range
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    iSupIndep (fun lam => LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k)) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum

  set z : ∀ lam, RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k :=
    fun lam => if h : lam ∈ s then (LinearMap.mem_range.mp (hv lam h)).choose else 0 with hzdef
  have hzv : ∀ lam ∈ s, RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k (z lam) = v lam := by
    intro lam h
    simp only [z, dif_pos h]
    exact (LinearMap.mem_range.mp (hv lam h)).choose_spec
  have hsum' : ∑ lam ∈ s, RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k (z lam) = 0 := by
    rw [Finset.sum_congr rfl hzv]; exact hsum
  intro lam0 hlam0
  rw [← hzv lam0 hlam0]
  exact auxiliary_component_eq_zero_of_sum_eq_zero n k s z hsum' lam0 hlam0

/-- The auxiliary direct-sum map is injective. -/
theorem auxiliaryDirectSumMap_injective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Function.Injective (auxiliaryDirectSumMap n k) :=
  directSumToModule_injective_of_iSupIndep _
    (auxiliary_injective n k) (auxiliary_iSupIndep_range n k)

set_option maxHeartbeats 800000 in

/-- The range of an auxiliary map is closed under the displayed action. -/
theorem auxiliary_range_mem_action
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    ∀ x ∈ LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k),
      RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g x ∈ LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k) := by

  have hbi1 : ∀ w, RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n (1, g) w = RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g w := by
    intro w
    rw [RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation_apply, ← RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationFirstRepresentation_apply, map_one, Module.End.one_apply,
      ← RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation_apply_eq_map]

  have key : ∀ z, RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k
        (TensorProduct.map LinearMap.id (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g) z)
      = RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
      have he := RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization_tmul_transform n lam k 1 g u v
      rw [show RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace n lam k 1 u = u from by rw [map_one]; rfl] at he
      rw [he, hbi1]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rintro _ ⟨z, rfl⟩
  exact ⟨TensorProduct.map LinearMap.id (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g) z, key z⟩

/-- The supremum of the auxiliary map ranges is closed under the displayed action. -/
theorem auxiliary_iSupRange_mem_action
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    ∀ x ∈ (⨆ lam, LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k)),
      RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g x ∈ ⨆ lam, LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k) := by
  intro x hx
  refine Submodule.iSup_induction
    (fun lam => LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k))
    (motive := fun y => RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g y ∈
      ⨆ lam, LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k)) hx ?_ ?_ ?_
  · intro lam y hy
    exact Submodule.mem_iSup_of_mem lam
      (auxiliary_range_mem_action n lam k g y hy)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

private theorem auxiliary_equivariantLinearEquiv_of_apply_eq_sub
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (r : ℕ) (ν : Fin n → ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (hval : ∀ i, lam.val i = (ν i : ℤ) - r) :
    Nonempty { e : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k ≃ₗ[k] RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n ν //
      ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
        e (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v)
          = RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(r : ℤ))) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n ν) g (e v) } := by

  have hnonneg : ∀ i, 0 ≤ lam.val i + (lam.toNat : ℤ) := by
    intro i
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
    have hlast : lam.val (Fin.last m) ≤ lam.val i := lam.property (Fin.le_last i)
    change 0 ≤ lam.val i + (((-(lam.val (Fin.last m))).toNat : ℕ) : ℤ)
    omega
  have hcast : ∀ i, (lam.toNatAt i : ℤ) = lam.val i + (lam.toNat : ℤ) := by
    intro i
    change (((lam.val i + (lam.toNat : ℤ)).toNat : ℕ) : ℤ) = lam.val i + (lam.toNat : ℤ)
    rw [Int.toNat_of_nonneg (hnonneg i)]

  have hshift_le : lam.toNat ≤ r := by
    cases n with
    | zero => exact Nat.zero_le r
    | succ m =>
        have hvl := hval (Fin.last m)
        change (-(lam.val (Fin.last m))).toNat ≤ r
        omega

  set c : ℕ := r - lam.toNat with hc
  have hnu : ∀ i, ν i = lam.toNatAt i + c := by
    intro i
    have h1 := hcast i
    have h2 := hval i
    omega
  have hνeq : (fun i => lam.toNatAt i + c) = ν := funext (fun i => (hnu i).symm)

  have hchar : RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(r : ℤ)) * RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ c
      = RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(lam.toNat : ℤ)) := by
    rw [← zpow_natCast (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n) c, ← zpow_add]
    congr 1
    omega

  rw [← hνeq]
  obtain ⟨e₀, he₀⟩ :=
    RepresentationTheory.LinearEquivCompatibility.exists_compatible_linearEquiv_of_antitone k n lam.toNatAt lam.toNatWeight_antitone c
  refine ⟨e₀, ?_⟩
  intro g v

  have key := (RepresentationTheory.LinearEquivCompatibility.RepresentationLinearEquiv.IsCompatible.map_both (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(r : ℤ))) he₀) g v
  rw [RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_mul, hchar] at key
  exact key

/-- An auxiliary indexed object admits an equivariant linear equivalence under the stated monotonicity condition. -/
theorem auxiliary_exists_equivariantLinearEquiv
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (r : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∃ (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n),
      Nonempty { e : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k ≃ₗ[k] RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n ν //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
          e (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v)
            = RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ (-(r : ℤ))) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n ν) g (e v) } :=

  ⟨⟨fun i => (ν i : ℤ) - r,
      fun _ _ hij => sub_le_sub_right (by exact_mod_cast hν hij) (r : ℤ)⟩,
    auxiliary_equivariantLinearEquiv_of_apply_eq_sub n k r ν _ (fun _ => rfl)⟩

/-- A simple auxiliary subrepresentation is the range of a compatible linear map. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.23.2" (role := primary)]
theorem auxiliary_exists_range_eq_of_isSimpleModule
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n))
    [FiniteDimensional k S.toSubmodule]
    (hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S)) :
    ∃ (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (ι : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)),
      (∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
        ι (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) = RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (ι v)) ∧
      LinearMap.range ι = S.toSubmodule := by

  obtain ⟨r, ν, hν, hf_ne⟩ :=
    RepresentationTheory.Auxiliary.EquivariantMaps.auxiliary_simple_subrepresentation_has_equivariant_map_after_negated_nat_power n k S hSsimple
  obtain ⟨f, hf⟩ := hf_ne

  obtain ⟨lam, he_ne⟩ :=
    auxiliary_exists_equivariantLinearEquiv n k r ν hν
  obtain ⟨e, he⟩ := he_ne


  set fe : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k ≃ₗ[k] S.toSubmodule := e.trans f with hfe
  have hfe_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      fe (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) = S.toRepresentation g (fe v) := by
    intro g v
    simp only [hfe, LinearEquiv.trans_apply]
    rw [he, hf]

  refine ⟨lam, S.toSubmodule.subtype ∘ₗ fe.toLinearMap, ?_, ?_⟩
  · intro g v
    change ((fe (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) : S.toSubmodule) : Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
        = RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g ((fe v : S.toSubmodule) : Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n))
    rw [hfe_equiv]
    exact LinearMap.coe_restrict_apply (S.apply_mem_toSubmodule g) (fe v)
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

/-- A simple auxiliary subrepresentation lies below the supremum of the component ranges. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.23.2" (role := supporting)]
theorem auxiliary_subrepresentation_le_iSup_of_isSimpleModule
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (S : Subrepresentation (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n))
    [FiniteDimensional k S.toSubmodule]
    (hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (Subrepresentation.asSubmodule S)) :
    S.toSubmodule ≤ ⨆ lam, LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k) := by
  obtain ⟨lam, ι, hι_equiv, hrange⟩ :=
    auxiliary_exists_range_eq_of_isSimpleModule n k S hSsimple
  rw [← hrange]
  exact (RepresentationTheory.GeneralLinearGroup.TensorLocalization.range_le_tensorToLocalization_range_of_equivariant n lam k ι hι_equiv).trans
    (le_iSup (fun lam => LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k)) lam)

/-- The indicated auxiliary submodule lies below the supremum of the component ranges. -/
theorem auxiliary_submodule_le_iSup
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (φ : Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) :
    RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ ≤
      ⨆ lam, LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k) := by
  classical
  set T : Submodule k (Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n)) :=
    ⨆ lam, LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k) with hT

  have hT_stable : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k),
      ∀ x ∈ T, RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g ((RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n).asModuleEquiv x) ∈ T := by
    intro g x hx
    exact auxiliary_iSupRange_mem_action n k g x hx
  set T_KG : Submodule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n).asModule :=
    RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.invariantSubmodule (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) T hT_stable with hTKG
  have hTKG_restrict : T_KG.restrictScalars k = T := by
    apply SetLike.ext; intro x
    rw [Submodule.restrictScalars_mem, hTKG, RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary.mem_invariantSubmodule_iff]

  set H : Subrepresentation (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) := RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.subrepresentation φ with hH
  haveI hfin : FiniteDimensional k (RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ) :=
    RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.finiteDimensional φ
  haveI hss := RepresentationTheory.Auxiliary.GeneralLinearPolynomialSubrepresentations.auxiliarySubrepresentation_isSemisimple k φ

  have hsub : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (x : H.toSubmodule),
      H.toSubmodule.subtype (H.toRepresentation g x)
        = RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n g (H.toSubmodule.subtype x) :=
    fun g x => LinearMap.coe_restrict_apply (H.apply_mem_toSubmodule g) x
  set incl :
      Representation.asModule H.toRepresentation →ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)] Representation.asModule (RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction.generalLinearGroupLocalizationRepresentation k n) :=
    RepresentationTheory.AsModuleEquivalences.linearMapAsModule H.toSubmodule.subtype hsub with hincl
  have hincl_apply : ∀ x, incl x = H.toSubmodule.subtype x := fun x => rfl

  have hrange_restrict : (LinearMap.range incl).restrictScalars k
      = RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ := by
    have hset : (LinearMap.range incl).restrictScalars k
        = LinearMap.range H.toSubmodule.subtype := by
      apply SetLike.ext; intro x
      rw [Submodule.restrictScalars_mem, LinearMap.mem_range, LinearMap.mem_range]
      constructor
      · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩
      · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩
    rw [hset, Submodule.range_subtype]; rfl

  have hbound : ∀ p ∈ {m : Submodule (MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin n) k)) (Representation.asModule H.toRepresentation) |
      IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) m},
      Submodule.map incl p ≤ T_KG := by
    intro p hp

    have hincl_inj : Function.Injective incl := by
      intro a b hab
      apply Subtype.coe_injective
      have : H.toSubmodule.subtype a = H.toSubmodule.subtype b := by
        rw [← hincl_apply, ← hincl_apply, hab]
      simpa using this

    have hSsimple : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
        (Subrepresentation.asSubmodule
          (Subrepresentation.ofSubmodule' (Submodule.map incl p))) :=
      (LinearEquiv.isSimpleModule_iff (Submodule.equivMapOfInjective incl hincl_inj p)).mp hp
    have hSsub : (Subrepresentation.ofSubmodule' (Submodule.map incl p)).toSubmodule
        ≤ RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ := by
      rw [← hrange_restrict]
      intro y hy
      rw [Submodule.restrictScalars_mem]
      exact (LinearMap.map_le_range (f := incl) (p := p)) hy
    haveI : FiniteDimensional k
        (Subrepresentation.ofSubmodule' (Submodule.map incl p)).toSubmodule :=
      Submodule.finiteDimensional_of_le hSsub
    have hreal := auxiliary_subrepresentation_le_iSup_of_isSimpleModule n k
      (Subrepresentation.ofSubmodule' (Submodule.map incl p)) hSsimple
    intro y hy
    exact hreal ((Subrepresentation.mem_ofSubmodule'_iff).mpr hy)

  have hrange_le : LinearMap.range incl ≤ T_KG := by
    rw [← Submodule.map_top,
      ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)) (Representation.asModule H.toRepresentation),
      sSup_eq_iSup, Submodule.map_iSup]
    refine iSup_le fun p => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hp => hbound p hp
  calc RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary φ
      = (LinearMap.range incl).restrictScalars k := hrange_restrict.symm
    _ ≤ T_KG.restrictScalars k := Submodule.restrictScalars_mono (S := k) hrange_le
    _ = T := hTKG_restrict

/-- The supremum of the auxiliary map ranges is the whole target. -/
theorem auxiliary_iSup_range_eq_top
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    ⨆ lam, LinearMap.range (RepresentationTheory.GeneralLinearGroup.TensorLocalization.tensorToLocalization n lam k) = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  exact auxiliary_submodule_le_iSup n k φ
    (RepresentationTheory.GeneralLinearGroup.Localization.Auxiliary.self_mem φ)

/-- The auxiliary direct-sum map is surjective. -/
theorem auxiliaryDirectSumMap_surjective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Function.Surjective (auxiliaryDirectSumMap n k) := by
  rw [← LinearMap.range_eq_top]
  unfold auxiliaryDirectSumMap
  rw [directSumToModule_range]
  exact auxiliary_iSup_range_eq_top n k

/-- The auxiliary direct-sum map is bijective. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.23.2" (role := primary)]
theorem auxiliaryDirectSumMap_bijective (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Function.Bijective (auxiliaryDirectSumMap n k) :=
  ⟨auxiliaryDirectSumMap_injective n k, auxiliaryDirectSumMap_surjective n k⟩

/-- The displayed representations and linear equivalence satisfy the indicated auxiliary predicate. -/
@[source_ref "Chapter5/Theorem5.23.2" (role := primary)]
theorem auxiliary_nonempty_representationRelation
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    Nonempty { e : Localization.Away (RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization.auxiliary_matrix_polynomial k n) ≃ₗ[k]
        (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
          (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) //
      Auxiliary.IsRepresentationRelation (RepresentationTheory.LinearAlgebra.Matrix.LocalizationActions.matrixLocalizationProductRepresentation k n) (auxiliaryTensorDirectSumRepresentation n k) e } :=


  auxiliary_nonempty_representationRelation_of_bijective n k (auxiliaryDirectSumMap_bijective n k)

end RepresentationTheory.AuxiliaryEquivariantDecomposition

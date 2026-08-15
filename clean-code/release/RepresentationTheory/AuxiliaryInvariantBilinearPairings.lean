/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.DualContraction
import RepresentationTheory.CharacterTwistIntertwiners

open scoped TensorProduct

noncomputable section

namespace RepresentationTheory.AuxiliaryInvariantBilinearPairings

section AbstractPerfect

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A nonzero invariant bilinear pairing has trivial left kernel when its left representation is simple. -/
theorem left_nondegenerate_of_simple_of_invariant
    (ρV : Representation k G V) (ρW : Representation k G W)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρV.asModule)
    (B : V →ₗ[k] W →ₗ[k] k) (hBne : B ≠ 0)
    (hinv : ∀ g v w, B (ρV g v) (ρW g w) = B v w) :
    ∀ v, (∀ w, B v w = 0) → v = 0 := by
  have hRinv : LinearMap.ker B ∈ ρV.invtSubmodule := by
    rw [ρV.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext w
    simp only [LinearMap.zero_apply]
    have hgg : ρW g (ρW g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h1 : B (ρV g x) w = B (ρV g x) (ρW g (ρW g⁻¹ w)) := by rw [hgg]
    rw [h1, hinv g x (ρW g⁻¹ w), hx]
    simp
  haveI := hV
  haveI hSO : IsSimpleOrder ρV.invtSubmodule :=
    (Representation.mapSubmodule ρV).isSimpleOrder_iff.mpr hV.toIsSimpleOrder
  have hker : LinearMap.ker B = ⊥ := by
    rcases hSO.eq_bot_or_eq_top ⟨LinearMap.ker B, hRinv⟩ with h | h
    · simpa using congrArg Subtype.val h
    · exact absurd (LinearMap.ker_eq_top.mp (by simpa using congrArg Subtype.val h)) hBne
  intro v hv
  have hv' : v ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker]; ext w; exact hv w
  rw [hker, Submodule.mem_bot] at hv'
  exact hv'

/-- A nonzero invariant bilinear pairing has trivial left and right kernels when both representations are simple. -/
theorem nondegenerate_of_simple_of_invariant
    (ρV : Representation k G V) (ρW : Representation k G W)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρV.asModule)
    (hW : IsSimpleModule (MonoidAlgebra k G) ρW.asModule)
    (B : V →ₗ[k] W →ₗ[k] k) (hBne : B ≠ 0)
    (hinv : ∀ g v w, B (ρV g v) (ρW g w) = B v w) :
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ w, (∀ v, B v w = 0) → w = 0) := by
  refine ⟨left_nondegenerate_of_simple_of_invariant ρV ρW hV B hBne hinv, ?_⟩
  have hflipne : B.flip ≠ 0 := fun h => hBne (by rw [← LinearMap.flip_flip B, h]; rfl)
  have hflipinv : ∀ g w v, B.flip (ρW g w) (ρV g v) = B.flip w v := by
    intro g w v; simp only [LinearMap.flip_apply]; exact hinv g v w
  exact left_nondegenerate_of_simple_of_invariant ρW ρV hW B.flip hflipne hflipinv

end AbstractPerfect

variable (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (k : Type)
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Defines an auxiliary linear equivalence from the first displayed module to the dual of the second. -/
noncomputable def auxiliaryLinearEquivToDual :
    RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ≃ₗ[k]
      Module.Dual k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :=
  (Classical.choice
    (RepresentationTheory.CharacterTwistIntertwiners.exists_intertwiner_to_dual_representation
      n lam k)).1

/-- The auxiliary equivalence sends the result of the first displayed group map to the result of the corresponding dual representation map. -/
theorem auxiliaryLinearEquivToDual_apply_groupMap
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) :
    auxiliaryLinearEquivToDual n lam k
        (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
          n lam k g v)
      = (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
          n lam k).dual g (auxiliaryLinearEquivToDual n lam k v) :=
  (Classical.choice
    (RepresentationTheory.CharacterTwistIntertwiners.exists_intertwiner_to_dual_representation
      n lam k)).2 g v

/-- Defines an auxiliary linear functional from the tensor product of the two displayed modules to the base field. -/
noncomputable def auxiliaryTensorPairing :
    RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k]
      RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k] k :=
  contractLeft k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) ∘ₗ
    TensorProduct.map (auxiliaryLinearEquivToDual n lam k).toLinearMap LinearMap.id

/-- Evaluating the auxiliary tensor pairing on a pure tensor agrees with left contraction after applying the auxiliary equivalence to the dual. -/
@[simp] theorem auxiliaryTensorPairing_eq_contractLeft
    (u : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k)
    (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    auxiliaryTensorPairing n lam k (u ⊗ₜ[k] v)
      = contractLeft k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
        (auxiliaryLinearEquivToDual n lam k u ⊗ₜ[k] v) := by
  simp [auxiliaryTensorPairing]

/-- The auxiliary tensor pairing is unchanged after applying the two displayed maps associated with a general linear group element. -/
theorem auxiliaryTensorPairing_apply_groupMaps (g : Matrix.GeneralLinearGroup (Fin n) k)
    (u : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k)
    (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :
    auxiliaryTensorPairing n lam k
        (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
            n lam k g u ⊗ₜ[k]
          RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
            n lam k g v)
      = auxiliaryTensorPairing n lam k (u ⊗ₜ[k] v) := by
  rw [auxiliaryTensorPairing_eq_contractLeft, auxiliaryTensorPairing_eq_contractLeft,
    auxiliaryLinearEquivToDual_apply_groupMap]
  exact RepresentationTheory.DualContraction.contractLeft_dual_action_tmul_action
    (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
      n lam k) g
    (auxiliaryLinearEquivToDual n lam k u) v

/-- The auxiliary tensor pairing is nonzero when the displayed second module is nontrivial. -/
theorem auxiliaryTensorPairing_ne_zero
    [Nontrivial (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)] :
    auxiliaryTensorPairing n lam k ≠ 0 := by
  intro h
  have hsurj : Function.Surjective
      (TensorProduct.map (auxiliaryLinearEquivToDual n lam k).toLinearMap
        (LinearMap.id :
          RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k]
            RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) := by
    have : TensorProduct.map (auxiliaryLinearEquivToDual n lam k).toLinearMap
        (LinearMap.id :
          RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k →ₗ[k]
            RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
        = (TensorProduct.congr (auxiliaryLinearEquivToDual n lam k)
            (LinearEquiv.refl k
              (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k))).toLinearMap := by
      rw [TensorProduct.toLinearMap_congr]; rfl
    rw [this]
    exact (TensorProduct.congr (auxiliaryLinearEquivToDual n lam k)
      (LinearEquiv.refl k
        (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k))).surjective
  refine RepresentationTheory.DualContraction.contractLeft_ne_zero
    (k := k) (V := RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) ?_
  refine LinearMap.ext fun t => ?_
  obtain ⟨s, rfl⟩ := hsurj t
  have := congrArg (fun (m : _ →ₗ[k] k) => m s) h
  simpa [auxiliaryTensorPairing, LinearMap.comp_apply, LinearMap.zero_apply] using this

/-- Under the two displayed weight-sum bounds, the auxiliary tensor pairing has trivial left and right kernels over the complex numbers. -/
theorem auxiliaryTensorPairing_nondegenerate
    (hN : (∑ i, lam.toNatAt i) ≤ n)
    (hN' : (∑ i, (lam.auxiliaryMap).toNatAt i) ≤ n) :
    (∀ u, (∀ v, auxiliaryTensorPairing n lam ℂ (u ⊗ₜ[ℂ] v) = 0) → u = 0) ∧
    (∀ v, (∀ u, auxiliaryTensorPairing n lam ℂ (u ⊗ₜ[ℂ] v) = 0) → v = 0) := by
  haveI hWsimple : IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
        n lam ℂ).asModule :=
    RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.isSimpleModule_auxiliaryGeneralLinearFDRep_of_weightSum_le
      n lam hN
  haveI hVsimple : IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
        n lam ℂ).asModule :=
    RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.isSimpleModule_auxiliaryGeneralLinearFDRep_of_weightSum_le
      n lam.auxiliaryMap hN'
  haveI : Nontrivial (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam ℂ) := by
    have hnt : Nontrivial
        (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
          n lam ℂ).asModule :=
      (Submodule.nontrivial_iff (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))).mp
        hWsimple.toNontrivial
    exact hnt
  set B := TensorProduct.curry (auxiliaryTensorPairing n lam ℂ) with hB
  have hBapp : ∀ u v, B u v = auxiliaryTensorPairing n lam ℂ (u ⊗ₜ[ℂ] v) := fun u v => rfl
  have hBne : B ≠ 0 := by
    intro h0
    refine auxiliaryTensorPairing_ne_zero n lam ℂ ?_
    apply TensorProduct.ext'
    intro u v
    rw [LinearMap.zero_apply, ← hBapp, h0]
    rfl
  have hBinv : ∀ g u v,
      B (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
          n lam ℂ g u)
        (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
          n lam ℂ g v)
      = B u v := by
    intro g u v
    rw [hBapp, hBapp]
    exact auxiliaryTensorPairing_apply_groupMaps n lam ℂ g u v
  have := nondegenerate_of_simple_of_invariant
    (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
      n lam ℂ)
    (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
      n lam ℂ)
    hVsimple hWsimple B hBne hBinv
  simpa only [hBapp] using this

end RepresentationTheory.AuxiliaryInvariantBilinearPairings

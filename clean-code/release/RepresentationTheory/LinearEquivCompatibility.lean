/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
import RepresentationTheory.GeneralLinearGroup.ExteriorPower

/-!
# Compatibility of linear equivalences with representations

Elementary compatibility operations for linear equivalences, together with an iterated
general-linear-group representation construction.
-/

noncomputable section

namespace RepresentationTheory.LinearEquivCompatibility

open RepresentationTheory.AuxiliaryModuleData
open RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
open RepresentationTheory.GeneralLinearGroup.ExteriorPower
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter

section Helpers

universe u

variable {k : Type u} [Field k] {G : Type u} [Monoid G]
  {V₁ V₂ V₃ : Type u}
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃]

/-- A predicate on two representations and a linear equivalence between their carrier spaces. -/
@[reducible] def RepresentationLinearEquiv.IsCompatible
    (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂)
    (e : V₁ ≃ₗ[k] V₂) : Prop :=
  ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v)

/-- Two successive compatible linear equivalences have a compatible composite. -/
theorem RepresentationLinearEquiv.IsCompatible.trans
    {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {ρ₃ : Representation k G V₃} {e : V₁ ≃ₗ[k] V₂} {f : V₂ ≃ₗ[k] V₃}
    (he : RepresentationLinearEquiv.IsCompatible ρ₁ ρ₂ e)
    (hf : RepresentationLinearEquiv.IsCompatible ρ₂ ρ₃ f) :
    RepresentationLinearEquiv.IsCompatible ρ₁ ρ₃ (e.trans f) := by
  intro g v
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he g v, hf g (e v)]

/-- Compatibility in the reverse direction holds for the inverse linear equivalence. -/
theorem RepresentationLinearEquiv.IsCompatible.symm
    {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {e : V₁ ≃ₗ[k] V₂} (he : RepresentationLinearEquiv.IsCompatible ρ₁ ρ₂ e) :
    RepresentationLinearEquiv.IsCompatible ρ₂ ρ₁ e.symm := by
  intro g w
  apply e.injective
  rw [e.apply_symm_apply, he g (e.symm w), e.apply_symm_apply]

/-- The compatibility predicate is preserved after applying the same scalar-valued monoid homomorphism transformation to both representations. -/
theorem RepresentationLinearEquiv.IsCompatible.map_both
    (c : G →* kˣ) {ρ₁ : Representation k G V₁}
    {ρ₂ : Representation k G V₂} {e : V₁ ≃ₗ[k] V₂}
    (he : RepresentationLinearEquiv.IsCompatible ρ₁ ρ₂ e) :
    RepresentationLinearEquiv.IsCompatible
      (twistByCharacter c ρ₁) (twistByCharacter c ρ₂) e := by
  intro g v
  simp only [twistByCharacter_apply, map_smul, he g v]

/-- The linear equivalence underlying an isomorphism of finite-dimensional representations satisfies the compatibility predicate. -/
theorem isCompatible_isoToLinearEquiv
    [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂)
    (f : FDRep.of ρ₁ ≅ FDRep.of ρ₂) :
    RepresentationLinearEquiv.IsCompatible ρ₁ ρ₂ (FDRep.isoToLinearEquiv f) := by
  intro g v
  have h := FDRep.Iso.conj_ρ f g
  change (FDRep.isoToLinearEquiv f) ((FDRep.of ρ₁).ρ g v)
    = (FDRep.of ρ₂).ρ g ((FDRep.isoToLinearEquiv f) v)
  have hconj : (FDRep.isoToLinearEquiv f).conj ((FDRep.of ρ₁).ρ g)
        ((FDRep.isoToLinearEquiv f) v)
      = (FDRep.isoToLinearEquiv f) ((FDRep.of ρ₁).ρ g v) := by
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change (FDRep.isoToLinearEquiv f)
        (((FDRep.of ρ₁).ρ g) ((FDRep.isoToLinearEquiv f).symm ((FDRep.isoToLinearEquiv f) v)))
      = (FDRep.isoToLinearEquiv f) (((FDRep.of ρ₁).ρ g) v)
    rw [(FDRep.isoToLinearEquiv f).symm_apply_apply]
  rw [h, hconj]

/-- The representation transformation associated with the unit monoid homomorphism fixes every representation. -/
theorem representationTransform_one (ρ : Representation k G V₁) :
    twistByCharacter (1 : G →* kˣ) ρ = ρ := by
  ext g v
  simp only [twistByCharacter_apply, MonoidHom.one_apply, Units.val_one, one_smul]

end Helpers

/-- For an antitone map from a finite type to natural numbers and each natural parameter, the displayed subtype of compatible linear equivalences is nonempty. -/
theorem exists_compatible_linearEquiv_of_antitone
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (μ : Fin n → ℕ) (hμ : Antitone μ) (t : ℕ) :
    Nonempty
      { e : schurSubmodule k n μ ≃ₗ[k] schurSubmodule k n (fun i => μ i + t) //
        RepresentationLinearEquiv.IsCompatible
          (twistByCharacter (generalLinearGroupToUnits k n ^ t)
            (schurSubmoduleRepresentation k n μ))
          (schurSubmoduleRepresentation k n (fun i => μ i + t)) e } := by
  induction t with
  | zero =>
    refine ⟨⟨LinearEquiv.refl k _, ?_⟩⟩
    intro g v
    change (twistByCharacter (generalLinearGroupToUnits k n ^ 0)
      (schurSubmoduleRepresentation k n μ) g v) = schurSubmoduleRepresentation k n μ g v
    rw [pow_zero, representationTransform_one]
  | succ t ih =>
    obtain ⟨e, he⟩ := ih
    have hμt : Antitone (fun i => μ i + t) :=
      fun i j hij => Nat.add_le_add_right (hμ hij) t
    obtain ⟨iso⟩ := shiftedAuxiliarySubtypeRepresentationIsoNonempty
      k n (fun i => μ i + t) hμt
    have hshift : RepresentationLinearEquiv.IsCompatible
        (schurSubmoduleRepresentation k n (fun i => μ i + (t + 1)))
        (twistByCharacter (generalLinearGroupToUnits k n)
          (schurSubmoduleRepresentation k n (fun i => μ i + t)))
        (FDRep.isoToLinearEquiv iso) := isCompatible_isoToLinearEquiv _ _ iso
    have he_tw : RepresentationLinearEquiv.IsCompatible
        (twistByCharacter (generalLinearGroupToUnits k n)
          (twistByCharacter (generalLinearGroupToUnits k n ^ t)
            (schurSubmoduleRepresentation k n μ)))
        (twistByCharacter (generalLinearGroupToUnits k n)
          (schurSubmoduleRepresentation k n (fun i => μ i + t))) e :=
      RepresentationLinearEquiv.IsCompatible.map_both (generalLinearGroupToUnits k n) he
    have hcomp := RepresentationLinearEquiv.IsCompatible.trans he_tw
      (RepresentationLinearEquiv.IsCompatible.symm hshift)
    have hsrc : twistByCharacter (generalLinearGroupToUnits k n)
        (twistByCharacter (generalLinearGroupToUnits k n ^ t)
          (schurSubmoduleRepresentation k n μ)) =
        twistByCharacter (generalLinearGroupToUnits k n ^ (t + 1))
          (schurSubmoduleRepresentation k n μ) := by
      rw [twistByCharacter_mul, ← pow_succ']
    rw [hsrc] at hcomp
    exact ⟨⟨e.trans (FDRep.isoToLinearEquiv iso).symm, hcomp⟩⟩

/-- For each natural parameter, the displayed subtype contains a map carrying one general linear group action to the other pointwise. -/
theorem exists_action_compatible_map
    (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : ℕ) :
    Nonempty
      { e : auxiliaryGeneralLinearFDRepAlt n lam k ≃ₗ[k]
            schurSubmodule k n (fun i => lam.auxiliaryMap.toNatAt i + t) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k)
          (v : auxiliaryGeneralLinearFDRepAlt n lam k),
          e (twistByCharacter
                (generalLinearGroupToUnits k n ^ (t + lam.auxiliaryMap.toNat))
                (generalLinearRepresentationOnAuxiliarySpace n lam k) g v)
            = schurSubmoduleRepresentation k n (fun i => lam.auxiliaryMap.toNatAt i + t)
                g (e v) } := by
  obtain ⟨e, he⟩ := exists_compatible_linearEquiv_of_antitone
    k n lam.auxiliaryMap.toNatAt lam.auxiliaryMap.toNatWeight_antitone t
  have hchar : generalLinearGroupToUnits k n ^ (t + lam.auxiliaryMap.toNat)
        * generalLinearGroupToUnits k n ^ (-(lam.auxiliaryMap.toNat : ℤ)) =
      generalLinearGroupToUnits k n ^ t := by
    rw [← zpow_natCast (generalLinearGroupToUnits k n) (t + lam.auxiliaryMap.toNat),
        ← zpow_add, ← zpow_natCast (generalLinearGroupToUnits k n) t]
    congr 1
    push_cast
    ring
  have hrep : twistByCharacter
        (generalLinearGroupToUnits k n ^ (t + lam.auxiliaryMap.toNat))
        (generalLinearRepresentationOnAuxiliarySpace n lam k) =
      twistByCharacter (generalLinearGroupToUnits k n ^ t)
        (schurSubmoduleRepresentation k n lam.auxiliaryMap.toNatAt) := by
    change twistByCharacter
        (generalLinearGroupToUnits k n ^ (t + lam.auxiliaryMap.toNat))
        (twistByCharacter (generalLinearGroupToUnits k n ^ (-(lam.auxiliaryMap.toNat : ℤ)))
          (schurSubmoduleRepresentation k n lam.auxiliaryMap.toNatAt)) = _
    rw [twistByCharacter_mul, hchar]
  refine ⟨e, ?_⟩
  intro g v
  rw [hrep]
  exact he g v

end RepresentationTheory.LinearEquivCompatibility

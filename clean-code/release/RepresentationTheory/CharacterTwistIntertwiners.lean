/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
import RepresentationTheory.LinearEquivCompatibility
import RepresentationTheory.GeneralLinearGroup.WeightVectors

noncomputable section

namespace RepresentationTheory.CharacterTwistIntertwiners

open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open scoped TensorProduct

section Untwist

variable {k G W₁ W₂ : Type*} [Field k] [Monoid G]
  [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]

/-- A linear equivalence that intertwines two representations after twisting both by the same character also intertwines the original representations. -/
theorem intertwines_of_twisted_intertwines (c : G →* kˣ)
    (ρ₁ : Representation k G W₁) (ρ₂ : Representation k G W₂)
    (e : W₁ ≃ₗ[k] W₂)
    (he : ∀ (g : G) (v : W₁),
      e (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter
        c ρ₁ g v) =
        RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter
          c ρ₂ g (e v)) :
    ∀ (g : G) (v : W₁), e (ρ₁ g v) = ρ₂ g (e v) := by
  intro g v
  have h := he g v
  rw [RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply,
    RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply,
    map_smul] at h
  exact smul_right_injective W₂ (Units.ne_zero (c g)) h

end Untwist

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- There are a twist parameter and an index such that the displayed representation and the displayed dual representation, after twisting, admit intertwiners with the same indexed representation. -/
theorem exists_twists_intertwining_common_representation
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    ∃ (s : ℕ) (ν : Fin n → ℕ),
      Nonempty
        { e : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ≃ₗ[k]
            RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n ν //
          ∀ (g : Matrix.GeneralLinearGroup (Fin n) k)
            (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k),
            e (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter
                (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits
                  k n ^ s)
                (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
                  n lam k) g v) =
              RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
                k n ν g (e v) }
      ∧ Nonempty
        { e : Module.Dual k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) ≃ₗ[k]
            RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n ν //
          ∀ (g : Matrix.GeneralLinearGroup (Fin n) k)
            (v : Module.Dual k
              (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)),
            e (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter
                (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits
                  k n ^ s)
                ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
                  n lam k).dual) g v) =
              RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation
                k n ν g (e v) } := by
  have hnonneg : ∀ (lz : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
      (i : Fin n), 0 ≤ lz.val i + (lz.toNat : ℤ) := by
    intro lz i
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
    have hlast : lz.val (Fin.last m) ≤ lz.val i := lz.property (Fin.le_last i)
    change 0 ≤ lz.val i + (((-(lz.val (Fin.last m))).toNat : ℕ) : ℤ)
    omega
  have hcast : ∀ (lz : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (i : Fin n),
      (lz.toNatAt i : ℤ) = lz.val i + (lz.toNat : ℤ) := by
    intro lz i
    change (((lz.val i + (lz.toNat : ℤ)).toNat : ℕ) : ℤ) = lz.val i + (lz.toNat : ℤ)
    rw [Int.toNat_of_nonneg (hnonneg lz i)]
  have hs : ∀ i, lam.toNatAt i ≤ (lam.auxiliaryMap).toNat + lam.toNat := by
    intro i
    have h1 : (lam.toNatAt i : ℤ) = lam.val i + (lam.toNat : ℤ) := hcast lam i
    have h2 : 0 ≤ (lam.auxiliaryMap).val (Fin.rev i) + ((lam.auxiliaryMap).toNat : ℤ) :=
      hnonneg (lam.auxiliaryMap) (Fin.rev i)
    have h3 : (lam.auxiliaryMap).val (Fin.rev i) = -lam.val i := by
      change -lam.val (Fin.rev (Fin.rev i)) = -lam.val i
      rw [Fin.rev_rev]
    omega
  have hνeq :
      RepresentationTheory.Determinants.FiniteNatFamilyTransforms.finiteNatFamilyTransform
          n lam.toNatAt ((lam.auxiliaryMap).toNat + lam.toNat) =
        (lam.auxiliaryMap).toNatAt := by
    funext j
    have hA : (lam.toNatAt (Fin.rev j) : ℤ) = lam.val (Fin.rev j) + (lam.toNat : ℤ) :=
      hcast lam (Fin.rev j)
    have hB : ((lam.auxiliaryMap).toNatAt j : ℤ) =
        (lam.auxiliaryMap).val j + ((lam.auxiliaryMap).toNat : ℤ) :=
      hcast (lam.auxiliaryMap) j
    have hw0 : (lam.auxiliaryMap).val j = -lam.val (Fin.rev j) := rfl
    change ((lam.auxiliaryMap).toNat + lam.toNat) - lam.toNatAt (Fin.rev j) =
      (lam.auxiliaryMap).toNatAt j
    omega
  refine ⟨(lam.auxiliaryMap).toNat, (lam.auxiliaryMap).toNatAt, ?_, ?_⟩
  · rw [show (lam.auxiliaryMap).toNat = 0 + (lam.auxiliaryMap).toNat from
      (Nat.zero_add _).symm]
    exact RepresentationTheory.LinearEquivCompatibility.exists_action_compatible_map n lam k 0
  · rw [← hνeq]
    exact
      RepresentationTheory.GeneralLinearGroup.WeightVectors.nonempty_intertwining_map_from_transformed_dual
        n lam k (lam.auxiliaryMap).toNat hs

/-- There is a common character twist for which the displayed representation admits an intertwiner with the correspondingly twisted dual representation. -/
theorem exists_twist_intertwiner_to_dual_representation
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    ∃ s : ℕ, Nonempty
      { e : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ≃ₗ[k]
          Module.Dual k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k)
          (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k),
          e (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter
              (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits
                k n ^ s)
              (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
                n lam k) g v) =
            RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter
              (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits
                k n ^ s)
              ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
                n lam k).dual) g (e v) } := by
  obtain ⟨s, ν, ⟨eA, heA⟩, ⟨eB, heB⟩⟩ :=
    exists_twists_intertwining_common_representation n lam k
  refine ⟨s, ⟨eA.trans eB.symm, ?_⟩⟩
  intro g v
  apply eB.injective
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, eB.apply_symm_apply,
    heA g v, heB g (eB.symm (eA v)), eB.apply_symm_apply]

/-- There exists a map intertwining the displayed general linear group representation with the displayed dual representation. -/
theorem exists_intertwiner_to_dual_representation
    (n : ℕ) (lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (k : Type)
    [Field k] [IsAlgClosed k] [CharZero k] :
    Nonempty
      { e : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ≃ₗ[k]
          Module.Dual k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) //
        ∀ (g : Matrix.GeneralLinearGroup (Fin n) k)
          (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k),
          e (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
            n lam k g v) =
            (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
              n lam k).dual g (e v) } := by
  obtain ⟨s, ⟨e, he⟩⟩ := exists_twist_intertwiner_to_dual_representation n lam k
  exact ⟨⟨e, intertwines_of_twisted_intertwines
    (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits
      k n ^ s)
    (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpace
      n lam k)
    ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
      n lam k).dual) e he⟩⟩

end RepresentationTheory.CharacterTwistIntertwiners

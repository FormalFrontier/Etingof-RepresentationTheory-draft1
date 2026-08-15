/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations
import RepresentationTheory.GeneralLinearGroup.ExteriorPower
import RepresentationTheory.AuxiliaryCharacter
import RepresentationTheory.AsModuleEquivalences
import RepresentationTheory.GeneralLinearGroup.PolynomialTransforms
import RepresentationTheory.MvPolynomial.UniformIndexShift
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.Alignment.Attribute

set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

noncomputable section

namespace RepresentationTheory.AuxiliaryRepresentationParameters

open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

private theorem finrank_submodule_congr' {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {S T : Submodule K W} (h : S = T) : Module.finrank K S = Module.finrank K T :=
  congrArg (fun U : Submodule K W => Module.finrank K U) h

/-- For an antitone natural-valued function, the first displayed auxiliary construction applied to the finite-dimensional representation equals the second displayed auxiliary construction applied after pointwise addition by the given natural number. -/
theorem auxiliary_identity_of_antitone (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (n : ℕ) (w : Fin n → ℕ) (hw : Antitone w) (p : ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k n
        (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ (p : ℤ)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w)))
      = RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial n (fun i => w i + p) := by
  induction p with
  | zero =>
    have hct : twistByCharacter (generalLinearGroupToUnits k n ^ (0 : ℤ)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w)
        = RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w := by
      ext g v; simp [twistByCharacter_apply]
    rw [Nat.cast_zero, hct]
    have hw0 : (fun i => w i + 0) = w := by funext i; omega
    rw [hw0]
    exact RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation_weightCharacter k n w hw
  | succ p ih =>
    have hshift : ∀ ν : Fin n → ℕ,
        Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k n
            (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ ((p + 1 : ℕ) : ℤ)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w)))
            (fun i => ν i + 1))
          = Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k n
            (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ ((p : ℕ) : ℤ)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w))) ν) := by
      intro ν
      refine finrank_submodule_congr' ?_
      rw [RepresentationTheory.AuxiliaryWeightSpaces.Duality.natAuxiliaryWeightSpace_eq_intAuxiliaryWeightSpace k n _ (fun i => ν i + 1),
          RepresentationTheory.AuxiliaryWeightSpaces.Duality.natAuxiliaryWeightSpace_eq_intAuxiliaryWeightSpace k n _ ν]
      simp only [FDRep.of_ρ']
      rw [RepresentationTheory.GeneralLinearGroup.PolynomialTransforms.indexed_family_transformed_representation_eq_shift (generalLinearGroupToUnits k n ^ ((p + 1 : ℕ) : ℤ))
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w) (fun _ => ((p + 1 : ℕ) : ℤ))
            (fun i t => RepresentationTheory.GeneralLinearGroup.PolynomialTransforms.pow_apply_indexed_element_eq_pow k n _ i t) (fun i => ((ν i + 1 : ℕ) : ℤ)),
          RepresentationTheory.GeneralLinearGroup.PolynomialTransforms.indexed_family_transformed_representation_eq_shift (generalLinearGroupToUnits k n ^ ((p : ℕ) : ℤ))
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w) (fun _ => ((p : ℕ) : ℤ))
            (fun i t => RepresentationTheory.GeneralLinearGroup.PolynomialTransforms.pow_apply_indexed_element_eq_pow k n _ i t) (fun i => ((ν i : ℕ) : ℤ))]
      have hAB : (fun i => ((ν i + 1 : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ))
          = (fun i => ((ν i : ℕ) : ℤ) - ((p : ℕ) : ℤ)) := by
        funext i; push_cast; ring
      simp only [hAB]
    have hvanish : ∀ μ : Fin n → ℕ, (∃ i, μ i = 0) →
        Module.finrank k (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k n
          (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ ((p + 1 : ℕ) : ℤ)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w)))
          μ) = 0 := by
      rintro μ ⟨i₀, hi₀⟩
      have hsub : RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k n
            (FDRep.of (twistByCharacter (generalLinearGroupToUnits k n ^ ((p + 1 : ℕ) : ℤ)) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w))) μ
          = integerTupleSubmodule k n (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w)
              (fun i => ((μ i : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ)) := by
        rw [RepresentationTheory.AuxiliaryWeightSpaces.Duality.natAuxiliaryWeightSpace_eq_intAuxiliaryWeightSpace k n _ μ]
        simp only [FDRep.of_ρ']
        rw [RepresentationTheory.GeneralLinearGroup.PolynomialTransforms.indexed_family_transformed_representation_eq_shift (generalLinearGroupToUnits k n ^ ((p + 1 : ℕ) : ℤ))
              (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n w) (fun _ => ((p + 1 : ℕ) : ℤ))
              (fun i t => RepresentationTheory.GeneralLinearGroup.PolynomialTransforms.pow_apply_indexed_element_eq_pow k n _ i t) (fun i => ((μ i : ℕ) : ℤ))]
      rw [finrank_submodule_congr' hsub]
      refine RepresentationTheory.GeneralLinearGroup.PolynomialTransforms.finrank_subtype_eq_zero_of_neg_coordinate k n w
        (fun i => ((μ i : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ)) i₀ ?_
      rw [hi₀]; push_cast; omega
    have hidx : (fun i => w i + (p + 1)) = (fun i => (w i + p) + 1) := by funext i; omega
    have hsp : RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial n (fun i => w i + (p + 1))
        = (∏ i : Fin n, MvPolynomial.X i) * RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial n (fun i => w i + p) := by
      rw [hidx, RepresentationTheory.MvPolynomial.UniformIndexShift.auxiliary_eq_prod_variables_mul]
    rw [RepresentationTheory.AuxiliaryCharacter.auxiliaryPolynomial_eq_product_X_mul_of_weightSpaceShift k n _ _ hshift hvanish, ih, hsp]

private theorem dominantWeight_shift_nonneg {n : ℕ} (lz : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (i : Fin n) :
    0 ≤ lz.val i + (lz.toNat : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  have hlast : lz.val (Fin.last m) ≤ lz.val i := lz.property (Fin.le_last i)
  change 0 ≤ lz.val i + (((-(lz.val (Fin.last m))).toNat : ℕ) : ℤ)
  omega

private theorem dominantWeight_toNatWeight_cast {n : ℕ} (lz : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) (i : Fin n) :
    (lz.toNatAt i : ℤ) = lz.val i + (lz.toNat : ℤ) := by
  change (((lz.val i + (lz.toNat : ℤ)).toNat : ℕ) : ℤ) = lz.val i + (lz.toNat : ℤ)
  rw [Int.toNat_of_nonneg (dominantWeight_shift_nonneg lz i)]

/-- Displayed auxiliary representation modules with distinct parameters are not linearly equivalent. -/
theorem auxiliaryRepresentation_not_linearEquiv_of_parameters_ne (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n} (hne : lam ≠ mu) :
    ¬ Nonempty ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModule ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)] (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k).asModule) := by
  rintro ⟨e⟩
  apply hne
  set f : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k ≃ₗ[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n mu k :=
    (((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModuleEquiv).symm.trans (e.restrictScalars k)).trans
      ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k).asModuleEquiv) with hf
  have hf_int : ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      f (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k g v) = RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k g (f v) := by
    intro g v
    simp only [hf, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      Representation.asModuleEquiv_symm_map_rho, map_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  have hf_twist : ∀ (c : Matrix.GeneralLinearGroup (Fin n) k →* kˣ)
      (g : Matrix.GeneralLinearGroup (Fin n) k) (v : RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k),
      f (twistByCharacter c (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k) g v)
        = twistByCharacter c (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k) g (f v) := by
    intro c g v
    rw [twistByCharacter_apply, map_smul, hf_int, twistByCharacter_apply]
  have hclear : ∀ (lz : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n), lz.toNat ≤ lam.toNat + mu.toNat →
      twistByCharacter (generalLinearGroupToUnits k n ^ ((lam.toNat + mu.toNat : ℕ) : ℤ)) (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lz k)
        = twistByCharacter (generalLinearGroupToUnits k n ^ (((lam.toNat + mu.toNat) - lz.toNat : ℕ) : ℤ))
            (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmoduleRepresentation k n lz.toNatAt) := by
    intro lz hle
    unfold RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt
    rw [twistByCharacter_mul, ← zpow_add]
    congr 2
    omega
  have hchar := RepresentationTheory.AuxiliaryCharacter.auxiliaryPolynomial_eq_of_linearEquiv k n
    (twistByCharacter (generalLinearGroupToUnits k n ^ ((lam.toNat + mu.toNat : ℕ) : ℤ)) (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k))
    (twistByCharacter (generalLinearGroupToUnits k n ^ ((lam.toNat + mu.toNat : ℕ) : ℤ)) (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k))
    f (hf_twist _)
  rw [hclear lam (by omega), hclear mu (by omega),
      auxiliary_identity_of_antitone k n lam.toNatAt lam.toNatWeight_antitone _,
      auxiliary_identity_of_antitone k n mu.toNatAt mu.toNatWeight_antitone _] at hchar
  have hweq := RepresentationTheory.AuxiliaryCharacter.antitone_eq_of_auxiliaryPolynomial_eq n _ _
    (fun i j hij => Nat.add_le_add_right (lam.toNatWeight_antitone hij) _)
    (fun i j hij => Nat.add_le_add_right (mu.toNatWeight_antitone hij) _) hchar
  apply Subtype.ext
  funext i
  have hi := congrFun hweq i
  have hcl := dominantWeight_toNatWeight_cast lam i
  have hcm := dominantWeight_toNatWeight_cast mu i
  have : (lam.toNatAt i : ℤ) + ((lam.toNat + mu.toNat) - lam.toNat : ℕ)
      = (mu.toNatAt i : ℤ) + ((lam.toNat + mu.toNat) - mu.toNat : ℕ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hi
  omega

/-- Two displayed auxiliary representation modules are linearly equivalent exactly when their parameters are equal. -/
@[source_ref "Chapter5/Discussion_after_Definition5.23.1" (role := primary),
  source_ref "Chapter5/Discussion_after_Definition5.23.1/Derived01" (role := supporting)]
theorem auxiliaryRepresentation_linearEquiv_iff_parameters_eq (n : ℕ) (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] {lam mu : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n} :
    Nonempty ((RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n lam k).asModule ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin n) k)] (RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.generalLinearRepresentationOnAuxiliarySpaceAlt n mu k).asModule) ↔
      lam = mu := by
  constructor
  · intro h
    by_contra hne
    exact auxiliaryRepresentation_not_linearEquiv_of_parameters_ne n k hne h
  · rintro rfl
    exact ⟨LinearEquiv.refl _ _⟩

end RepresentationTheory.AuxiliaryRepresentationParameters

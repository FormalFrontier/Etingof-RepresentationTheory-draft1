/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.AuxiliaryModuleData
import RepresentationTheory.GeneralLinearGroup.AuxiliaryDecomposition
import RepresentationTheory.GeneralLinearGroup.CoordinatePolynomials
import RepresentationTheory.GeneralLinear.AuxiliaryRepresentations

















open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace RepresentationTheory.AuxiliarySemisimpleDecomposition

open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]





























































/-- Establishes semisimplicity for the module associated with a representation under an auxiliary hypothesis. -/
@[source_ref "Chapter5/Theorem5.23.2" (role := supporting)]
theorem isSemisimpleModule_of_auxiliary
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ)
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    (halg : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty n ⇑ρ) :
    IsSemisimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule := by
  classical

  obtain ⟨s, hpoly⟩ := halg.exists_det_twist

  have hcoe : ⇑(RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s) ρ)
      = fun g => ((Matrix.GeneralLinearGroup.det g : k) ^ s) • ρ g := by
    funext g
    change ((RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s) g : k) • ρ g = _
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  have hpoly_tw : RepresentationTheory.GeneralLinearGroup.DiagonalAction.IsAuxiliaryEndomorphismFamily n ⇑(RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s) ρ) := by
    rw [hcoe]; exact hpoly

  have hss_tw : IsSemisimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k))
      (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s) ρ).asModule := by
    have h := RepresentationTheory.GeneralLinearGroup.AuxiliaryDecomposition.GeneralLinearGroup.AuxiliaryDecomposition.isSemisimpleModule_of_auxiliaryCondition k n
      (FDRep.of (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s) ρ))
      (by rw [FDRep.of_ρ']; exact hpoly_tw)
    rwa [FDRep.of_ρ'] at h

  have huntwist : RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s)⁻¹
      (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s) ρ) = ρ := by
    ext g v
    rw [RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter_apply, smul_smul, ← Units.val_mul,
      ← MonoidHom.mul_apply, inv_mul_cancel, MonoidHom.one_apply, Units.val_one, one_smul]
  have hfin := RepresentationTheory.GeneralLinear.AuxiliaryRepresentations.isSemisimpleModule_auxiliaryRepresentationConstruction (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s)⁻¹
    (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.twistByCharacter (RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation.generalLinearGroupToUnits k n ^ s) ρ) (hss := hss_tw)
  rwa [huntwist] at hfin




/-- An auxiliary family of types indexed by a natural number and a field. -/
noncomputable abbrev auxiliary (n : ℕ) (k : Type*) [Field k] :=
  MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k

































private theorem glCoordinateRing_rank (n : ℕ) :
    Module.rank k (auxiliary n k) = Cardinal.aleph0 := by
  haveI : Nonempty (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) := ⟨Sum.inr ()⟩
  haveI : Infinite (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n →₀ ℕ) :=
    @Finsupp.infinite_of_right (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) ℕ _ _ ⟨Sum.inr ()⟩
  have hcard : Cardinal.mk (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n →₀ ℕ) = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 _
  have hbasis := (MvPolynomial.basisMonomials (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex n) k).mk_eq_rank
  rw [hcard, Cardinal.lift_aleph0, Cardinal.lift_id'] at hbasis
  exact hbasis.symm



set_option maxHeartbeats 400000 in

private theorem directSum_rank_le_aleph0 (n : ℕ) :
    Module.rank k (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
      (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) ≤ Cardinal.aleph0 := by
  set F := fun lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n =>
    (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)
  rw [rank_directSum]

  have h_sup : ⨆ lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n, Module.rank k (F lam) ≤ Cardinal.aleph0 := by
    apply ciSup_le'
    intro lam
    haveI : Module.Finite k (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k) :=
      RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily.finite n lam.auxiliaryMap k
    haveI : Module.Finite k (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k) :=
      RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily.finite n lam k
    exact (Module.rank_lt_aleph0 k (F lam)).le
  calc Cardinal.sum (fun lam => Module.rank k (F lam))

      ≤ _ := Cardinal.sum_le_lift_mk_mul_iSup_lift _
    _ ≤ Cardinal.aleph0 * Cardinal.aleph0 := by
        apply mul_le_mul'
        · rw [Cardinal.lift_le_aleph0]; exact Cardinal.mk_le_aleph0

        · have hlift : (fun i => Cardinal.lift.{0} (Module.rank k (F i))) =
              fun lam => Module.rank k (F lam) := by
            funext lam; exact Cardinal.lift_id' _
          rw [hlift]; exact h_sup
    _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0


private def oneRowWeight (n : ℕ) (m : ℕ) (hn : 0 < n) : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n :=
  ⟨fun i => if i = ⟨0, hn⟩ then (m : ℤ) else 0, by
    intro i j hij
    by_cases hi : i = ⟨0, hn⟩ <;> by_cases hj : j = ⟨0, hn⟩ <;> simp [hi, hj]
    exfalso; apply hi; subst hj
    exact Fin.ext (show i.val = 0 by exact Nat.le_zero.mp hij)⟩

private theorem oneRowWeight_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (oneRowWeight n · hn) := by
  intro m₁ m₂ h
  have := congr_arg (fun w : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n => w.val ⟨0, hn⟩) h
  simp [oneRowWeight] at this
  exact_mod_cast this

private theorem oneRowWeight_shift (n : ℕ) (m : ℕ) (hn : 0 < n) :
    (oneRowWeight n m hn).toNat = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.toNat, oneRowWeight]

    split_ifs with h
    ·
      simp
    ·
      simp

private theorem oneRowWeight_toNatWeight (n : ℕ) (m : ℕ) (hn : 0 < n) :
    (oneRowWeight n m hn).toNatAt = fun i => if i = ⟨0, hn⟩ then m else 0 := by
  ext i
  simp only [RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.toNatAt, oneRowWeight]
  have : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.toNat (oneRowWeight n m hn) = 0 := oneRowWeight_shift n m hn
  unfold oneRowWeight at this
  rw [this]
  split_ifs <;> simp




set_option maxHeartbeats 800000 in
private theorem directSum_rank_ge_aleph0 [CharZero k] (n : ℕ) (hn : 0 < n) :
    Cardinal.aleph0 ≤ Module.rank k (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
      (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) := by
  set F := fun lam : RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n =>
    (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)


  have hne : ∀ m : ℕ, Nontrivial (RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n (oneRowWeight n m hn) k) := by
    intro m

    have hanti : Antitone (oneRowWeight n m hn).toNatAt := by
      rw [oneRowWeight_toNatWeight]
      intro i j hij
      by_cases hi : i = ⟨0, hn⟩ <;> by_cases hj : j = ⟨0, hn⟩ <;> simp [hi, hj]
      exfalso; apply hi; subst hj
      exact Fin.ext (show i.val = 0 by exact Nat.le_zero.mp hij)
    have hbot := RepresentationTheory.AuxiliaryModuleData.auxiliary_ne_bot_of_antitone (k := k) n (oneRowWeight n m hn).toNatAt hanti
    rw [ne_eq, ← Submodule.subsingleton_iff_eq_bot] at hbot
    exact not_subsingleton_iff_nontrivial.mp hbot
  rw [rank_directSum]



  have h1 : ∀ m : ℕ, 1 ≤ Module.rank k (F (oneRowWeight n m hn)) := by
    intro m
    haveI := hne m

    haveI : Nontrivial (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n (oneRowWeight n m hn) k) := by
      have hanti : Antitone (oneRowWeight n m hn).auxiliaryMap.toNatAt := by
        intro i j hij


        unfold RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.auxiliaryMap RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex.toNatAt
        apply Int.toNat_le_toNat
        gcongr
        simp only [neg_le_neg_iff]


        exact (oneRowWeight n m hn).property (Fin.rev_anti hij)
      exact not_subsingleton_iff_nontrivial.mp
        ((ne_eq .. ▸ Submodule.subsingleton_iff_eq_bot.not).mpr
          (RepresentationTheory.AuxiliaryModuleData.auxiliary_ne_bot_of_antitone (k := k) n _ hanti))
    exact Cardinal.one_le_iff_ne_zero.mpr (rank_pos (R := k)).ne'


  calc Cardinal.aleph0
      = Cardinal.sum (fun _ : ℕ => (1 : Cardinal)) := by simp
    _ ≤ Cardinal.sum (fun m : ℕ => Module.rank k (F (oneRowWeight n m hn))) :=
        Cardinal.sum_le_sum _ _ h1
    _ ≤ Cardinal.sum (fun lam => Module.rank k (F lam)) := by

        rw [Cardinal.sum, Cardinal.sum]
        exact ⟨⟨fun ⟨m, x⟩ => ⟨oneRowWeight n m hn, x⟩, fun ⟨m₁, x₁⟩ ⟨m₂, x₂⟩ h => by
          simp only [Sigma.mk.inj_iff] at h
          obtain ⟨hm, hx⟩ := h
          have hm' := oneRowWeight_injective n hn hm
          subst hm'
          exact Sigma.ext rfl (by exact hx)⟩⟩

private theorem peterWeyl_rank_eq [CharZero k] (n : ℕ) (hn : 0 < n) :
    Module.rank k (auxiliary n k) =
      Module.rank k (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
        (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k)) := by
  rw [glCoordinateRing_rank]
  exact le_antisymm (directSum_rank_le_aleph0 n) (directSum_rank_ge_aleph0 n hn) |>.symm

/-- Provides the existence of a linear equivalence from the auxiliary type to the displayed direct sum. -/
theorem nonempty_linearEquiv_auxiliary [CharZero k]
    (n : ℕ) (hn : 0 < n) :
    Nonempty (auxiliary n k ≃ₗ[k]
      (DirectSum (RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex n) fun lam =>
        (RepresentationTheory.AuxiliaryModuleData.auxiliaryOtherFamily n lam k ⊗[k] RepresentationTheory.AuxiliaryModuleData.auxiliaryFamily n lam k))) :=
  nonempty_linearEquiv_of_rank_eq (peterWeyl_rank_eq n hn)

end RepresentationTheory.AuxiliarySemisimpleDecomposition

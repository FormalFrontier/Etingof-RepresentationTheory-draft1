/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import RepresentationTheory.Alignment.Attribute

/-! # Endomorphism dichotomy -/




















namespace RepresentationTheory.Algebra.Module.EndomorphismDichotomy

/-- Under the displayed module property, every endomorphism is either bijective or nilpotent. -/
@[source_ref "Chapter3/Lemma3.8.2" (role := primary),
  source_ref "Chapter3/Lemma3.8.2/Derived2" (role := primary)]
theorem bijective_or_nilpotent_of_auxiliaryProperty (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A W)
    (θ : W →ₗ[A] W) :
    Function.Bijective θ ∨ IsNilpotent θ := by
  
  haveI : IsNoetherian A W := isNoetherian_of_tower k inferInstance
  haveI : IsArtinian A W := isArtinian_of_tower k inferInstance
  
  have hFit := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow θ
  
  have h_triv : (⨆ n, LinearMap.ker (θ ^ n)) = ⊥ ∨ (⨅ n, LinearMap.range (θ ^ n)) = ⊥ :=
    hW.2 _ _ hFit
  rcases h_triv with hker_bot | hrange_bot
  · 
    left
    have hker : LinearMap.ker θ = ⊥ := by
      refine eq_bot_iff.mpr ?_
      have h1 : LinearMap.ker θ ≤ ⨆ n, LinearMap.ker (θ ^ n) :=
        le_iSup_of_le 1 (by simp)
      rwa [hker_bot] at h1
    have hinj : Function.Injective θ := LinearMap.ker_eq_bot.mp hker
    exact ⟨hinj, (LinearMap.injective_iff_surjective (f := θ.restrictScalars k)).mp hinj⟩
  · 
    right
    
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp θ.eventually_iSup_ker_pow_eq
    
    have htop : (⨆ n, LinearMap.ker (θ ^ n)) = ⊤ := by
      have := codisjoint_iff.mp hFit.codisjoint
      rwa [hrange_bot, sup_bot_eq] at this
    rw [hm m le_rfl] at htop
    exact ⟨m, LinearMap.ext fun w => by
      have : w ∈ LinearMap.ker (θ ^ m) := htop ▸ Submodule.mem_top
      exact LinearMap.mem_ker.mp this⟩



/-- Under the displayed module property, a finite sum of nilpotent endomorphisms is nilpotent. -/
@[source_ref "Chapter3/Lemma3.8.2/Derived4" (role := primary),
  source_ref "Chapter3/Lemma3.8.2" (role := primary)]
theorem sum_nilpotent_of_auxiliaryProperty (k : Type*) (A : Type*) (W : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W]
    (hW : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A W)
    {n : ℕ} (θ : Fin n → (W →ₗ[A] W)) (hθ : ∀ i, IsNilpotent (θ i)) :
    IsNilpotent (∑ i, θ i) := by
  haveI := hW.1
  
  have nilp_not_unit : ∀ (f : Module.End A W), IsNilpotent f → ¬ IsUnit f := by
    rintro f ⟨m, hm⟩ huf
    exact not_isUnit_zero (hm ▸ huf.pow m)
  
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hN : IsNilpotent (∑ i : Fin n, θ (Fin.succ i)) := ih _ (fun i => hθ _)
    
    rcases bijective_or_nilpotent_of_auxiliaryProperty k A W hW
      (θ 0 + ∑ i : Fin n, θ (Fin.succ i)) with hbij | hnil
    · 
      exfalso
      
      have huS : IsUnit (θ 0 + ∑ i : Fin n, θ (Fin.succ i)) :=
        (Module.End.isUnit_iff _).mpr hbij
      obtain ⟨u, hu_eq⟩ := huS
      
      have h1 : (↑u⁻¹ : Module.End A W) * (θ 0) +
          ↑u⁻¹ * (∑ i : Fin n, θ (Fin.succ i)) = 1 := by
        rw [← mul_add, ← hu_eq, Units.inv_mul]
      
      have unit_lift : ∀ (f : Module.End A W),
          Function.Bijective ((↑u⁻¹ : Module.End A W) * f) → IsUnit f := by
        intro f hbf
        have : (f : Module.End A W) = ↑u * (↑u⁻¹ * f) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [this]; exact u.isUnit.mul ((Module.End.isUnit_iff _).mpr hbf)
      
      have h_nilp0 : IsNilpotent ((↑u⁻¹ : Module.End A W) * θ 0) := by
        rcases bijective_or_nilpotent_of_auxiliaryProperty k A W hW (↑u⁻¹ * θ 0) with hb | hn
        · exact absurd (unit_lift _ hb) (nilp_not_unit _ (hθ 0))
        · exact hn
      
      have h_nilpN : IsNilpotent ((↑u⁻¹ : Module.End A W) * ∑ i : Fin n, θ (Fin.succ i)) := by
        rcases bijective_or_nilpotent_of_auxiliaryProperty k A W hW
          (↑u⁻¹ * ∑ i : Fin n, θ (Fin.succ i)) with hb | hn
        · exact absurd (unit_lift _ hb) (nilp_not_unit _ hN)
        · exact hn
      
      have h_eq : (↑u⁻¹ : Module.End A W) * θ 0 =
          1 - ↑u⁻¹ * (∑ i : Fin n, θ (Fin.succ i)) :=
        eq_sub_of_add_eq h1
      
      have h_unit0 : IsUnit ((↑u⁻¹ : Module.End A W) * θ 0) := by
        rw [h_eq]; exact h_nilpN.isUnit_one_sub
      
      exact nilp_not_unit _ h_nilp0 h_unit0
    · exact hnil

end RepresentationTheory.Algebra.Module.EndomorphismDichotomy

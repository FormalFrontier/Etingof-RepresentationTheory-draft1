/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import RepresentationTheory.LinearAlgebra.ModuleDecompositions



/-! # Krull–Schmidt decompositions for modules -/

open LinearMap

namespace RepresentationTheory.Algebra.Module.KrullSchmidt

variable {A : Type*} [Ring A] {V : Type*} [AddCommGroup V] [Module A V]


/-- Under the displayed module property, every endomorphism is nilpotent or a unit. -/
theorem nilpotent_or_isUnit_end
    [IsArtinian A V] [IsNoetherian A V]
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A V) (f : Module.End A V) :
    IsNilpotent f ∨ IsUnit f := by
  
  obtain ⟨n, hcompl, hn1⟩ :=
    (f.eventually_isCompl_ker_pow_range_pow.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn1).symm⟩
  rcases hV.2 (LinearMap.ker (f ^ (m + 1))) (LinearMap.range (f ^ (m + 1))) hcompl with
    hker | hrange
  · 
    
    right
    rw [Module.End.isUnit_iff]
    have hinj_pow : Function.Injective (f ^ (m + 1)) := LinearMap.ker_eq_bot.mp hker
    have hsurj_pow : Function.Surjective (f ^ (m + 1)) := by
      rw [← LinearMap.range_eq_top]
      have hsup : LinearMap.ker (f ^ (m + 1)) ⊔ LinearMap.range (f ^ (m + 1)) = ⊤ :=
        codisjoint_iff.mp hcompl.codisjoint
      rwa [hker, bot_sup_eq] at hsup
    
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hinj_pow
      rw [Module.End.pow_apply, Module.End.pow_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hsurj_pow y
      refine ⟨(⇑f)^[m] z, ?_⟩
      rw [Module.End.pow_apply, Function.iterate_succ_apply'] at hz
      exact hz
  · 
    left
    refine ⟨m + 1, ?_⟩
    ext x
    have hx : (f ^ (m + 1)) x ∈ LinearMap.range (f ^ (m + 1)) := LinearMap.mem_range_self _ x
    rw [hrange, Submodule.mem_bot] at hx
    simpa using hx


/-- Under the displayed module property, the endomorphism ring of an Artinian and Noetherian module is local. -/
theorem isLocalRing_end
    [IsArtinian A V] [IsNoetherian A V]
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A V) :
    IsLocalRing (Module.End A V) := by
  haveI : Nontrivial V := hV.1
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases nilpotent_or_isUnit_end hV a with hnil | hunit
  · exact Or.inr (IsNilpotent.isUnit_one_sub hnil)
  · exact Or.inl hunit


private lemma exists_indecomposable_decomposition_aux
    [IsArtinian A V] [IsNoetherian A V] (d : ℕ) :
    ∀ S : Submodule A V, Module.length A (↥S) ≤ (d : ℕ∞) →
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, W i ≤ S) ∧
      (∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W i)) ∧
      (⨆ i, W i) = S ∧ iSupIndep W := by
  induction d with
  | zero =>
    intro S hd
    have hlen0 : Module.length A ↥S = 0 := le_zero_iff.mp (by simpa using hd)
    have hsub : Subsingleton ↥S := Module.length_eq_zero_iff.mp hlen0
    have hS : S = ⊥ := by
      by_contra hne
      exact (not_subsingleton_iff_nontrivial.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)) hsub
    subst hS
    exact ⟨0, Fin.elim0, nofun, nofun, by simp, iSupIndep_subsingleton _⟩
  | succ d ih =>
    intro S hd
    by_cases hIndec : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A S
    · exact ⟨1, fun _ => S, fun _ => le_refl S, fun _ => hIndec,
        by simp, iSupIndep_subsingleton _⟩
    · 
      by_cases hS_triv : S = ⊥
      · subst hS_triv
        exact ⟨0, Fin.elim0, nofun, nofun, by simp, iSupIndep_subsingleton _⟩
      have hS_nt : Nontrivial ↥S := Submodule.nontrivial_iff_ne_bot.mpr hS_triv
      unfold RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate at hIndec
      push Not at hIndec
      obtain ⟨M', N', hCompl, hM'ne, hN'ne⟩ := hIndec hS_nt
      have hSup' : M' ⊔ N' = ⊤ := codisjoint_iff.mp hCompl.codisjoint
      have hInf' : M' ⊓ N' = ⊥ := disjoint_iff.mp hCompl.disjoint
      
      set M := Submodule.map S.subtype M' with hM_def
      set N := Submodule.map S.subtype N' with hN_def
      have hML : M ≤ S := Submodule.map_subtype_le S M'
      have hNL : N ≤ S := Submodule.map_subtype_le S N'
      have hMN_sup : M ⊔ N = S := by
        rw [hM_def, hN_def, ← Submodule.map_sup, hSup',
          Submodule.map_top, Submodule.range_subtype]
      have hMN_disj : Disjoint M N := by
        rw [disjoint_iff, hM_def, hN_def,
          ← Submodule.map_inf S.subtype S.injective_subtype,
          hInf', Submodule.map_bot]
      have hM'_ne_top : M' ≠ ⊤ := by
        intro h; rw [h, top_inf_eq] at hInf'; exact hN'ne hInf'
      have hN'_ne_top : N' ≠ ⊤ := by
        intro h; rw [h, inf_top_eq] at hInf'; exact hM'ne hInf'
      have hM_lt_S : M < S := by
        refine lt_of_le_of_ne hML fun heq => hN'ne ?_
        have hN_le_M : N ≤ M := by rw [heq]; exact hMN_sup ▸ le_sup_right
        have hN_bot : N = ⊥ := eq_bot_iff.mpr (hMN_disj hN_le_M le_rfl)
        exact Submodule.map_injective_of_injective (S.injective_subtype)
          (hN_bot.trans (Submodule.map_bot _).symm)
      have hN_lt_S : N < S := by
        refine lt_of_le_of_ne hNL fun heq => hM'ne ?_
        have hM_le_N : M ≤ N := by rw [heq]; exact hMN_sup ▸ le_sup_left
        have hM_bot : M = ⊥ := eq_bot_iff.mpr (hMN_disj.symm hM_le_N le_rfl)
        exact Submodule.map_injective_of_injective (S.injective_subtype)
          (hM_bot.trans (Submodule.map_bot _).symm)
      
      have hlen : ∀ P : Submodule A V, P < S → Module.length A ↥P ≤ (d : ℕ∞) := by
        intro P hP
        have hPle : P ≤ S := hP.le
        have hne_top : Submodule.comap S.subtype P ≠ ⊤ := by
          rw [ne_eq, Submodule.comap_subtype_eq_top]
          exact fun hSP => hP.ne (le_antisymm hPle hSP)
        have hlt : Module.length A ↥(Submodule.comap S.subtype P) < Module.length A ↥S :=
          Submodule.length_lt hne_top
        rw [(Submodule.comapSubtypeEquivOfLe hPle).length_eq] at hlt
        have hstep : Module.length A ↥P < (d : ℕ∞) + 1 :=
          lt_of_lt_of_le hlt (by rw [← Nat.cast_add_one]; exact hd)
        exact (ENat.lt_add_one_iff (ENat.coe_ne_top d)).mp hstep
      obtain ⟨nM, WM, hWM_le, hWM_indec, hWM_sup, hWM_ind⟩ := ih M (hlen M hM_lt_S)
      obtain ⟨nN, WN, hWN_le, hWN_indec, hWN_sup, hWN_ind⟩ := ih N (hlen N hN_lt_S)
      
      set W' : Fin nM ⊕ Fin nN → Submodule A V := Sum.elim WM WN with hW'_def
      have hW'_le : ∀ i, W' i ≤ S := by
        intro i; cases i with
        | inl j => exact le_trans (hWM_le j) hML
        | inr j => exact le_trans (hWN_le j) hNL
      have hW'_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W' i) := by
        intro i; cases i with
        | inl j => exact hWM_indec j
        | inr j => exact hWN_indec j
      have hW'_sup : (⨆ i, W' i) = S := by
        simp only [W', iSup_sum, Sum.elim_inl, Sum.elim_inr, hWM_sup, hWN_sup, hMN_sup]
      have hW'_ind : iSupIndep W' := by
        intro i
        cases i with
        | inl j =>
          have h_comp_le : (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ (⨆ j', WN j') := by
            apply iSup_le; intro i; apply iSup_le; intro hi
            cases i with
            | inl j' =>
              exact le_sup_of_le_left
                (le_iSup_of_le j' (le_iSup_of_le (fun h => hi (congrArg Sum.inl h)) le_rfl))
            | inr j' => exact le_sup_of_le_right (le_iSup WN j')
          have hWM_j_le_M : WM j ≤ M := hWM_le j
          have hrest_le_M : (⨆ j', ⨆ (_ : j' ≠ j), WM j') ≤ M :=
            iSup₂_le fun j' _ => hWM_le j'
          have hN_eq : ⨆ j', WN j' = N := hWN_sup
          rw [disjoint_iff]
          apply eq_bot_iff.mpr
          have h_le_rest : WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
            calc WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i)
                ≤ WM j ⊓ ((⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ (⨆ j', WN j')) :=
                  inf_le_inf_left _ h_comp_le
              _ = WM j ⊓ ((⨆ j', ⨆ (_ : j' ≠ j), WM j') ⊔ N) := by rw [hN_eq]
              _ ≤ M ⊓ (N ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WM j')) := by
                  rw [sup_comm]; exact inf_le_inf_right _ hWM_j_le_M
              _ = M ⊓ N ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
                  (inf_sup_assoc_of_le N hrest_le_M).symm
              _ = (⨆ j', ⨆ (_ : j' ≠ j), WM j') := by
                  rw [disjoint_iff.mp hMN_disj, bot_sup_eq]
          calc WM j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inl j), W' i)
              ≤ WM j ⊓ (⨆ j', ⨆ (_ : j' ≠ j), WM j') :=
                le_inf inf_le_left h_le_rest
            _ = ⊥ := disjoint_iff.mp (hWM_ind j)
        | inr j =>
          have h_comp_le : (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i) ≤
              (⨆ j', WM j') ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j') := by
            apply iSup_le; intro i; apply iSup_le; intro hi
            cases i with
            | inl j' => exact le_sup_of_le_left (le_iSup WM j')
            | inr j' =>
              exact le_sup_of_le_right
                (le_iSup_of_le j' (le_iSup_of_le (fun h => hi (congrArg Sum.inr h)) le_rfl))
          have hWN_j_le_N : WN j ≤ N := hWN_le j
          have hrest_le_N : (⨆ j', ⨆ (_ : j' ≠ j), WN j') ≤ N :=
            iSup₂_le fun j' _ => hWN_le j'
          have hM_eq : ⨆ j', WM j' = M := hWM_sup
          rw [disjoint_iff]
          apply eq_bot_iff.mpr
          have h_le_rest : WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i) ≤
              (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
            calc WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i)
                ≤ WN j ⊓ ((⨆ j', WM j') ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) :=
                  inf_le_inf_left _ h_comp_le
              _ = WN j ⊓ (M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) := by rw [hM_eq]
              _ ≤ N ⊓ (M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j')) :=
                  inf_le_inf_right _ hWN_j_le_N
              _ = N ⊓ M ⊔ (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
                  (inf_sup_assoc_of_le M hrest_le_N).symm
              _ = (⨆ j', ⨆ (_ : j' ≠ j), WN j') := by
                  rw [inf_comm, disjoint_iff.mp hMN_disj, bot_sup_eq]
          calc WN j ⊓ (⨆ i, ⨆ (_ : i ≠ Sum.inr j), W' i)
              ≤ WN j ⊓ (⨆ j', ⨆ (_ : j' ≠ j), WN j') :=
                le_inf inf_le_left h_le_rest
            _ = ⊥ := disjoint_iff.mp (hWN_ind j)
      refine ⟨nM + nN, W' ∘ finSumFinEquiv.symm, ?_, ?_, ?_, ?_⟩
      · exact fun i => hW'_le (finSumFinEquiv.symm i)
      · exact fun i => hW'_indec (finSumFinEquiv.symm i)
      · rw [show (⨆ i, (W' ∘ finSumFinEquiv.symm) i) = ⨆ i, W' i from
          finSumFinEquiv.symm.surjective.iSup_comp W', hW'_sup]
      · exact hW'_ind.comp finSumFinEquiv.symm.injective


/-- An Artinian and Noetherian module has a finite internal spanning family satisfying the displayed module property. -/
theorem exists_internalFamily [IsArtinian A V] [IsNoetherian A V] :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W i)) ∧ iSup W = ⊤ ∧ iSupIndep W := by
  have hbound : Module.length A (↥(⊤ : Submodule A V)) ≤ ((Module.length A V).toNat : ℕ∞) := by
    rw [Submodule.topEquiv.length_eq, ENat.coe_toNat Module.length_ne_top]
  obtain ⟨n, W, _, hindec, hsup, hind⟩ :=
    exists_indecomposable_decomposition_aux (Module.length A V).toNat ⊤ hbound
  exact ⟨n, W, hindec, hsup, hind⟩


/-- Under the displayed module property, a finite sum of nilpotent endomorphisms is nilpotent. -/
theorem sum_nilpotent_end
    [IsArtinian A V] [IsNoetherian A V]
    (hV : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A V)
    {n : ℕ} (θ : Fin n → Module.End A V) (hθ : ∀ i, IsNilpotent (θ i)) :
    IsNilpotent (∑ i, θ i) := by
  haveI := hV.1
  have nilp_not_unit : ∀ (f : Module.End A V), IsNilpotent f → ¬ IsUnit f := by
    rintro f ⟨m, hm⟩ huf
    exact not_isUnit_zero (hm ▸ huf.pow m)
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hN : IsNilpotent (∑ i : Fin n, θ (Fin.succ i)) := ih _ (fun i => hθ _)
    rcases nilpotent_or_isUnit_end hV
      (θ 0 + ∑ i : Fin n, θ (Fin.succ i)) with hnil | huS
    · exact hnil
    · exfalso
      obtain ⟨u, hu_eq⟩ := huS
      have h1 : (↑u⁻¹ : Module.End A V) * (θ 0) +
          ↑u⁻¹ * (∑ i : Fin n, θ (Fin.succ i)) = 1 := by
        rw [← mul_add, ← hu_eq, Units.inv_mul]
      have unit_lift : ∀ (f : Module.End A V),
          IsUnit ((↑u⁻¹ : Module.End A V) * f) → IsUnit f := by
        intro f hbf
        have : (f : Module.End A V) = ↑u * (↑u⁻¹ * f) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [this]; exact u.isUnit.mul hbf
      have h_nilp0 : IsNilpotent ((↑u⁻¹ : Module.End A V) * θ 0) := by
        rcases nilpotent_or_isUnit_end hV (↑u⁻¹ * θ 0) with hn | hb
        · exact hn
        · exact absurd (unit_lift _ hb) (nilp_not_unit _ (hθ 0))
      have h_nilpN : IsNilpotent ((↑u⁻¹ : Module.End A V) * ∑ i : Fin n, θ (Fin.succ i)) := by
        rcases nilpotent_or_isUnit_end hV
          (↑u⁻¹ * ∑ i : Fin n, θ (Fin.succ i)) with hn | hb
        · exact hn
        · exact absurd (unit_lift _ hb) (nilp_not_unit _ hN)
      have h_eq : (↑u⁻¹ : Module.End A V) * θ 0 =
          1 - ↑u⁻¹ * (∑ i : Fin n, θ (Fin.succ i)) :=
        eq_sub_of_add_eq h1
      have h_unit0 : IsUnit ((↑u⁻¹ : Module.End A V) * θ 0) := by
        rw [h_eq]; exact h_nilpN.isUnit_one_sub
      exact nilp_not_unit _ h_nilp0 h_unit0


private lemma isCompl_equiv_of_isCompl {R : Type*} {V : Type*}
    [Ring R] [AddCommGroup V] [Module R V]
    {M C D : Submodule R V}
    (hMC : IsCompl M C) (hMD : IsCompl M D) :
    Nonempty (C ≃ₗ[R] D) :=
  ⟨(Submodule.quotientEquivOfIsCompl M C hMC).symm.trans
    (Submodule.quotientEquivOfIsCompl M D hMD)⟩


private lemma krull_schmidt_find_iso_summand_finiteLength
    [IsArtinian A V] [IsNoetherian A V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W i))
    (hW'_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W' i))
    (hW_ne : ∀ i, W i ≠ ⊥)
    (hW'_ne : ∀ i, W' i ≠ ⊥)
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W')
    (hn_pos : 0 < n) (hm_pos : 0 < m) :
    ∃ j : Fin m, Nonempty ((W ⟨0, hn_pos⟩) ≃ₗ[A] (W' j)) ∧
      IsCompl (W' j) (⨆ i, ⨆ (_ : i ≠ (⟨0, hn_pos⟩ : Fin n)), W i) := by
  set i₀ : Fin n := ⟨0, hn_pos⟩
  have hIntW : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).mpr ⟨hW_ind, hW_sup⟩
  have hIntW' : DirectSum.IsInternal W' :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W').mpr ⟨hW'_ind, hW'_sup⟩
  set eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hIntW with eW_def
  set eW' := LinearEquiv.ofBijective (DirectSum.coeLinearMap W') hIntW' with eW'_def
  set π₀ : V →ₗ[A] ↥(W i₀) :=
    (DirectSum.component A (Fin n) (fun i => ↥(W i)) i₀).comp eW.symm.toLinearMap
  set π' : ∀ j : Fin m, V →ₗ[A] ↥(W' j) :=
    fun j => (DirectSum.component A (Fin m) (fun j => ↥(W' j)) j).comp eW'.symm.toLinearMap
  set f : Fin m → Module.End A ↥(W i₀) :=
    fun j => (π₀.comp ((W' j).subtype.comp ((π' j).comp (W i₀).subtype)))
  have hπ₀_ι₀ : π₀.comp (W i₀).subtype = LinearMap.id := by
    ext ⟨y, hy⟩
    simp only [π₀, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply]
    exact congrArg Subtype.val (hIntW.ofBijective_coeLinearMap_same ⟨y, hy⟩)
  have hrecon : ∀ v : V, ∑ j : Fin m, ((W' j).subtype ((π' j) v) : V) = v := by
    intro v
    have hπ'_eq : ∀ j, π' j v = (eW'.symm v) j := fun j => rfl
    simp_rw [hπ'_eq]
    suffices h : ∀ (d : DirectSum (Fin m) (fun j => ↥(W' j))),
        (∑ j : Fin m, ((W' j).subtype (d j) : V)) = (DirectSum.coeLinearMap W') d by
      rw [h]; exact eW'.apply_symm_apply v
    intro d
    induction d using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      simp only [DirectSum.coeLinearMap_of]
      rw [Finset.sum_eq_single i]
      · simp [DirectSum.of_eq_same]
      · intro j _ hji; simp [DirectSum.of_eq_of_ne _ _ _ hji]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    | add x y hx hy =>
      simp only [map_add]
      simp_rw [show ∀ j : Fin m, (x + y) j = x j + y j from fun j => rfl,
        map_add, Finset.sum_add_distrib, hx, hy]
  have hf_sum : ∑ j, f j = LinearMap.id := by
    ext ⟨x, hx⟩
    simp only [f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
    have h1 : (∑ j : Fin m, π₀ ((W' j).subtype ((π' j) ((W i₀).subtype ⟨x, hx⟩)))) =
        π₀ (∑ j : Fin m, ((W' j).subtype ((π' j) x) : V)) := by
      rw [map_sum]; rfl
    rw [h1, hrecon x]
    have := LinearMap.congr_fun hπ₀_ι₀ ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    exact congrArg Subtype.val this
  have hW0_indec := hW_indec i₀
  have hW0_nontrivial : Nontrivial ↥(W i₀) :=
    Submodule.nontrivial_iff_ne_bot.mpr (hW_ne i₀)
  have hid_not_nilp : ¬ IsNilpotent (LinearMap.id : Module.End A ↥(W i₀)) := by
    rintro ⟨p, hp⟩
    simp at hp
    obtain ⟨a, b, hab⟩ := hW0_nontrivial
    have h1 := LinearMap.congr_fun hp a
    have h2 := LinearMap.congr_fun hp b
    simp at h1 h2
    exact hab (h1.trans h2.symm)
  have hf_not_all_nilp : ¬ ∀ j, IsNilpotent (f j) := by
    intro hall
    have := sum_nilpotent_end hW0_indec f hall
    rw [hf_sum] at this
    exact hid_not_nilp this
  push Not at hf_not_all_nilp
  obtain ⟨j₀, hj₀⟩ := hf_not_all_nilp
  have hj₀_bij : Function.Bijective (f j₀) := by
    rcases nilpotent_or_isUnit_end hW0_indec (f j₀) with hn | hu
    · exact absurd hn hj₀
    · exact (Module.End.isUnit_iff _).mp hu
  set α : ↥(W' j₀) →ₗ[A] ↥(W i₀) := π₀.comp (W' j₀).subtype
  set β : ↥(W i₀) →ₗ[A] ↥(W' j₀) := (π' j₀).comp (W i₀).subtype
  have hf_eq : f j₀ = α.comp β := rfl
  set φ : Module.End A ↥(W' j₀) := β.comp α
  have hφ_not_nilp : ¬ IsNilpotent φ := by
    intro ⟨p, hp⟩
    have key : ∀ (q : ℕ) (y : ↥(W' j₀)),
        ((α.comp β) ^ q) (α y) = α (((β.comp α) ^ q) y) := by
      intro q; induction q with
      | zero => intro y; simp
      | succ q ih =>
        intro y
        simp only [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
        exact ih (β (α y))
    have hf_pow : (f j₀) ^ (p + 1) = 0 := by
      rw [hf_eq]
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.zero_apply, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
      rw [key p (β x), show ((β.comp α) ^ p) (β x) = 0 from LinearMap.congr_fun hp (β x)]
      simp
    have hf_unit : IsUnit (f j₀) := (Module.End.isUnit_iff _).mpr hj₀_bij
    exact not_isUnit_zero (hf_pow ▸ hf_unit.pow (p + 1))
  have hW'_indec_j₀ := hW'_indec j₀
  have hφ_bij : Function.Bijective φ := by
    rcases nilpotent_or_isUnit_end hW'_indec_j₀ φ with hn | hu
    · exact absurd hn hφ_not_nilp
    · exact (Module.End.isUnit_iff _).mp hu
  have hα_inj : Function.Injective α := by
    intro a b h; exact hφ_bij.1 (show β (α a) = β (α b) by rw [h])
  have hα_surj : Function.Surjective α := by
    intro y; obtain ⟨x, hx⟩ := hj₀_bij.2 y
    rw [hf_eq] at hx; simp only [LinearMap.comp_apply] at hx
    exact ⟨β x, hx⟩
  set C := ⨆ i, ⨆ (_ : i ≠ i₀), W i
  have hIsCompl_W0_C : IsCompl (W i₀) C := by
    constructor
    · exact hW_ind i₀
    · rw [codisjoint_iff]
      apply top_le_iff.mp
      rw [← hW_sup]
      exact iSup_le fun i => by
        rcases eq_or_ne i i₀ with rfl | h
        · exact le_sup_left
        · exact le_sup_of_le_right (le_biSup _ h)
  set αe := LinearEquiv.ofBijective α ⟨hα_inj, hα_surj⟩
  set g : V →ₗ[A] ↥(W' j₀) := αe.symm.toLinearMap.comp π₀
  have hg_proj : ∀ x : ↥(W' j₀), g ((W' j₀).subtype x) = x := by
    intro x
    change αe.symm (π₀ ↑x) = x
    have : π₀ ↑x = αe x := rfl
    rw [this, αe.symm_apply_apply]
  have hIsCompl_g : IsCompl (W' j₀) (LinearMap.ker g) :=
    LinearMap.isCompl_of_proj hg_proj
  have hker_g_eq_C : LinearMap.ker g = C := by
    have : LinearMap.ker g = LinearMap.ker π₀ := by
      ext v; simp only [g, LinearMap.mem_ker, LinearMap.comp_apply]
      constructor
      · intro h
        have h0 : αe.symm (π₀ v) = αe.symm 0 := by
          rw [map_zero]; exact h
        exact αe.symm.injective h0
      · intro h; simp [h]
    rw [this]
    have hC_le : C ≤ LinearMap.ker π₀ := by
      apply iSup₂_le
      intro i hi v hv
      rw [LinearMap.mem_ker]
      change (DirectSum.component A (Fin n) (fun i => ↥(W i)) i₀)
        (eW.symm ((W i).subtype ⟨v, hv⟩)) = 0
      have heq : eW.symm ((W i).subtype ⟨v, hv⟩) =
          DirectSum.lof A (Fin n) (fun i => ↥(W i)) i ⟨v, hv⟩ := by
        apply eW.injective
        simp only [eW_def, LinearEquiv.ofBijective_apply, LinearEquiv.apply_symm_apply,
          DirectSum.coeLinearMap_of, Submodule.subtype_apply, DirectSum.lof_eq_of]
      rw [heq, DirectSum.component.of, dif_neg hi]
    apply le_antisymm _ hC_le
    intro x hx
    have hx_top : x ∈ W i₀ ⊔ C := hIsCompl_W0_C.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hx_top
    rw [LinearMap.mem_ker] at hx
    have hπ₀c : π₀ c = 0 := LinearMap.mem_ker.mp (hC_le hc)
    have hπ₀_w : (π₀ w : ↥(W i₀)) = ⟨w, hw⟩ := LinearMap.congr_fun hπ₀_ι₀ ⟨w, hw⟩
    have hkilled : π₀ (w + c) = 0 := hx
    rw [map_add, hπ₀c, add_zero] at hkilled
    rw [hπ₀_w] at hkilled
    have hw_zero : w = 0 :=
      congrArg Subtype.val (Subtype.ext_iff.mpr (congrArg Subtype.val hkilled))
    rw [hw_zero, zero_add]
    exact hc
  have hIsCompl_Wj₀_C : IsCompl (W' j₀) C := hker_g_eq_C ▸ hIsCompl_g
  exact ⟨j₀, ⟨αe.symm⟩, hIsCompl_Wj₀_C⟩


private lemma krull_schmidt_uniqueness_aux_finiteLength
    (d : ℕ) : ∀ (V : Type*) [AddCommGroup V] [Module A V] [IsArtinian A V] [IsNoetherian A V],
    Module.length A V ≤ (d : ℕ∞) →
    ∀ {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V),
    (∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W i)) →
    (∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W' i)) →
    (∀ i, W i ≠ ⊥) → (∀ i, W' i ≠ ⊥) →
    iSup W = ⊤ → iSup W' = ⊤ → iSupIndep W → iSupIndep W' →
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) := by
  induction d with
  | zero =>
    intro V _ _ _ _ hd n m W W' _ _ hW_ne hW'_ne hW_sup hW'_sup _ _
    have hV : Module.length A V = 0 := le_zero_iff.mp (by simpa using hd)
    haveI : Subsingleton V := Module.length_eq_zero_iff.mp hV
    have hn0 : n = 0 := by
      by_contra h
      exact hW_ne ⟨0, Nat.pos_of_ne_zero h⟩ Submodule.eq_bot_of_subsingleton
    have hm0 : m = 0 := by
      by_contra h
      exact hW'_ne ⟨0, Nat.pos_of_ne_zero h⟩ Submodule.eq_bot_of_subsingleton
    subst hn0; subst hm0
    exact ⟨rfl, ⟨Equiv.refl _, nofun⟩⟩
  | succ d ih =>
    intro V _ _ _ _ hd n m W W' hW_indec hW'_indec hW_ne hW'_ne hW_sup hW'_sup hW_ind hW'_ind
    by_cases hn : n = 0
    · subst hn
      have hm0 : m = 0 := by
        by_contra h
        have h_pos : 0 < m := Nat.pos_of_ne_zero h
        have hle : W' ⟨0, h_pos⟩ ≤ ⊤ := le_top
        have hV0 : (⊤ : Submodule A V) = ⊥ := by rw [← hW_sup]; simp
        rw [hV0] at hle
        exact hW'_ne ⟨0, h_pos⟩ (eq_bot_iff.mpr hle)
      subst hm0
      exact ⟨rfl, ⟨Equiv.refl _, nofun⟩⟩
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · exfalso
          subst hm0
          have hV0 : (⊤ : Submodule A V) = ⊥ := by rw [← hW'_sup]; simp
          have h_le : W ⟨0, hn_pos⟩ ≤ ⊤ := le_top
          rw [hV0] at h_le
          exact hW_ne ⟨0, hn_pos⟩ (eq_bot_iff.mpr h_le)
        · exact hm0
      obtain ⟨j₀, hj₀_iso, hIsCompl_j₀_C⟩ := krull_schmidt_find_iso_summand_finiteLength W W'
        hW_indec hW'_indec hW_ne hW'_ne hW_sup hW_ind hW'_sup hW'_ind hn_pos hm_pos
      set C := ⨆ i, ⨆ (_ : i ≠ (⟨0, hn_pos⟩ : Fin n)), W i
      set D := ⨆ j, ⨆ (_ : j ≠ j₀), W' j
      have hIsCompl_j₀_D : IsCompl (W' j₀) D := by
        exact ⟨hW'_ind j₀, codisjoint_iff.mpr (top_le_iff.mp (by
          rw [← hW'_sup]; exact iSup_le fun j => by
            rcases eq_or_ne j j₀ with rfl | h
            · exact le_sup_left
            · exact le_sup_of_le_right (le_biSup _ h)))⟩
      obtain ⟨eCD⟩ := isCompl_equiv_of_isCompl hIsCompl_j₀_C hIsCompl_j₀_D
      set i₀ : Fin n := ⟨0, hn_pos⟩
      have hIsCompl_W0_C : IsCompl (W i₀) C :=
        ⟨hW_ind i₀, codisjoint_iff.mpr
          (top_le_iff.mp (hW_sup ▸ iSup_le fun i =>
            (eq_or_ne i i₀).elim (· ▸ le_sup_left)
              (fun h => le_sup_of_le_right (le_biSup _ h))))⟩
      have hC_len : Module.length A ↥C ≤ (d : ℕ∞) := by
        have hC_lt : C < ⊤ := lt_top_iff_ne_top.mpr fun h =>
          hW_ne i₀ (by
            have := hIsCompl_W0_C.disjoint.eq_bot
            rw [h, inf_top_eq] at this; exact this)
        have hlt : Module.length A ↥C < Module.length A V := Submodule.length_lt hC_lt.ne
        have hstep : Module.length A ↥C < (d : ℕ∞) + 1 :=
          lt_of_lt_of_le hlt (by rw [← Nat.cast_add_one]; exact hd)
        exact (ENat.lt_add_one_iff (ENat.coe_ne_top d)).mp hstep
      have hW_le_C : ∀ i, i ≠ i₀ → W i ≤ C := fun i hi => le_biSup _ hi
      have hW'_le_D : ∀ j, j ≠ j₀ → W' j ≤ D := fun j hj => le_biSup _ hj
      let succMap : Fin (n - 1) → Fin n :=
        fun i => ⟨i.val + 1, by omega⟩
      have succMap_inj : Function.Injective succMap :=
        fun a b h => Fin.ext (by simp only [succMap, Fin.mk.injEq] at h; omega)
      have succMap_ne : ∀ i, succMap i ≠ i₀ :=
        fun i h => by simp only [succMap, i₀, Fin.mk.injEq] at h; omega
      have succMap_surj :
          ∀ i : Fin n, i ≠ i₀ → ∃ j, succMap j = i := by
        intro ⟨i, hi⟩ hne
        have hine : i ≠ 0 := fun h => hne (Fin.ext h)
        exact ⟨⟨i - 1, by omega⟩, Fin.ext (by simp [succMap]; omega)⟩
      let skipJ₀ : Fin (m - 1) → Fin m := fun i =>
        if i.val < j₀.val then ⟨i.val, by omega⟩
        else ⟨i.val + 1, by omega⟩
      have skipJ₀_inj : Function.Injective skipJ₀ := by
        intro a b h
        simp only [skipJ₀] at h
        ext
        split_ifs at h with h1 h2 h2
        · exact Fin.mk.inj h
        · exfalso; have := Fin.mk.inj h; omega
        · exfalso; have := Fin.mk.inj h; omega
        · have := Fin.mk.inj h; omega
      have skipJ₀_ne : ∀ i, skipJ₀ i ≠ j₀ := by
        intro i h
        simp only [skipJ₀] at h
        split_ifs at h with h1
        · exact absurd (Fin.mk.inj h).symm (by omega)
        · exact absurd (Fin.mk.inj h).symm (by omega)
      have skipJ₀_surj :
          ∀ j : Fin m, j ≠ j₀ → ∃ i, skipJ₀ i = j := by
        intro j hjne
        have hjne_val : j.val ≠ j₀.val := fun h => hjne (Fin.ext h)
        by_cases h : j.val < j₀.val
        · exact ⟨⟨j.val, by omega⟩, Fin.ext (by simp [skipJ₀, h])⟩
        · refine ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩
          simp only [skipJ₀]
          have hj_ge : ¬(j.val - 1 < j₀.val) := by omega
          simp [hj_ge]; omega
      let WC : Fin (n - 1) → Submodule A ↥C :=
        fun i => (W (succMap i)).comap C.subtype
      let W'D : Fin (m - 1) → Submodule A ↥D :=
        fun i => (W' (skipJ₀ i)).comap D.subtype
      let W'C : Fin (m - 1) → Submodule A ↥C :=
        fun i => (W'D i).map eCD.symm.toLinearMap
      have hWC_ne : ∀ i, WC i ≠ ⊥ := by
        intro i h; apply hW_ne (succMap i)
        have hmapC : Submodule.map C.subtype (WC i) = W (succMap i) :=
          by rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hW_le_C _ (succMap_ne i))]
        rw [← hmapC, h, Submodule.map_bot]
      have hWC_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (WC i) := by
        intro i
        refine ⟨Submodule.nontrivial_iff_ne_bot.mpr (hWC_ne i), fun P Q hPQ => ?_⟩
        have e := Submodule.comapSubtypeEquivOfLe (hW_le_C _ (succMap_ne i))
        have hSup := codisjoint_iff.mp hPQ.codisjoint
        have hInf := disjoint_iff.mp hPQ.disjoint
        by_contra hne
        push Not at hne
        obtain ⟨hP, hQ⟩ := hne
        exact (hW_indec (succMap i)).not_exists_auxiliary_pair
          ⟨P.map e.toLinearMap, Q.map e.toLinearMap,
           fun h => hP (by rwa [Submodule.map_eq_bot_iff] at h),
           fun h => hQ (by rwa [Submodule.map_eq_bot_iff] at h),
           by rw [← Submodule.map_sup, hSup, Submodule.map_top]
              exact LinearMap.range_eq_top.mpr e.surjective,
           by rw [← Submodule.map_inf e.toLinearMap e.injective, hInf, Submodule.map_bot]⟩
      have hWC_sup : iSup WC = ⊤ := by
        have hC_eq : C = ⨆ i, W (succMap i) := by
          rw [show C = ⨆ i, ⨆ (_ : i ≠ i₀), W i from rfl]
          apply le_antisymm
          · exact iSup₂_le fun i hi => by
              obtain ⟨j, hj⟩ := succMap_surj i hi
              exact hj ▸ le_iSup (fun i => W (succMap i)) j
          · exact iSup_le fun i => le_biSup W (succMap_ne i)
        rw [eq_top_iff]; intro ⟨x, hxC⟩ _
        have key : (⨆ i, (WC i).map C.subtype).comap C.subtype = iSup WC :=
          Submodule.comap_iSup_map_of_injective Subtype.val_injective WC
        rw [← key, Submodule.mem_comap]
        change x ∈ ⨆ i, (WC i).map C.subtype
        have h_map : ∀ i, (WC i).map C.subtype = W (succMap i) := fun i => by
          change (Submodule.map C.subtype ((W (succMap i)).comap C.subtype)) = W (succMap i)
          rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hW_le_C _ (succMap_ne i))]
        simp_rw [h_map]; rw [← hC_eq]; exact hxC
      have hWC_ind : iSupIndep WC := by
        intro i; rw [disjoint_iff, eq_bot_iff]
        intro ⟨x, hxC⟩ ⟨hxi, hxrest⟩
        suffices x = (0 : V) by exact Subtype.val_injective this
        have hx1 : x ∈ W (succMap i) := hxi
        have hx2 : x ∈ ⨆ j, ⨆ (_ : j ≠ i), W (succMap j) :=
          (iSup₂_le fun j hj => Submodule.comap_mono (le_biSup (W ∘ succMap) hj) :
            ⨆ j, ⨆ (_ : j ≠ i), WC j ≤
              (⨆ j, ⨆ (_ : j ≠ i), W (succMap j)).comap C.subtype) hxrest
        exact (Submodule.mem_bot A).mp
          (disjoint_iff.mp ((hW_ind.comp succMap_inj) i) ▸
            (⟨hx1, hx2⟩ : x ∈ W (succMap i) ⊓ _))
      have hW'D_ne : ∀ i, W'D i ≠ ⊥ := by
        intro i h; apply hW'_ne (skipJ₀ i)
        have hmapD : Submodule.map D.subtype (W'D i) = W' (skipJ₀ i) :=
          by rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hW'_le_D _ (skipJ₀_ne i))]
        rw [← hmapD, h, Submodule.map_bot]
      have hW'D_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W'D i) := by
        intro i
        refine ⟨Submodule.nontrivial_iff_ne_bot.mpr (hW'D_ne i), fun P Q hPQ => ?_⟩
        have e := Submodule.comapSubtypeEquivOfLe (hW'_le_D _ (skipJ₀_ne i))
        have hSup := codisjoint_iff.mp hPQ.codisjoint
        have hInf := disjoint_iff.mp hPQ.disjoint
        by_contra hne
        push Not at hne
        obtain ⟨hP, hQ⟩ := hne
        exact (hW'_indec (skipJ₀ i)).not_exists_auxiliary_pair
          ⟨P.map e.toLinearMap, Q.map e.toLinearMap,
           fun h => hP (by rwa [Submodule.map_eq_bot_iff] at h),
           fun h => hQ (by rwa [Submodule.map_eq_bot_iff] at h),
           by rw [← Submodule.map_sup, hSup, Submodule.map_top]
              exact LinearMap.range_eq_top.mpr e.surjective,
           by rw [← Submodule.map_inf e.toLinearMap e.injective, hInf, Submodule.map_bot]⟩
      have hW'D_sup : iSup W'D = ⊤ := by
        have hD_eq : D = ⨆ i, W' (skipJ₀ i) := by
          rw [show D = ⨆ j, ⨆ (_ : j ≠ j₀), W' j from rfl]
          apply le_antisymm
          · exact iSup₂_le fun j hj => by
              obtain ⟨i, hi⟩ := skipJ₀_surj j hj
              exact hi ▸ le_iSup (fun i => W' (skipJ₀ i)) i
          · exact iSup_le fun i => le_biSup W' (skipJ₀_ne i)
        rw [eq_top_iff]; intro ⟨x, hxD⟩ _
        have key : (⨆ i, (W'D i).map D.subtype).comap D.subtype = iSup W'D :=
          Submodule.comap_iSup_map_of_injective Subtype.val_injective W'D
        rw [← key, Submodule.mem_comap]
        change x ∈ ⨆ i, (W'D i).map D.subtype
        have h_map : ∀ i, (W'D i).map D.subtype = W' (skipJ₀ i) := fun i => by
          change (Submodule.map D.subtype ((W' (skipJ₀ i)).comap D.subtype)) = W' (skipJ₀ i)
          rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hW'_le_D _ (skipJ₀_ne i))]
        simp_rw [h_map]; rw [← hD_eq]; exact hxD
      have hW'D_ind : iSupIndep W'D := by
        intro i; rw [disjoint_iff, eq_bot_iff]
        intro ⟨x, hxD⟩ ⟨hxi, hxrest⟩
        suffices x = (0 : V) by exact Subtype.val_injective this
        have hx1 : x ∈ W' (skipJ₀ i) := hxi
        have hx2 : x ∈ ⨆ j, ⨆ (_ : j ≠ i), W' (skipJ₀ j) :=
          (iSup₂_le fun j hj => Submodule.comap_mono (le_biSup (W' ∘ skipJ₀) hj) :
            ⨆ j, ⨆ (_ : j ≠ i), W'D j ≤
              (⨆ j, ⨆ (_ : j ≠ i), W' (skipJ₀ j)).comap D.subtype) hxrest
        exact (Submodule.mem_bot A).mp
          (disjoint_iff.mp ((hW'_ind.comp skipJ₀_inj) i) ▸
            (⟨hx1, hx2⟩ : x ∈ W' (skipJ₀ i) ⊓ _))
      have hW'C_ne : ∀ i, W'C i ≠ ⊥ := by
        intro i h; apply hW'D_ne i
        rwa [show W'C i = (W'D i).map eCD.symm.toLinearMap from rfl,
          Submodule.map_eq_bot_iff] at h
      have hW'C_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W'C i) := by
        intro i
        have hcomap_eq : W'C i = (W'D i).comap (eCD : ↥C →ₗ[A] ↥D) := by
          change (W'D i).map eCD.symm.toLinearMap = (W'D i).comap (eCD : ↥C →ₗ[A] ↥D)
          rw [Submodule.comap_equiv_eq_map_symm]
        have e : ↥(W'C i) ≃ₗ[A] ↥(W'D i) :=
          hcomap_eq ▸ LinearEquiv.ofSubmodule' eCD (W'D i)
        refine ⟨Submodule.nontrivial_iff_ne_bot.mpr (hW'C_ne i), fun P Q hPQ => ?_⟩
        have hSup := codisjoint_iff.mp hPQ.codisjoint
        have hInf := disjoint_iff.mp hPQ.disjoint
        by_contra hne
        push Not at hne
        obtain ⟨hP, hQ⟩ := hne
        exact (hW'D_indec i).not_exists_auxiliary_pair
          ⟨P.map e.toLinearMap, Q.map e.toLinearMap,
           fun h => hP (by rwa [Submodule.map_eq_bot_iff] at h),
           fun h => hQ (by rwa [Submodule.map_eq_bot_iff] at h),
           by rw [← Submodule.map_sup, hSup, Submodule.map_top]
              exact LinearMap.range_eq_top.mpr e.surjective,
           by rw [← Submodule.map_inf e.toLinearMap e.injective, hInf, Submodule.map_bot]⟩
      have hW'C_sup : iSup W'C = ⊤ := by
        have hrw : iSup W'C = iSup (fun i => (W'D i).map eCD.symm.toLinearMap) := rfl
        rw [hrw, ← Submodule.map_iSup, hW'D_sup, Submodule.map_top]
        exact LinearMap.range_eq_top.mpr eCD.symm.surjective
      have hW'C_ind : iSupIndep W'C := by
        intro i; rw [disjoint_iff]
        have h_eq : ∀ j, W'C j = (W'D j).map eCD.symm.toLinearMap := fun _ => rfl
        simp_rw [h_eq, ← Submodule.map_iSup,
          ← Submodule.map_inf _ eCD.symm.injective,
          disjoint_iff.mp (hW'D_ind i), Submodule.map_bot]
      obtain ⟨hnm_pred, σ', hσ'⟩ := ih ↥C hC_len WC W'C
        hWC_indec hW'C_indec hWC_ne hW'C_ne
        hWC_sup hW'C_sup hWC_ind hW'C_ind
      have hnm : n = m := by omega
      subst hnm
      refine ⟨rfl, ?_⟩
      let σ_fun : Fin n → Fin n := fun i =>
        if h : i.val = 0 then j₀
        else skipJ₀ (σ' ⟨i.val - 1, by omega⟩)
      have σ_inj : Function.Injective σ_fun := by
        intro a b hab
        simp only [σ_fun] at hab
        split_ifs at hab with h1 h2
        · exact Fin.ext (by omega)
        · exfalso; exact skipJ₀_ne _ hab.symm
        · exfalso; exact skipJ₀_ne _ hab
        · exact Fin.ext (by
            have h3 := skipJ₀_inj hab
            have h4 := σ'.injective h3
            simp only [Fin.mk.injEq] at h4; omega)
      have σ_surj : Function.Surjective σ_fun := by
        intro j
        by_cases hj : j = j₀
        · exact ⟨⟨0, hn_pos⟩, by simp [σ_fun, hj]⟩
        · obtain ⟨i, hi⟩ := skipJ₀_surj j hj
          obtain ⟨k, hk⟩ := σ'.surjective i
          refine ⟨⟨k.val + 1, by omega⟩, ?_⟩
          simp only [σ_fun, show ¬((k.val + 1 : ℕ) = 0) from by omega,
            show k.val + 1 - 1 = k.val from by omega, dite_false]
          rw [show (⟨k.val, by omega⟩ : Fin (n - 1)) = k
            from Fin.ext rfl, hk, hi]
      refine ⟨Equiv.ofBijective σ_fun ⟨σ_inj, σ_surj⟩, fun i => ?_⟩
      change Nonempty (↥(W i) ≃ₗ[A] ↥(W' (σ_fun i)))
      by_cases h : (i : ℕ) = 0
      · have hσ_eq : σ_fun i = j₀ := dif_pos h
        rw [hσ_eq]
        have hi : i = i₀ := Fin.ext h
        subst hi; exact hj₀_iso
      · set idx : Fin (n - 1) := ⟨i.val - 1, by omega⟩
        have hσ_eq : σ_fun i = skipJ₀ (σ' idx) := dif_neg h
        rw [hσ_eq]
        obtain ⟨eIH⟩ := hσ' idx
        have hSucc : succMap idx = i :=
          Fin.ext (by simp [succMap, idx]; omega)
        have e1 : ↥(W i) ≃ₗ[A] ↥(WC idx) := by
          rw [show W i = W (succMap idx) from by rw [hSucc]]
          exact (Submodule.comapSubtypeEquivOfLe (hW_le_C _ (succMap_ne idx))).symm
        have hcomap : W'C (σ' idx) = (W'D (σ' idx)).comap (eCD : ↥C →ₗ[A] ↥D) := by
          change (W'D (σ' idx)).map eCD.symm.toLinearMap = _
          rw [Submodule.comap_equiv_eq_map_symm]
        have e2 : ↥(W'C (σ' idx)) ≃ₗ[A] ↥(W' (skipJ₀ (σ' idx))) := by
          rw [hcomap]
          exact (LinearEquiv.ofSubmodule' eCD (W'D (σ' idx))).trans
            (Submodule.comapSubtypeEquivOfLe (hW'_le_D _ (skipJ₀_ne (σ' idx))))
        exact ⟨e1.trans (eIH.trans e2)⟩


/-- Two finite internal spanning families satisfying the displayed property have equal lengths and equivalent members after a permutation. -/
theorem internalFamily_unique_up_to_permutation [IsArtinian A V] [IsNoetherian A V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W i))
    (hW'_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (W' i))
    (hW_ne : ∀ i, W i ≠ ⊥) (hW'_ne : ∀ i, W' i ≠ ⊥)
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W') :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i))) :=
  krull_schmidt_uniqueness_aux_finiteLength (Module.length A V).toNat V
    (ENat.coe_toNat Module.length_ne_top).ge W W'
    hW_indec hW'_indec hW_ne hW'_ne hW_sup hW'_sup hW_ind hW'_ind

end RepresentationTheory.Algebra.Module.KrullSchmidt

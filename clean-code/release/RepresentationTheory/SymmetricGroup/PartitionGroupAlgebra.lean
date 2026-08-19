/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions

/-!
# Partition group algebra

Provides group-algebra identities associated with a natural-number partition.
-/

namespace RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)



/-- If a permutation lies in the displayed set, multiplying the displayed group-algebra element on the right by its image in the group algebra leaves that element unchanged. -/
theorem mul_perm_eq_self_of_mem {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ (G n) p =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB]
  rw [Finset.sum_mul]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])



/-- If a permutation lies in the displayed set, multiplying the displayed group-algebra element on the left by its image in the group algebra leaves that element unchanged. -/
theorem perm_mul_eq_self_of_mem {n : ℕ} {la : Nat.Partition n}
    (p : G n) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    MonoidAlgebra.of ℂ (G n) p * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB]
  rw [Finset.mul_sum]
  simp_rw [← (MonoidAlgebra.of ℂ (G n)).map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft ⟨p, hp⟩) _ _
    (fun g => by simp [Subgroup.coe_mul])



/-- If a permutation lies in the displayed set, multiplying the displayed group-algebra element on the left by its image in the group algebra scales that element by the permutation's sign. -/
theorem perm_mul_eq_sign_smul_of_mem {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    MonoidAlgebra.of ℂ (G n) q * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA]
  rw [Finset.mul_sum, Finset.smul_sum]
  simp_rw [Algebra.mul_smul_comm, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  congr 1
  
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, hsqq, one_mul]



/-- If a permutation lies in the displayed set, multiplying the displayed group-algebra element on the right by its image in the group algebra scales that element by the permutation's sign. -/
theorem mul_perm_eq_sign_smul_of_mem {n : ℕ} {la : Nat.Partition n}
    (q : G n) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ (G n) q =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by
  classical
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA]
  rw [Finset.sum_mul, Finset.smul_sum]
  simp_rw [Algebra.smul_mul_assoc, ← (MonoidAlgebra.of ℂ (G n)).map_mul, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulRight ⟨q, hq⟩) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul]
  congr 1
  
  have hsqq : ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) = 1 := by
    have hmul : (Equiv.Perm.sign q : ℤˣ) * (Equiv.Perm.sign q : ℤˣ) = 1 := Int.units_mul_self _
    have h : ((Equiv.Perm.sign q : ℤˣ) : ℤ) * ((Equiv.Perm.sign q : ℤˣ) : ℤ) = 1 := by
      have := congr_arg Units.val hmul
      simp only [Units.val_mul, Units.val_one] at this
      exact this
    exact_mod_cast h
  simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
  
  linear_combination -((↑(↑(Equiv.Perm.sign g.val) : ℤ) : ℂ)) * hsqq

open Pointwise in





private theorem swap_mem_rowSubgroup {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (h : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val) :
    Equiv.swap i j ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl


private theorem swap_mem_colSubgroup {n : ℕ} {la : Nat.Partition n}
    {i j : Fin n} (h : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val) :
    Equiv.swap i j ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
  intro k
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl


private theorem conj_swap_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ⁻¹ * Equiv.swap i j * σ = Equiv.swap (σ⁻¹ i) (σ⁻¹ j) :=
  Equiv.trans_swap_trans_symm i j σ

open Pointwise in







/-- If a permutation does not lie in the product of the two displayed sets, there is a swap in the first set whose conjugate by that permutation lies in the second set. -/
@[source_ref "Chapter5/Lemma5.13.1" (role := supporting),
  source_ref "Chapter5/Discussion_end_of_Lemma5.13.1_proof" (role := supporting)]
theorem exists_swap_mem_left_of_not_mem_mul {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la : Set (Equiv.Perm (Fin n))) *
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la : Set (Equiv.Perm (Fin n)))) :
    ∃ t : Equiv.Perm (Fin n), Equiv.Perm.IsSwap t ∧
      t ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la ∧ σ⁻¹ * t * σ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
  classical
  
  
  
  let parts := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la
  let row := fun k : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts k.val
  let col := fun k : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k.val
  
  by_cases h_exists : ∃ i j : Fin n, i ≠ j ∧ row i = row j ∧ col (σ⁻¹ i) = col (σ⁻¹ j)
  · 
    obtain ⟨i, j, hij, hrow, hcol⟩ := h_exists
    exact ⟨Equiv.swap i j, ⟨i, j, hij, rfl⟩, swap_mem_rowSubgroup hrow,
      by rw [conj_swap_eq]; exact swap_mem_colSubgroup hcol⟩
  · 
    push Not at h_exists
    
    
    have h_col_inj : ∀ a b : Fin n, a ≠ b → col a = col b →
        row (σ a) ≠ row (σ b) := by
      intro a b hab hcol hrow
      have := h_exists (σ a) (σ b) (by intro h; exact hab (σ.injective h)) hrow
      have hcol_ne : col a ≠ col b := by simpa using this
      exact hcol_ne hcol
    exfalso
    apply hσ
    
    
    have hps : parts.sum = n := by
      change (la.parts.sort (· ≥ ·)).sum = n
      have h1 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ) = la.parts := Multiset.sort_eq _ _
      have h2 : (↑(la.parts.sort (· ≥ ·)) : Multiset ℕ).sum =
          (la.parts.sort (· ≥ ·)).sum := Multiset.sum_coe _
      linarith [h2.symm.trans (congrArg Multiset.sum h1), la.parts_sum]
    
    have getD_le_sum : ∀ (l : List ℕ) (i : ℕ), l.getD i 0 ≤ l.sum := by
      intro l i; induction l generalizing i with
      | nil => simp [List.getD]
      | cons a as ih =>
        cases i with
        | zero => rw [List.getD_cons_zero, List.sum_cons]; omega
        | succ j => rw [List.getD_cons_succ, List.sum_cons]; linarith [ih j]
    
    have row_valid_gen : ∀ (l : List ℕ) (k : ℕ), k < l.sum → RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow l k < l.length := by
      intro l k hk
      by_contra h; push Not at h
      have hcol := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength l k hk
      have hgetD : l.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow l k) 0 = 0 := by
        apply List.getD_eq_default; omega
      omega
    have row_valid : ∀ k : Fin n, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts k.val < parts.length := by
      intro k; exact row_valid_gen parts k.val (by omega)
    
    
    
    have cell_valid : ∀ k : Fin n,
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k.val < parts.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k).val) 0 := by
      
      suffices worse : ∀ (c₀ : ℕ) (k₀ : Fin n),
          parts.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k₀).val) 0 ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₀.val →
          c₀ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₀.val →
          ∃ k₁ : Fin n,
            parts.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k₁).val) 0 ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₁.val ∧
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₁.val > c₀ by
        
        by_contra h_bad; push Not at h_bad; obtain ⟨k₀, hk₀⟩ := h_bad
        have chain : ∀ m : ℕ, ∃ k' : Fin n,
            parts.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k').val) 0 ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k'.val ∧
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k'.val ≥ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₀.val + m := by
          intro m; induction m with
          | zero => exact ⟨k₀, hk₀, le_refl _⟩
          | succ m ih =>
            obtain ⟨k', hk'_bad, hge⟩ := ih
            obtain ⟨k'', hk'', hgt⟩ := worse _ k' hk'_bad rfl
            exact ⟨k'', hk'', by omega⟩
        obtain ⟨k', _, hge⟩ := chain n
        have hcol_bound := (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength parts k'.val (by omega)).trans_le
          (getD_le_sum parts _)
        omega
      
      intro c₀ k₀ hk₀_bad hc₀_eq
      
      let S_c := Finset.univ.filter (fun k : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k.val = c₀)
      
      let R_c := (Finset.range parts.length).filter (fun r => c₀ < parts.getD r 0)
      
      let σ_img := S_c.image (fun k => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k).val)
      
      have hk₀_S : k₀ ∈ S_c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc₀_eq.symm⟩
      
      have hr₀_img : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k₀).val ∈ σ_img :=
        Finset.mem_image.mpr ⟨k₀, hk₀_S, rfl⟩
      
      have hr₀_not_Rc : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k₀).val ∉ R_c := by
        intro hmem
        have := (Finset.mem_filter.mp hmem).2
        omega
      
      have hcard_S_le_R : S_c.card ≤ R_c.card := by
        apply Finset.card_le_card_of_injOn (fun k : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts k.val)
        · intro k hk
          have hk_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (row_valid k), ?_⟩
          rw [← hk_col]; exact RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn_lt_rowLength parts k.val (by omega)
        · intro k₁ hk₁ k₂ hk₂ heq
          have hk₁_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₁)).2
          have hk₂_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₂)).2
          exact Fin.val_injective (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq parts k₁.val k₂.val
            (by omega) (by omega) heq (by rw [hk₁_col, hk₂_col]))
      
      have hcard_img : σ_img.card = S_c.card := by
        apply Finset.card_image_of_injOn
        intro k₁ hk₁ k₂ hk₂ heq
        have hk₁_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₁)).2
        have hk₂_col := (Finset.mem_filter.mp (Finset.mem_coe.mp hk₂)).2
        by_contra hne
        have hcol_eq : col k₁ = col k₂ := by
          change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₂.val
          rw [hk₁_col, hk₂_col]
        exact h_col_inj k₁ k₂ hne hcol_eq heq
      
      have ⟨r_star, hr_star_Rc, hr_star_not_img⟩ : ∃ r ∈ R_c, r ∉ σ_img := by
        by_contra h_all; push Not at h_all
        have h_union := Finset.card_le_card
          (Finset.union_subset h_all (Finset.singleton_subset_iff.mpr hr₀_img))
        rw [Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr hr₀_not_Rc),
          Finset.card_singleton] at h_union
        omega
      have hr_star_wide : c₀ < parts.getD r_star 0 :=
        (Finset.mem_filter.mp hr_star_Rc).2
      
      let T_rs := Finset.univ.filter (fun i : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts i.val = r_star)
      
      have h_σinv_inj : Set.InjOn (fun i : Fin n => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (σ⁻¹ i).val) ↑T_rs := by
        intro i hi j hj heq
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        by_contra hne
        have hrow_eq : row i = row j := by
          change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts i.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts j.val
          rw [hi', hj']
        exact h_exists i j hne hrow_eq heq
      
      have h_no_c : ∀ i ∈ T_rs, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (σ⁻¹ i).val ≠ c₀ := by
        intro i hi habs
        have hi_row := (Finset.mem_filter.mp hi).2
        apply hr_star_not_img
        refine Finset.mem_image.mpr ⟨σ⁻¹ i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, habs⟩, ?_⟩
        have happ : σ (σ⁻¹ i) = i := by change (σ * σ⁻¹) i = i; simp
        rw [show RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ (σ⁻¹ i)).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts i.val from by
          congr 1; exact congrArg Fin.val happ]
        exact hi_row
      
      let ci := T_rs.image (fun i => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (σ⁻¹ i).val)
      have hci_card : ci.card = T_rs.card := Finset.card_image_of_injOn h_σinv_inj
      
      have hTrs_large : parts.getD r_star 0 ≤ T_rs.card := by
        have pos_in_row : ∀ c' : ℕ, c' < parts.getD r_star 0 →
            ∃ k : Fin n, k ∈ T_rs ∧ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k.val = c' := by
          intro c' hc'
          obtain ⟨pos, hpos, hrow, hcol⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts r_star c' hc'
          exact ⟨⟨pos, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow⟩, hcol⟩
        choose f hf_mem hf_col using pos_in_row
        rw [← Fintype.card_fin (parts.getD r_star 0)]
        rw [← Finset.card_univ (α := Fin (parts.getD r_star 0))]
        apply Finset.card_le_card_of_injOn
          (fun c' : Fin (parts.getD r_star 0) => f c'.val c'.isLt)
        · intro c' _; exact hf_mem c'.val c'.isLt
        · intro c₁ _ c₂ _ heq
          have h1 := hf_col c₁.val c₁.isLt
          have h2 := hf_col c₂.val c₂.isLt
          have hfinval : (f c₁.val c₁.isLt).val = (f c₂.val c₂.isLt).val :=
            congrArg Fin.val heq
          
          have : c₁.val = c₂.val := by rw [← h1, ← h2, hfinval]
          exact Fin.ext this
      
      have ⟨c', hc'_mem, hc'_large⟩ : ∃ c' ∈ ci, parts.getD r_star 0 ≤ c' := by
        by_contra h_all; push Not at h_all
        have hsub : ci ⊆ Finset.range (parts.getD r_star 0) \ {c₀} := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (h_all x hx), ?_⟩
          rw [Finset.mem_singleton]
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact h_no_c i hi
        have h1 := Finset.card_le_card hsub
        have hsing_sub : {c₀} ⊆ Finset.range (parts.getD r_star 0) :=
          Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hr_star_wide)
        rw [Finset.card_sdiff_of_subset hsing_sub, Finset.card_range,
          Finset.card_singleton] at h1
        omega
      
      obtain ⟨i, hi_T, hi_col⟩ := Finset.mem_image.mp hc'_mem
      have hi_row := (Finset.mem_filter.mp hi_T).2
      refine ⟨σ⁻¹ i, ?_, ?_⟩
      · 
        show parts.getD (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ (σ⁻¹ i)).val) 0 ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (σ⁻¹ i).val
        have happ : σ (σ⁻¹ i) = i := by
          change (σ * σ⁻¹) i = i; simp
        rw [show (σ (σ⁻¹ i)).val = i.val from congrArg Fin.val happ, hi_row]
        linarith
      · 
        change c₀ < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (σ⁻¹ i).val
        linarith
    
    have q_spec : ∀ k : Fin n, ∃ k' : Fin n,
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts k'.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k).val ∧
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k'.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k.val := by
      intro k
      obtain ⟨pos, hpos, hrow, hcol⟩ := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength parts
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k).val) (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k.val) (cell_valid k)
      exact ⟨⟨pos, hps ▸ hpos⟩, hrow, hcol⟩
    choose q_fun hq_row hq_col using q_spec
    
    have q_inj : Function.Injective q_fun := by
      intro k₁ k₂ heq
      by_contra hne
      have hσne : σ k₁ ≠ σ k₂ := fun h => hne (σ.injective h)
      have hval : (q_fun k₁).val = (q_fun k₂).val := congrArg Fin.val heq
      have hrow_σ : row (σ k₁) = row (σ k₂) := by
        change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k₁).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts (σ k₂).val
        rw [← hq_row k₁, ← hq_row k₂, hval]
      have hcol_k : col k₁ = col k₂ := by
        change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₁.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k₂.val
        rw [← hq_col k₁, ← hq_col k₂, hval]
      have h_absurd := h_exists (σ k₁) (σ k₂) hσne hrow_σ
      have hcol_ne : col k₁ ≠ col k₂ := by simpa using h_absurd
      exact hcol_ne hcol_k
    
    have q_surj := (Finite.injective_iff_surjective).mp q_inj
    
    let q_perm : Equiv.Perm (Fin n) := Equiv.ofBijective q_fun ⟨q_inj, q_surj⟩
    
    have hq_col_sub : q_perm ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
      intro k
      change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts (q_fun k).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts k.val
      exact hq_col k
    
    have hp_row : σ * q_perm⁻¹ ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := by
      intro k
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have h := hq_row (q_perm⁻¹ k)
      have hqq : q_fun (q_perm⁻¹ k) = k := by
        change q_perm (q_perm⁻¹ k) = k; exact q_perm.apply_symm_apply k
      rw [hqq] at h; exact h.symm
    
    refine Set.mem_mul.mpr ⟨σ * q_perm⁻¹, hp_row, q_perm, hq_col_sub, ?_⟩
    group


private theorem sandwich_mem {n : ℕ} {la : Nat.Partition n}
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ (q * p) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) := by
  rw [map_mul (MonoidAlgebra.of ℂ _)]
  simp only [mul_assoc]
  rw [perm_mul_eq_self_of_mem p hp,
    ← mul_assoc (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la), mul_perm_eq_sign_smul_of_mem q hq,
    Algebra.smul_mul_assoc]

open Pointwise in




private theorem sandwich_not_mem {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la : Set (Equiv.Perm (Fin n))) *
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la : Set (Equiv.Perm (Fin n)))) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la = 0 := by
  classical
  
  have hσ_inv : σ⁻¹ ∉ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la : Set (Equiv.Perm (Fin n))) *
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la : Set (Equiv.Perm (Fin n))) := by
    intro hmem
    apply hσ
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.mp hmem
    exact Set.mem_mul.mpr ⟨q⁻¹, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem hq,
      p⁻¹, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).inv_mem hp,
      show q⁻¹ * p⁻¹ = σ from by rw [← mul_inv_rev, hpq, inv_inv]⟩
  obtain ⟨t, ht_swap, ht_row, ht_col'⟩ := exists_swap_mem_left_of_not_mem_mul σ⁻¹ hσ_inv
  
  set u := σ * t * σ⁻¹ with hu_def
  have hu_col : u ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := by
    have : σ⁻¹⁻¹ = σ := inv_inv σ
    rw [hu_def, ← this]; exact ht_col'
  
  
  have hσt : σ * t = u * σ := by
    rw [hu_def, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  
  have hsign_u : (↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ) = -1 := by
    have hsign_t : Equiv.Perm.sign t = -1 := by
      obtain ⟨x, z, hxz, ht_eq⟩ := ht_swap; rw [ht_eq]; exact Equiv.Perm.sign_swap hxz
    have : Equiv.Perm.sign u = -1 := by
      change Equiv.Perm.sign (σ * t * σ⁻¹) = -1
      rw [map_mul, map_mul, hsign_t, Equiv.Perm.sign_inv]
      simp [mul_comm, Int.units_mul_self]
    simp [this]
  
  
  
  suffices heq : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) by
    
    rw [hsign_u, neg_one_smul] at heq
    
    have hg : ∀ g, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ *
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la).coeff g = 0 := by
      intro g
      have := Finsupp.ext_iff.mp (congrArg MonoidAlgebra.coeff heq) g
      have hneg : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la).coeff g =
          - (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ *
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la).coeff g := by
        simpa using this
      exact (mul_eq_zero.mp (show (2 : ℂ) * _ = 0 by linear_combination hneg)).resolve_left
        (by norm_num)
    exact MonoidAlgebra.coeff_injective (Finsupp.ext hg)
  
  
  
  have h1 : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ (σ * t) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
    conv_lhs => rw [← perm_mul_eq_self_of_mem t ht_row]
    rw [map_mul (MonoidAlgebra.of ℂ _) σ t]
    simp only [mul_assoc]
  have h2 : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ (u * σ) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la) := by
    rw [map_mul (MonoidAlgebra.of ℂ _)]
    simp only [mul_assoc]
    rw [← mul_assoc (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la), mul_perm_eq_sign_smul_of_mem u hu_col,
      Algebra.smul_mul_assoc]
  exact h1.trans (hσt ▸ h2)

set_option maxHeartbeats 800000 in



private lemma dual_sandwich_mem {n : ℕ} {la : Nat.Partition n}
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la)
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ (p * q) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
  rw [map_mul (MonoidAlgebra.of ℂ _)]
  simp only [mul_assoc]
  rw [perm_mul_eq_sign_smul_of_mem q hq, Algebra.mul_smul_comm, Algebra.mul_smul_comm]
  congr 1
  rw [← mul_assoc, mul_perm_eq_self_of_mem p hp]

open Pointwise in


private theorem dual_sandwich_not_mem {n : ℕ} {la : Nat.Partition n}
    (σ : Equiv.Perm (Fin n))
    (hσ : σ ∉ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la : Set (Equiv.Perm (Fin n))) *
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la : Set (Equiv.Perm (Fin n)))) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la = 0 := by
  classical
  obtain ⟨t, ht_swap, ht_row, ht_col'⟩ := exists_swap_mem_left_of_not_mem_mul σ hσ
  set u := σ⁻¹ * t * σ with hu_def
  have hu_col : u ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := ht_col'
  have hσt : t * σ = σ * u := by simp [hu_def]; group
  have hsign_u : (↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ) = -1 := by
    have hsign_t : Equiv.Perm.sign t = -1 := by
      obtain ⟨x, z, hxz, ht_eq⟩ := ht_swap; rw [ht_eq]; exact Equiv.Perm.sign_swap hxz
    have : Equiv.Perm.sign u = -1 := by
      change Equiv.Perm.sign (σ⁻¹ * t * σ) = -1
      rw [map_mul, map_mul, hsign_t, Equiv.Perm.sign_inv]
      simp [mul_comm, Int.units_mul_self]
    simp [this]
  suffices heq : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) by
    rw [hsign_u, neg_one_smul] at heq
    have hg : ∀ g, (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ *
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la).coeff g = 0 := by
      intro g
      have := Finsupp.ext_iff.mp (congrArg MonoidAlgebra.coeff heq) g
      have hneg : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la).coeff g =
          - (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ *
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la).coeff g := by
        simpa using this
      exact (mul_eq_zero.mp (show (2 : ℂ) * _ = 0 by linear_combination hneg)).resolve_left
        (by norm_num)
    exact MonoidAlgebra.coeff_injective (Finsupp.ext hg)
  have h1 : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ (t * σ) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by
    conv_lhs => rw [← mul_perm_eq_self_of_mem t ht_row]
    rw [map_mul (MonoidAlgebra.of ℂ _) t σ]
    simp only [mul_assoc]
  have h2 : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ (σ * u) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
      ((↑(↑(Equiv.Perm.sign u) : ℤ) : ℂ)) •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
    rw [map_mul (MonoidAlgebra.of ℂ _)]
    simp only [mul_assoc]
    rw [perm_mul_eq_sign_smul_of_mem u hu_col, Algebra.mul_smul_comm, Algebra.mul_smul_comm]
  exact h1.trans (hσt ▸ h2)



private lemma sign_cast_sq {n : ℕ} (g : Equiv.Perm (Fin n)) :
    ((↑(↑(Equiv.Perm.sign g) : ℤ) : ℂ)) * ((↑(↑(Equiv.Perm.sign g) : ℤ) : ℂ)) = 1 := by
  have hmul : (Equiv.Perm.sign g : ℤˣ) * (Equiv.Perm.sign g : ℤˣ) = 1 := Int.units_mul_self _
  have h : ((Equiv.Perm.sign g : ℤˣ) : ℤ) * ((Equiv.Perm.sign g : ℤˣ) : ℤ) = 1 := by
    have := congrArg Units.val hmul
    exact this
  exact_mod_cast h



/-- The square of the displayed group-algebra element is the cardinality of the displayed set times that element. -/
theorem fixed_action_sq_eq_card_smul {n : ℕ} (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
      (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
  classical
  have hexp : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la
      = ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la), MonoidAlgebra.of ℂ (G n) (g : Equiv.Perm (Fin n)) := rfl
  calc RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la
      = (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la), MonoidAlgebra.of ℂ (G n) (g : Equiv.Perm (Fin n)))
          * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by rw [← hexp]
    _ = ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
          MonoidAlgebra.of ℂ (G n) (g : Equiv.Perm (Fin n)) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
          rw [Finset.sum_mul]
    _ = ∑ _g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la), RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
          refine Finset.sum_congr rfl (fun g _ => ?_)
          exact perm_mul_eq_self_of_mem (g : Equiv.Perm (Fin n)) g.2
    _ = (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
            Nat.cast_smul_eq_nsmul]



/-- The square of the displayed group-algebra element is the cardinality of the displayed set times that element. -/
theorem sign_action_sq_eq_card_smul {n : ℕ} (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
      (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by
  classical
  have hexp : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la
      = ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
          ((↑(↑(Equiv.Perm.sign (g : Equiv.Perm (Fin n))) : ℤ) : ℂ)) •
            MonoidAlgebra.of ℂ (G n) (g : Equiv.Perm (Fin n)) := rfl
  calc RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la
      = (∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
          ((↑(↑(Equiv.Perm.sign (g : Equiv.Perm (Fin n))) : ℤ) : ℂ)) •
            MonoidAlgebra.of ℂ (G n) (g : Equiv.Perm (Fin n)))
          * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by rw [← hexp]
    _ = ∑ g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
          ((↑(↑(Equiv.Perm.sign (g : Equiv.Perm (Fin n))) : ℤ) : ℂ)) •
            (MonoidAlgebra.of ℂ (G n) (g : Equiv.Perm (Fin n)) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
          rw [Finset.sum_mul]; simp_rw [Algebra.smul_mul_assoc]
    _ = ∑ _g : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la), RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [perm_mul_eq_sign_smul_of_mem (g : Equiv.Perm (Fin n)) g.2, smul_smul,
            sign_cast_sq, one_smul]
    _ = (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
            Nat.cast_smul_eq_nsmul]


/-- The square of the displayed left-hand sandwich element is itself. -/
@[source_ref "Chapter5/Discussion_Young_projectors" (role := supporting)]
theorem left_idempotent_sq {n : ℕ} (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF n la = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF n la := by
  have hne : (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) := Nat.card_pos
    exact_mod_cast this.ne'
  have hs : ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ)⁻¹ * (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ)⁻¹)
      * (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) = (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, fixed_action_sq_eq_card_smul, smul_smul,
    smul_smul, hs]


/-- The square of the displayed right-hand sandwich element is itself. -/
@[source_ref "Chapter5/Discussion_Young_projectors" (role := supporting)]
theorem right_idempotent_sq {n : ℕ} (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE n la = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE n la := by
  have hne : (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ) ≠ 0 := by
    have : 0 < Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) := Nat.card_pos
    exact_mod_cast this.ne'
  have hs : ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ)⁻¹ * (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ)⁻¹)
      * (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ) = (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, sign_action_sq_eq_card_smul, smul_smul,
    smul_smul, hs]





/-- The product of the two displayed idempotent elements is the inverse of the product of the two displayed set cardinalities, acting as a scalar on the displayed target element. -/
theorem right_idempotent_mul_left_idempotent {n : ℕ} (la : Nat.Partition n) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF n la =
      ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) * (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ))⁻¹
        • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  have hscalar : (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ)⁻¹ * (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ)⁻¹
      = ((Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) : ℂ) * (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) : ℂ))⁻¹ := by
    rw [mul_inv]; ring
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, smul_smul, hscalar]

end RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra

open Pointwise in



/-- For each partition, there is a function-like scalar-valued object such that placing any group-algebra element between the two displayed elements gives its scalar value times a third displayed element. -/
theorem RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_sign_fixed_sandwich_eq_smul
    (n : ℕ) (la : Nat.Partition n) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ,
      ∀ x, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
        ℓ x • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  classical
  
  have basis_mul : ∀ σ : Equiv.Perm (Fin n), ∃ coeff : ℂ,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
        coeff • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
    intro σ
    by_cases hmem : σ ∈ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la : Set (Equiv.Perm (Fin n))) *
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la : Set (Equiv.Perm (Fin n)))
    · obtain ⟨q, hq, p, hp, hqp⟩ := Set.mem_mul.mp hmem
      exact ⟨↑(↑(Equiv.Perm.sign q) : ℤ), by rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC]; exact hqp ▸ sandwich_mem q hq p hp⟩
    · exact ⟨0, by rw [zero_smul]; exact sandwich_not_mem σ hmem⟩
  
  choose f hf using basis_mul
  let ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ :=
    (Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))).comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  refine ⟨ℓ, fun x => ?_⟩
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    have hleft : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la *
        (0 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la = 0 := by
      simp
    have hright :
        ℓ (0 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = 0 := by
      simp
    exact hleft.trans hright.symm
  | add x y hx hy =>
    let x' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := x
    let y' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := y
    change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * (x' + y') * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la =
      ℓ (x' + y') • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la
    rw [map_add, add_smul, mul_add, add_mul]
    exact congr_arg₂ (· + ·) hx hy
  | single σ r =>
    have hℓ : ℓ (MonoidAlgebra.single σ r) = f σ * r := by
      change (Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))
        (Finsupp.single σ r) = f σ * r
      rw [Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have hsingle : MonoidAlgebra.single σ r = r • MonoidAlgebra.of ℂ _ σ := by
      ext g
      simp [MonoidAlgebra.coeff_single]
    conv_lhs => rw [hsingle]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hf, smul_smul, hℓ, mul_comm]

open Pointwise in




/-- For each partition, there is a function-like scalar-valued object such that placing any group-algebra element between the two displayed elements gives its scalar value times their product. -/
@[source_ref "Chapter5/Lemma5.13.1" (role := supporting)]
theorem RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_fixed_sign_sandwich_eq_smul_mul
    (n : ℕ) (la : Nat.Partition n) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ,
      ∀ x, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
        ℓ x • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
  classical
  have basis_mul : ∀ σ : Equiv.Perm (Fin n), ∃ coeff : ℂ,
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * MonoidAlgebra.of ℂ _ σ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
        coeff • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) := by
    intro σ
    by_cases hmem : σ ∈ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la : Set (Equiv.Perm (Fin n))) *
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la : Set (Equiv.Perm (Fin n)))
    · obtain ⟨p, hp, q, hq, hpq⟩ := Set.mem_mul.mp hmem
      exact ⟨↑(↑(Equiv.Perm.sign q) : ℤ), hpq ▸ dual_sandwich_mem p hp q hq⟩
    · exact ⟨0, by rw [zero_smul]; exact dual_sandwich_not_mem σ hmem⟩
  choose f hf using basis_mul
  let ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ :=
    (Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))).comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  refine ⟨ℓ, fun x => ?_⟩
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    have hleft : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la *
        (0 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la = 0 := by
      simp
    have hright : ℓ (0 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) •
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la) = 0 := by
      simp
    exact hleft.trans hright.symm
  | add x y hx hy =>
    let x' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := x
    let y' : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) := y
    change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * (x' + y') * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la =
      ℓ (x' + y') • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la)
    rw [map_add, add_smul, mul_add, add_mul]
    exact congr_arg₂ (· + ·) hx hy
  | single σ r =>
    have hℓ : ℓ (MonoidAlgebra.single σ r) = f σ * r := by
      change (Finsupp.lsum ℂ (fun σ => f σ • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))
        (Finsupp.single σ r) = f σ * r
      rw [Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have hsingle : MonoidAlgebra.single σ r = r • MonoidAlgebra.of ℂ _ σ := by
      ext g
      simp [MonoidAlgebra.coeff_single]
    conv_lhs => rw [hsingle]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hf, smul_smul, hℓ, mul_comm]

open Pointwise in






/-- For each partition, there is a function-like scalar-valued object such that placing any group-algebra element between the two displayed idempotent elements gives its scalar value times a third displayed element. -/
@[source_ref "Chapter5/Introduction_5.13" (role := supporting),
  source_ref "Chapter5/Lemma5.13.1" (role := primary)]
theorem RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_idempotent_sandwich_eq_smul
    (n : ℕ) (la : Nat.Partition n) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) →ₗ[ℂ] ℂ,
      ∀ x, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF n la * x * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE n la =
        ℓ x • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD n la := by
  obtain ⟨ℓ, hℓ⟩ := RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_fixed_sign_sandwich_eq_smul_mul n la
  refine ⟨ℓ, fun x => ?_⟩
  have key := hℓ x
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm]
  rw [key]
  simp only [smul_smul]
  congr 1
  ring

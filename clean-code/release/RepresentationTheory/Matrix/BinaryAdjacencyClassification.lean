/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteIntegerMatrixModels
import RepresentationTheory.IntegerAdjacencyMatrixCombinatorics
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Matrix.BinaryAdjacencyClassification

open Matrix Finset





/-- Any two indices assigned the value three by the given matrix-dependent function are equal. -/
lemma Matrix.vertex_eq_of_values_eq_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (v w : Fin n)
    (hv : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj v = 3) (hw : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj w = 3) : v = w := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  by_contra hvw
  
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      
      symm := ⟨fun i j h => by change adj j i = 1; rw [hsymm.apply i j]; exact h⟩
      loopless := ⟨fun i h => by change adj i i = 1 at h; linarith [hdiag i]⟩ }
  haveI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
  haveI : Nonempty (Fin n) := ⟨v⟩
  have hG_conn : G.Connected :=
    ⟨fun u w' => by
      obtain ⟨path, hhead, hlast, hedges⟩ := hconn u w'
      exact RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.reachable_of_list_path G path u w' hhead hlast hedges⟩
  obtain ⟨walk⟩ := hG_conn.preconnected v w
  set pw := (walk.toPath : G.Walk v w) with hpw_def
  have hpw_path : pw.IsPath := (walk.toPath).property
  set L := pw.length with hL_def
  have hL_pos : 0 < L := by
    rw [Nat.pos_iff_ne_zero]; intro hL0; apply hvw
    have hL0' : pw.length = 0 := by omega
    have h1 := pw.getVert_length
    rw [hL0'] at h1
    rw [← pw.getVert_zero]; exact h1
  
  set supp := pw.support.toFinset with hsupp_def
  have hv_in : v ∈ supp := List.mem_toFinset.mpr pw.start_mem_support
  have hw_in : w ∈ supp := List.mem_toFinset.mpr pw.end_mem_support
  have hgv_in : ∀ m, m ≤ L → pw.getVert m ∈ supp :=
    fun m _ => List.mem_toFinset.mpr (pw.getVert_mem_support m)
  have hgv_adj : ∀ m, m < L → adj (pw.getVert m) (pw.getVert (m + 1)) = 1 :=
    fun m hm => pw.adj_getVert_succ hm
  have hgv_inj : ∀ m₁ m₂, m₁ ≤ L → m₂ ≤ L → pw.getVert m₁ = pw.getVert m₂ →
      m₁ = m₂ :=
    fun m₁ m₂ h₁ h₂ heq => hpw_path.getVert_injOn h₁ h₂ heq
  
  set x : Fin n → ℤ := fun i =>
    if i ∈ supp then 2
    else if adj v i = 1 ∨ adj w i = 1 then 1
    else 0 with hx_def
  have hx_ne : x ≠ 0 := by
    intro h; have hv0 := congr_fun h v
    change (if v ∈ supp then 2
      else if adj v v = 1 ∨ adj w v = 1 then 1 else 0) = 0 at hv0
    rw [if_pos hv_in] at hv0; exact absurd hv0 (by omega)
  have hx_nonneg : ∀ i, 0 ≤ x i := fun i => by simp only [x]; split_ifs <;> omega
  have hadj_nonneg : ∀ a b, 0 ≤ adj a b * x b := fun a b =>
    mul_nonneg (by rcases h01 a b with h | h <;> omega) (hx_nonneg b)
  
  have mulVec_eq : ∀ a, ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) a =
      2 * x a - ∑ b, adj a b * x b := by
    intro a; simp only [Matrix.mulVec, dotProduct]
    rw [show ∑ b, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) a b * x b =
        ∑ b, (2 * (1 : Matrix _ _ ℤ) a b * x b - adj a b * x b) from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.sub_apply, Matrix.smul_apply]; ring)]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [show ∑ b, 2 * (1 : Matrix (Fin n) (Fin n) ℤ) a b * x b =
        ∑ b, if a = b then 2 * x b else 0 from
      Finset.sum_congr rfl (fun b _ => by
        simp only [Matrix.one_apply]; split_ifs <;> simp)]
    simp
  have adj_sum_lb : ∀ (a b₁ b₂ : Fin n), b₁ ≠ b₂ →
      adj a b₁ = 1 → adj a b₂ = 1 →
      adj a b₁ * x b₁ + adj a b₂ * x b₂ ≤ ∑ b, adj a b * x b := by
    intro a b₁ b₂ hne hab₁ hab₂
    calc adj a b₁ * x b₁ + adj a b₂ * x b₂ =
        ∑ b ∈ ({b₁, b₂} : Finset _), adj a b * x b := by
          rw [Finset.sum_pair hne]
      _ ≤ ∑ b, adj a b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg a b)
  have adj_sum_lb1 : ∀ (a b₁ : Fin n),
      adj a b₁ = 1 → adj a b₁ * x b₁ ≤ ∑ b, adj a b * x b := by
    intro a b₁ hab₁
    calc adj a b₁ * x b₁ = ∑ b ∈ ({b₁} : Finset _), adj a b * x b := by simp
      _ ≤ ∑ b, adj a b * x b :=
          Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg a b)
  
  have v_adj_sum_ge4 : ∀ (p1 : Fin n), adj v p1 = 1 → p1 ∈ supp →
      4 ≤ ∑ b, adj v b * x b := by
    intro p1 hp1_adj hp1_supp
    set N := Finset.univ.filter (fun j => adj v j = 1) with hN_def
    have hN_card : N.card = 3 := by
      simp only [hN_def]; delta RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount at hv; convert hv
    have hp1_N : p1 ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1_adj⟩
    have hN_erase : (N.erase p1).card = 2 := by
      rw [Finset.card_erase_of_mem hp1_N]; omega
    have hN_le : ∑ j ∈ N, adj v j * x j ≤ ∑ b, adj v b * x b :=
      Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg v b)
    have hN_sum : ∑ j ∈ N, adj v j * x j = adj v p1 * x p1 +
        ∑ j ∈ N.erase p1, adj v j * x j :=
      (Finset.add_sum_erase N _ hp1_N).symm
    have hxp1 : x p1 = 2 := by
      change (if p1 ∈ supp then 2 else _) = 2
      rw [if_pos hp1_supp]
    
    have hN_min : ∀ j ∈ N.erase p1, 1 ≤ adj v j * x j := by
      intro j hj
      have hadj_j := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
      rw [hadj_j, one_mul]
      change 1 ≤ (if j ∈ supp then 2
        else if adj v j = 1 ∨ adj w j = 1 then 1 else 0)
      split_ifs with h1 h2
      · omega
      · omega
      · exact absurd (Or.inl hadj_j) h2
    
    have hsum_ge : 2 ≤ ∑ j ∈ N.erase p1, adj v j * x j := by
      calc 2 = ∑ _ ∈ N.erase p1, (1 : ℤ) := by
            rw [Finset.sum_const]; simp [hN_erase]
        _ ≤ ∑ j ∈ N.erase p1, adj v j * x j :=
          Finset.sum_le_sum hN_min
    nlinarith [hp1_adj, hxp1]
  have w_adj_sum_ge4 : ∀ (p1 : Fin n), adj w p1 = 1 → p1 ∈ supp →
      4 ≤ ∑ b, adj w b * x b := by
    intro p1 hp1_adj hp1_supp
    set N := Finset.univ.filter (fun j => adj w j = 1) with hN_def
    have hN_card : N.card = 3 := by
      simp only [hN_def]; delta RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount at hw; convert hw
    have hp1_N : p1 ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1_adj⟩
    have hN_erase : (N.erase p1).card = 2 := by
      rw [Finset.card_erase_of_mem hp1_N]; omega
    have hN_le : ∑ j ∈ N, adj w j * x j ≤ ∑ b, adj w b * x b :=
      Finset.sum_le_univ_sum_of_nonneg (fun b => hadj_nonneg w b)
    have hN_sum : ∑ j ∈ N, adj w j * x j = adj w p1 * x p1 +
        ∑ j ∈ N.erase p1, adj w j * x j :=
      (Finset.add_sum_erase N _ hp1_N).symm
    have hxp1 : x p1 = 2 := by
      change (if p1 ∈ supp then 2 else _) = 2
      rw [if_pos hp1_supp]
    have hN_min : ∀ j ∈ N.erase p1, 1 ≤ adj w j * x j := by
      intro j hj
      have hadj_j := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
      rw [hadj_j, one_mul]
      change 1 ≤ (if j ∈ supp then 2
        else if adj v j = 1 ∨ adj w j = 1 then 1 else 0)
      split_ifs with h1 h2
      · omega
      · omega
      · exact absurd (Or.inr hadj_j) h2
    have hsum_ge : 2 ≤ ∑ j ∈ N.erase p1, adj w j * x j := by
      calc 2 = ∑ _ ∈ N.erase p1, (1 : ℤ) := by
            rw [Finset.sum_const]; simp [hN_erase]
        _ ≤ ∑ j ∈ N.erase p1, adj w j * x j :=
          Finset.sum_le_sum hN_min
    nlinarith [hp1_adj, hxp1]
  
  have hB_le : dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) ≤ 0 := by
    apply Finset.sum_nonpos; intro a _
    rw [mulVec_eq]
    by_cases ha_S : a ∈ supp
    · 
      have hxa : x a = 2 := by simp [x, ha_S]
      rw [hxa]
      
      have ha_mem : a ∈ pw.support := List.mem_toFinset.mp ha_S
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.mem_iff_getElem.mp ha_mem
      rw [pw.length_support] at hidx_lt
      have hidx_le : idx ≤ L := by omega
      have ha_gv : pw.getVert idx = a := by
        rw [pw.getVert_eq_support_getElem hidx_le]; exact hidx_eq
      by_cases hidx0 : idx = 0
      · 
        have hav : a = v := by rw [← ha_gv, hidx0, pw.getVert_zero]
        rw [hav]
        have h01 := hgv_adj 0 hL_pos
        rw [pw.getVert_zero] at h01
        nlinarith [v_adj_sum_ge4 (pw.getVert 1) h01 (hgv_in 1 (by omega))]
      · by_cases hidxL : idx = L
        · 
          have haw : a = w := by
            rw [← ha_gv, hidxL]; exact pw.getVert_length
          rw [haw]
          have hp_adj : adj w (pw.getVert (L - 1)) = 1 := by
            have := hgv_adj (L - 1) (by omega)
            rw [show L - 1 + 1 = L from by omega] at this
            rwa [pw.getVert_length, hsymm.apply] at this
          nlinarith [w_adj_sum_ge4 (pw.getVert (L - 1)) hp_adj
            (hgv_in (L - 1) (by omega))]
        · 
          have h0 : 0 < idx := by omega
          have hL' : idx < L := by omega
          have hpred := hgv_adj (idx - 1) (by omega)
          rw [show idx - 1 + 1 = idx from by omega] at hpred
          have hsucc := hgv_adj idx hL'
          rw [ha_gv] at hpred hsucc
          have hpred' : adj a (pw.getVert (idx - 1)) = 1 := by
            rw [hsymm.apply]; exact hpred
          have hne : pw.getVert (idx - 1) ≠ pw.getVert (idx + 1) := by
            intro heq
            exact absurd (hgv_inj (idx - 1) (idx + 1) (by omega)
              (by omega) heq) (by omega)
          have hpred_x : x (pw.getVert (idx - 1)) = 2 := by
            simp [x, hgv_in (idx - 1) (by omega)]
          have hsucc_x : x (pw.getVert (idx + 1)) = 2 := by
            simp [x, hgv_in (idx + 1) (by omega)]
          nlinarith [adj_sum_lb a _ _ hne hpred' hsucc,
            hpred_x, hsucc_x]
    · 
      by_cases ha_adj : adj v a = 1 ∨ adj w a = 1
      · have hxa : x a = 1 := by
          simp only [x, if_neg ha_S, if_pos ha_adj]
        rw [hxa]
        rcases ha_adj with hva | hwa
        · have hav : adj a v = 1 := by rw [hsymm.apply]; exact hva
          have hxv : x v = 2 := by simp [hx_def, hv_in]
          nlinarith [adj_sum_lb1 a v hav]
        · have haw : adj a w = 1 := by rw [hsymm.apply]; exact hwa
          have hxw : x w = 2 := by simp [hx_def, hw_in]
          nlinarith [adj_sum_lb1 a w haw]
      · have : x a = 0 := by simp [x, ha_S, ha_adj]
        rw [this]; simp
  linarith [hpos x hx_ne]





/-- If the matrix-dependent value at an index is three, then some index has both matrix entry one from it and matrix-dependent value one. -/
lemma Matrix.exists_entry_one_and_vertex_value_one_of_vertex_value_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (v : Fin n) (hv : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj v = 3) :
    ∃ u, adj v u = 1 ∧ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj u = 1 := by
  obtain ⟨hsymm, hdiag, h01, _, hpos⟩ := hD
  
  by_contra h; push Not at h
  
  have h_nbr_deg : ∀ u, adj v u = 1 → 2 ≤ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj u := by
    intro u hu
    have h1 : 1 ≤ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj u := by
      change 1 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card
      exact Finset.one_le_card.mpr ⟨v, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hsymm.apply v u).symm ▸ hu⟩⟩
    have h_ne1 : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj u ≠ 1 := h u hu
    omega
  
  set N := Finset.univ.filter (fun j => adj v j = 1) with hN_def
  have hN_card : N.card = 3 := hv
  
  obtain ⟨n₁, n₂, n₃, hne12, hne13, hne23, hcover⟩ :=
    Finset.card_eq_three.mp hN_card
  have hn₁_adj : adj v n₁ = 1 := by
    have : n₁ ∈ N := hcover ▸ Finset.mem_insert_self _ _
    exact (Finset.mem_filter.mp this).2
  have hn₂_adj : adj v n₂ = 1 := by
    have : n₂ ∈ N := hcover ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self _ _))
    exact (Finset.mem_filter.mp this).2
  have hn₃_adj : adj v n₃ = 1 := by
    have : n₃ ∈ N := hcover ▸ Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))
    exact (Finset.mem_filter.mp this).2
  
  have get_second_nbr : ∀ u, adj v u = 1 → u ≠ v →
      ∃ w, adj u w = 1 ∧ w ≠ v ∧ w ≠ u := by
    intro u hu hu_ne
    have hdeg : 2 ≤ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj u := h_nbr_deg u hu
    
    have : 2 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card := hdeg
    have hv_mem : v ∈ Finset.univ.filter (fun j => adj u j = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsymm.apply v u).symm ▸ hu⟩
    
    have h_erase := Finset.card_erase_of_mem hv_mem
    have : 1 ≤ ((Finset.univ.filter (fun j => adj u j = 1)).erase v).card := by omega
    obtain ⟨w, hw_mem⟩ := Finset.one_le_card.mp this
    have hw := Finset.mem_erase.mp hw_mem
    have hw_ne_u : w ≠ u := by
      intro heq; subst heq
      have := (Finset.mem_filter.mp hw.2).2
      rw [hdiag] at this; omega
    exact ⟨w, (Finset.mem_filter.mp hw.2).2, hw.1, hw_ne_u⟩
  
  have hv_ne1 : n₁ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₁_adj; omega
  have hv_ne2 : n₂ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₂_adj; omega
  have hv_ne3 : n₃ ≠ v := by
    intro h; subst h; rw [hdiag] at hn₃_adj; omega
  obtain ⟨a₁, ha₁_adj, ha₁_nv, ha₁_nn⟩ := get_second_nbr n₁ hn₁_adj hv_ne1
  obtain ⟨a₂, ha₂_adj, ha₂_nv, ha₂_nn⟩ := get_second_nbr n₂ hn₂_adj hv_ne2
  obtain ⟨a₃, ha₃_adj, ha₃_nv, ha₃_nn⟩ := get_second_nbr n₃ hn₃_adj hv_ne3
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  set x : Fin n → ℤ := fun a =>
    if a = v then 3
    else if a = n₁ ∨ a = n₂ ∨ a = n₃ then 2
    else if a = a₁ ∨ a = a₂ ∨ a = a₃ then 1
    else 0 with hx_def
  have hx_ne : x ≠ 0 := by
    intro h; have := congr_fun h v; simp [x] at this
  
  have hB_le : dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) ≤ 0 := by
    
    
    
    
    
    
    have hx_nonneg : ∀ i, 0 ≤ x i := by
      intro i; simp only [x]; split_ifs <;> omega
    have hadj_x_nn : ∀ i j, 0 ≤ adj i j * x j := by
      intro i j; rcases h01 i j with h | h <;> simp [h, hx_nonneg j]
    
    have ha_n1v : adj n₁ v = 1 := by rw [hsymm.apply v n₁]; exact hn₁_adj
    have ha_n2v : adj n₂ v = 1 := by rw [hsymm.apply v n₂]; exact hn₂_adj
    have ha_n3v : adj n₃ v = 1 := by rw [hsymm.apply v n₃]; exact hn₃_adj
    have ha_a1n1 : adj a₁ n₁ = 1 := by rw [hsymm.apply n₁ a₁]; exact ha₁_adj
    have ha_a2n2 : adj a₂ n₂ = 1 := by rw [hsymm.apply n₂ a₂]; exact ha₂_adj
    have ha_a3n3 : adj a₃ n₃ = 1 := by rw [hsymm.apply n₃ a₃]; exact ha₃_adj
    
    have hxv : x v = 3 := by simp [x]
    have hxn1 : x n₁ = 2 := by
      change (if n₁ = v then 3 else if n₁ = n₁ ∨ n₁ = n₂ ∨ n₁ = n₃ then 2 else _) = 2
      rw [if_neg hv_ne1, if_pos (Or.inl rfl)]
    have hxn2 : x n₂ = 2 := by
      change (if n₂ = v then 3 else if n₂ = n₁ ∨ n₂ = n₂ ∨ n₂ = n₃ then 2 else _) = 2
      rw [if_neg hv_ne2, if_pos (Or.inr (Or.inl rfl))]
    have hxn3 : x n₃ = 2 := by
      change (if n₃ = v then 3 else if n₃ = n₁ ∨ n₃ = n₂ ∨ n₃ = n₃ then 2 else _) = 2
      rw [if_neg hv_ne3, if_pos (Or.inr (Or.inr rfl))]
    
    suffices h_bound : ∀ i : Fin n, 2 * x i ≤ ∑ j : Fin n, adj i j * x j by
      
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply]
      apply Finset.sum_nonpos
      intro i _
      apply mul_nonpos_of_nonneg_of_nonpos (hx_nonneg i)
      
      change ∑ j : Fin n, ((2 : ℤ) * (if i = j then 1 else 0) - adj i j) * x j ≤ 0
      have : ∑ j : Fin n, ((2 : ℤ) * (if i = j then (1 : ℤ) else 0) - adj i j) * x j =
          2 * x i - ∑ j : Fin n, adj i j * x j := by
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        congr 1
        simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
          (fun j _ hji => by rw [if_neg (Ne.symm hji)])]
        simp
      linarith [this, h_bound i]
    
    intro i
    by_cases hxi : x i = 0
    · simp [hxi]; exact Finset.sum_nonneg (fun j _ => hadj_x_nn i j)
    · have hi_cases : i = v ∨ (i = n₁ ∨ i = n₂ ∨ i = n₃) ∨
          (i = a₁ ∨ i = a₂ ∨ i = a₃) := by
        simp only [x] at hxi; split_ifs at hxi <;> simp_all
      
      rcases hi_cases with hi | (hi | hi | hi) | (hi | hi | hi) <;> rw [hi]
      · 
        have hS : ({n₁, n₂, n₃} : Finset _).sum (fun j => adj v j * x j) ≤
            ∑ j : Fin n, adj v j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn v j)
        have hS_eq : ({n₁, n₂, n₃} : Finset _).sum (fun j => adj v j * x j) = 6 := by
          have hm1 : n₁ ∉ ({n₂, n₃} : Finset _) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨hne12, hne13⟩
          rw [Finset.sum_insert hm1, Finset.sum_pair hne23,
              hn₁_adj, hn₂_adj, hn₃_adj, hxn1, hxn2, hxn3]; norm_num
        rw [hxv]; linarith
      · 
        have hS_le : ({v, a₁} : Finset _).sum (fun j => adj n₁ j * x j) ≤
            ∑ j : Fin n, adj n₁ j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn n₁ j)
        have hS_ge : ({v, a₁} : Finset _).sum (fun j => adj n₁ j * x j) ≥ 4 := by
          rw [Finset.sum_pair (Ne.symm ha₁_nv), ha_n1v, ha₁_adj, one_mul, one_mul, hxv]
          have : x a₁ ≥ 1 := by
            change (if a₁ = v then 3 else if a₁ = n₁ ∨ a₁ = n₂ ∨ a₁ = n₃ then 2
              else if a₁ = a₁ ∨ a₁ = a₂ ∨ a₁ = a₃ then 1 else 0) ≥ 1
            rw [if_neg ha₁_nv]
            by_cases h : a₁ = n₁ ∨ a₁ = n₂ ∨ a₁ = n₃
            · rw [if_pos h]; omega
            · rw [if_neg h, if_pos (show a₁ = a₁ ∨ a₁ = a₂ ∨ a₁ = a₃ from Or.inl rfl)]
          linarith
        rw [hxn1]; linarith
      · 
        have hS_le : ({v, a₂} : Finset _).sum (fun j => adj n₂ j * x j) ≤
            ∑ j : Fin n, adj n₂ j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn n₂ j)
        have hS_ge : ({v, a₂} : Finset _).sum (fun j => adj n₂ j * x j) ≥ 4 := by
          rw [Finset.sum_pair (Ne.symm ha₂_nv), ha_n2v, ha₂_adj, one_mul, one_mul, hxv]
          have : x a₂ ≥ 1 := by
            change (if a₂ = v then 3 else if a₂ = n₁ ∨ a₂ = n₂ ∨ a₂ = n₃ then 2
              else if a₂ = a₁ ∨ a₂ = a₂ ∨ a₂ = a₃ then 1 else 0) ≥ 1
            rw [if_neg ha₂_nv]
            by_cases h : a₂ = n₁ ∨ a₂ = n₂ ∨ a₂ = n₃
            · rw [if_pos h]; omega
            · rw [if_neg h, if_pos (show a₂ = a₁ ∨ a₂ = a₂ ∨ a₂ = a₃ from Or.inr (Or.inl rfl))]
          linarith
        rw [hxn2]; linarith
      · 
        have hS_le : ({v, a₃} : Finset _).sum (fun j => adj n₃ j * x j) ≤
            ∑ j : Fin n, adj n₃ j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => hadj_x_nn n₃ j)
        have hS_ge : ({v, a₃} : Finset _).sum (fun j => adj n₃ j * x j) ≥ 4 := by
          rw [Finset.sum_pair (Ne.symm ha₃_nv), ha_n3v, ha₃_adj, one_mul, one_mul, hxv]
          have : x a₃ ≥ 1 := by
            change (if a₃ = v then 3 else if a₃ = n₁ ∨ a₃ = n₂ ∨ a₃ = n₃ then 2
              else if a₃ = a₁ ∨ a₃ = a₂ ∨ a₃ = a₃ then 1 else 0) ≥ 1
            rw [if_neg ha₃_nv]
            by_cases h : a₃ = n₁ ∨ a₃ = n₂ ∨ a₃ = n₃
            · rw [if_pos h]; omega
            · rw [if_neg h, if_pos (show a₃ = a₁ ∨ a₃ = a₂ ∨ a₃ = a₃ from Or.inr (Or.inr rfl))]
          linarith
        rw [hxn3]; linarith
      · 
        by_cases ha₁_in_n : a₁ = n₁ ∨ a₁ = n₂ ∨ a₁ = n₃
        · 
          have ha₁v : adj a₁ v = 1 := by
            rcases ha₁_in_n with hi | hi | hi
            · exact absurd hi ha₁_nn
            · rw [hi, hsymm.apply v n₂]; exact hn₂_adj
            · rw [hi, hsymm.apply v n₃]; exact hn₃_adj
          have hS_pair : ({n₁, v} : Finset _).sum (fun j => adj a₁ j * x j) ≤
              ∑ j : Fin n, adj a₁ j * x j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hadj_x_nn a₁ j)
          rw [Finset.sum_pair hv_ne1, ha_a1n1, ha₁v, one_mul, one_mul, hxn1, hxv] at hS_pair
          have hxa : x a₁ = 2 := by simp only [x]; rw [if_neg ha₁_nv, if_pos ha₁_in_n]
          linarith
        · 
          have hS : adj a₁ n₁ * x n₁ ≤ ∑ j : Fin n, adj a₁ j * x j :=
            Finset.single_le_sum (fun j _ => hadj_x_nn a₁ j) (Finset.mem_univ n₁)
          rw [ha_a1n1, one_mul, hxn1] at hS
          have hxa : x a₁ ≤ 1 := by
            simp only [x]; rw [if_neg ha₁_nv, if_neg ha₁_in_n]; omega
          linarith
      · 
        by_cases ha₂_in_n : a₂ = n₁ ∨ a₂ = n₂ ∨ a₂ = n₃
        · have ha₂v : adj a₂ v = 1 := by
            rcases ha₂_in_n with hi | hi | hi
            · rw [hi, hsymm.apply v n₁]; exact hn₁_adj
            · exact absurd hi ha₂_nn
            · rw [hi, hsymm.apply v n₃]; exact hn₃_adj
          have hS_pair : ({n₂, v} : Finset _).sum (fun j => adj a₂ j * x j) ≤
              ∑ j : Fin n, adj a₂ j * x j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hadj_x_nn a₂ j)
          rw [Finset.sum_pair hv_ne2, ha_a2n2, ha₂v, one_mul, one_mul, hxn2, hxv] at hS_pair
          have hxa : x a₂ = 2 := by simp only [x]; rw [if_neg ha₂_nv, if_pos ha₂_in_n]
          linarith
        · have hS : adj a₂ n₂ * x n₂ ≤ ∑ j : Fin n, adj a₂ j * x j :=
            Finset.single_le_sum (fun j _ => hadj_x_nn a₂ j) (Finset.mem_univ n₂)
          rw [ha_a2n2, one_mul, hxn2] at hS
          have hxa : x a₂ ≤ 1 := by
            simp only [x]; rw [if_neg ha₂_nv, if_neg ha₂_in_n]; omega
          linarith
      · 
        by_cases ha₃_in_n : a₃ = n₁ ∨ a₃ = n₂ ∨ a₃ = n₃
        · have ha₃v : adj a₃ v = 1 := by
            rcases ha₃_in_n with hi | hi | hi
            · rw [hi, hsymm.apply v n₁]; exact hn₁_adj
            · rw [hi, hsymm.apply v n₂]; exact hn₂_adj
            · exact absurd hi ha₃_nn
          have hS_pair : ({n₃, v} : Finset _).sum (fun j => adj a₃ j * x j) ≤
              ∑ j : Fin n, adj a₃ j * x j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => hadj_x_nn a₃ j)
          rw [Finset.sum_pair hv_ne3, ha_a3n3, ha₃v, one_mul, one_mul, hxn3, hxv] at hS_pair
          have hxa : x a₃ = 2 := by simp only [x]; rw [if_neg ha₃_nv, if_pos ha₃_in_n]
          linarith
        · have hS : adj a₃ n₃ * x n₃ ≤ ∑ j : Fin n, adj a₃ j * x j :=
            Finset.single_le_sum (fun j _ => hadj_x_nn a₃ j) (Finset.mem_univ n₃)
          rw [ha_a3n3, one_mul, hxn3] at hS
          have hxa : x a₃ ≤ 1 := by
            simp only [x]; rw [if_neg ha₃_nv, if_neg ha₃_in_n]; omega
          linarith
  linarith [hpos x hx_ne]



private lemma star_adj_of_deg3_n4 {adj : Matrix (Fin 4) (Fin 4) ℤ}
    (hD : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 4 adj) (v : Fin 4) (hv : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj v = 3) :
    ∀ i j : Fin 4, adj i j = if (i = v) = (j = v) then 0 else 1 := by
  have hsymm := hD.1
  have hdiag := hD.2.1
  have h01 := hD.2.2.1
  
  have hadj_v : ∀ j, j ≠ v → adj v j = 1 := by
    intro j hj
    have hsub : Finset.univ.filter (fun j => adj v j = 1) ⊆ Finset.univ.erase v := by
      intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_erase.mpr ⟨fun h => by rw [h] at hx; linarith [hdiag v], Finset.mem_univ _⟩
    have hcard : (Finset.univ.erase v).card ≤ (Finset.univ.filter (fun j => adj v j = 1)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount at hv; omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : j ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
    rw [← heq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  
  have hno_edge : ∀ i j : Fin 4, i ≠ v → j ≠ v → i ≠ j → adj i j = 0 := by
    intro i j hi hj hij
    rcases h01 i j with h | h
    · exact h
    · 
      exfalso
      have hedge := RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.edgeCount_eq_card_sub_one hD (by omega)
      unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.edgeCount at hedge
      have hdeg_i : 2 ≤ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj i := by
        change 2 ≤ (Finset.univ.filter (fun k => adj i k = 1)).card
        have hv_mem : v ∈ Finset.univ.filter (fun k => adj i k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply i v ▸ hadj_v i hi⟩
        have hj_mem : j ∈ Finset.univ.filter (fun k => adj i k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        have hne : v ≠ j := Ne.symm hj
        exact Finset.one_lt_card.mpr ⟨v, hv_mem, j, hj_mem, hne⟩
      have hdeg_j : 2 ≤ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj j := by
        change 2 ≤ (Finset.univ.filter (fun k => adj j k = 1)).card
        have hv_mem : v ∈ Finset.univ.filter (fun k => adj j k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply j v ▸ hadj_v j hj⟩
        have hi_mem : i ∈ Finset.univ.filter (fun k => adj j k = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply j i ▸ h⟩
        have hne : v ≠ i := Ne.symm hi
        exact Finset.one_lt_card.mpr ⟨v, hv_mem, i, hi_mem, hne⟩
      have hsum_ge : 8 ≤ ∑ k : Fin 4, RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj k := by
        have hv_sum := Finset.add_sum_erase Finset.univ (fun k => RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj k) (Finset.mem_univ v)
        have hi_sum := Finset.add_sum_erase (Finset.univ.erase v) (fun k => RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj k)
          (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
        have hj_mem : j ∈ (Finset.univ.erase v).erase i :=
          Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
        have hj_sum := Finset.add_sum_erase ((Finset.univ.erase v).erase i) (fun k => RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj k) hj_mem
        have hrest_ge : ∀ k ∈ ((Finset.univ.erase v).erase i).erase j, 1 ≤ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj k := by
          intro k hk
          have hkv : k ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2).1
          change 1 ≤ (Finset.univ.filter (fun m => adj k m = 1)).card
          exact Finset.one_le_card.mpr ⟨v, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hsymm.apply k v ▸ hadj_v k hkv⟩⟩
        have hrest_nonempty : (((Finset.univ.erase v).erase i).erase j).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro h
          have := Finset.card_eq_zero.mpr h
          simp [Finset.card_erase_of_mem, hj_mem,
            Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩] at this
        obtain ⟨k, hk⟩ := hrest_nonempty
        have hk_le := Finset.single_le_sum (fun x _ => Nat.zero_le (RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj x)) hk
        linarith [hrest_ge k hk]
      omega
  
  intro i j
  by_cases hiv : i = v <;> by_cases hjv : j = v
  · 
    have : (i = v) = (j = v) := by simp [hiv, hjv]
    simp only [ite_true, hiv, hjv, hdiag]
  · 
    simp only [hiv, hjv]; exact hadj_v j hjv
  · 
    simp only [hjv, eq_true, hiv]
    exact hsymm.apply i v ▸ hadj_v i hiv
  · 
    have : (i = v) = (j = v) := by rw [eq_false hiv, eq_false hjv]
    simp only [this, ite_true]
    by_cases hij : i = j
    · simp [hij, hdiag]
    · exact hno_edge i j hiv hjv hij


private lemma branch_classification_n4 {adj : Matrix (Fin 4) (Fin 4) ℤ}
    (hD : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 4 adj) (v : Fin 4) (hv : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj v = 3) :
    ∃ t : RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel, ∃ σ : Fin t.rank ≃ Fin 4,
      ∀ i j, adj (σ i) (σ j) = t.matrix i j := by
  have hstar := star_adj_of_deg3_n4 hD v hv
  
  
  set σ : Fin 4 ≃ Fin 4 := Equiv.swap (⟨1, by omega⟩ : Fin 4) v
  refine ⟨.D 4 (by omega), σ, fun i j => ?_⟩
  
  have hi := i.isLt; have hj := j.isLt
  change _ < 4 at hi hj
  change adj (σ ⟨i.val, by omega⟩) (σ ⟨j.val, by omega⟩) = _
  rw [hstar]
  have hσ_eq_v : ∀ x : Fin 4, σ x = v ↔ x = ⟨1, by omega⟩ := by
    intro x; constructor
    · intro h; exact σ.injective (h.trans (Equiv.swap_apply_left _ _).symm)
    · intro h; subst h; exact Equiv.swap_apply_left _ _
  simp only [hσ_eq_v]
  simp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.rank, Fin.ext_iff]
  split_ifs with h <;> simp_all <;> omega







/-- A symmetric binary adjacency matrix obtained by attaching a uniquely adjacent vertex to a relabeled path is equivalent, up to reversing the path, to the corresponding standard adjacency matrix. -/
lemma Matrix.exists_relabeling_of_erase_leaf_path_relabeling {k : ℕ} {adj : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ}
    (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (u : Fin (k + 1)) (v' : Fin k)
    (adj' : Matrix (Fin k) (Fin k) ℤ)
    (hadj'_def : adj' = fun i j => adj (u.succAbove i) (u.succAbove j))
    (hu_adj : adj u (u.succAbove v') = 1)
    (hu_unique : ∀ w, adj u w = 1 → w = u.succAbove v')
    (σ' : Fin k ≃ Fin k)
    (hσ'_fwd : ∀ (m : Fin k) (hm : m.val + 1 < k),
      adj' (σ' m) (σ' ⟨m.val + 1, hm⟩) = 1)
    (hσ'_only : ∀ i j, adj' (σ' i) (σ' j) = 1 →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (b : ℕ) (hb_lt : b < k) (hσ'_b : σ' ⟨b, hb_lt⟩ = v')
    (t_adj : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (b_std : ℕ) (hb_std_lt : b_std < k)
    (hb_match : b = b_std ∨ b = k - 1 - b_std)
    (ht_path : ∀ (i j : Fin (k + 1)), i.val < k → j.val < k →
      t_adj i j = if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0)
    (ht_branch : ∀ (i : Fin (k + 1)), i.val < k →
      t_adj i ⟨k, by omega⟩ = if i.val = b_std then 1 else 0)
    (ht_branch_symm : ∀ (i : Fin (k + 1)), i.val < k →
      t_adj ⟨k, by omega⟩ i = if i.val = b_std then 1 else 0)
    (ht_diag_k : t_adj ⟨k, by omega⟩ ⟨k, by omega⟩ = 0) :
    ∃ σ : Fin (k + 1) ≃ Fin (k + 1),
      ∀ i j, adj (σ i) (σ j) = t_adj i j := by
  have hk_pos : 0 < k := by omega
  
  have hadj'_symm : ∀ i j : Fin k, adj' i j = adj' j i := by
    intro i j; simp only [hadj'_def]; exact hsymm.apply _ _
  
  have hσ'_iff : ∀ (i j : Fin k), adj' (σ' i) (σ' j) = 1 ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro i j; constructor
    · exact hσ'_only i j
    · rintro (h1 | h2)
      · have hlt : i.val + 1 < k := h1 ▸ j.isLt
        rw [show j = ⟨i.val + 1, hlt⟩ from Fin.ext h1.symm]
        exact hσ'_fwd i hlt
      · have hlt : j.val + 1 < k := h2 ▸ i.isLt
        rw [show i = ⟨j.val + 1, hlt⟩ from Fin.ext h2.symm]
        rw [hadj'_symm]; exact hσ'_fwd j hlt
  
  
  let revK : Fin k ≃ Fin k :=
    ⟨fun i => ⟨k - 1 - i.val, by omega⟩,
     fun i => ⟨k - 1 - i.val, by omega⟩,
     fun i => Fin.ext (by simp; omega),
     fun i => Fin.ext (by simp; omega)⟩
  let maybeRevEquiv : Fin k ≃ Fin k :=
    if b = b_std then Equiv.refl _ else revK
  have hMR_b : maybeRevEquiv ⟨b_std, hb_std_lt⟩ = ⟨b, hb_lt⟩ := by
    simp only [maybeRevEquiv]
    split_ifs with h
    · exact Fin.ext h.symm
    · rcases hb_match with rfl | hrev
      · exact absurd rfl h
      · apply Fin.ext; change k - 1 - b_std = b; omega
  have hMR_consec : ∀ (i j : Fin k),
      (maybeRevEquiv i).val + 1 = (maybeRevEquiv j).val ∨
        (maybeRevEquiv j).val + 1 = (maybeRevEquiv i).val ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
    intro i j; simp only [maybeRevEquiv]
    split_ifs with h
    · simp [Equiv.refl_apply]
    · change (k - 1 - i.val) + 1 = (k - 1 - j.val) ∨
           (k - 1 - j.val) + 1 = (k - 1 - i.val) ↔
           i.val + 1 = j.val ∨ j.val + 1 = i.val
      have hi := i.isLt; have hj := j.isLt
      constructor <;> (intro hc; omega)
  
  let σ₀ : Fin k ≃ Fin k := maybeRevEquiv.trans σ'
  have hσ₀_apply : ∀ i, σ₀ i = σ' (maybeRevEquiv i) := fun _ => rfl
  
  have hσ₀_b : σ₀ ⟨b_std, by omega⟩ = v' := by
    rw [hσ₀_apply, hMR_b]; exact hσ'_b
  
  have hσ₀_iff : ∀ (i j : Fin k), adj' (σ₀ i) (σ₀ j) = 1 ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro i j; rw [hσ₀_apply, hσ₀_apply, hσ'_iff]; exact hMR_consec i j
  
  have hadj'_apply : ∀ (a b : Fin k),
      adj' a b = adj (u.succAbove a) (u.succAbove b) :=
    fun a b => congrFun (congrFun hadj'_def a) b
  
  have hadj_σ₀ : ∀ (i j : Fin k),
      adj (u.succAbove (σ₀ i)) (u.succAbove (σ₀ j)) =
      if (i.val + 1 = j.val ∨ j.val + 1 = i.val)
        then 1 else 0 := by
    intro i j; rw [← hadj'_apply]
    by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos h]; exact (hσ₀_iff i j).mpr h
    · rw [if_neg h]
      rcases h01 (u.succAbove (σ₀ i)) (u.succAbove (σ₀ j))
        with h0 | h1
      · rwa [← hadj'_apply] at h0
      · rw [← hadj'_apply] at h1
        exact absurd ((hσ₀_iff i j).mp h1) h
  
  have hadj_branch : ∀ (i : Fin k),
      adj (u.succAbove (σ₀ i)) u =
        if i.val = b_std then 1 else 0 := by
    intro i; split_ifs with h
    · have hi : i = ⟨b_std, by omega⟩ := by ext; exact h
      rw [hi, hσ₀_b]
      rw [hsymm.apply]; exact hu_adj
    · have hne : σ₀ i ≠ v' := by
        intro heq; apply h
        have := σ₀.injective (heq.trans hσ₀_b.symm)
        exact congrArg Fin.val this
      rcases h01 (u.succAbove (σ₀ i)) u with h0 | h1
      · exact h0
      · rw [hsymm.apply] at h1
        exact absurd (Fin.succAbove_right_injective
          (hu_unique _ h1)) hne
  
  let fwd : Fin (k + 1) → Fin (k + 1) := fun i =>
    if h : i.val < k then u.succAbove (σ₀ ⟨i.val, h⟩) else u
  
  have fwd_inj : Function.Injective fwd := by
    intro i j hij; simp only [fwd] at hij
    by_cases hi : i.val < k <;> by_cases hj : j.val < k
    · rw [dif_pos hi, dif_pos hj] at hij
      have h1 := Fin.succAbove_right_injective hij
      have h2 := σ₀.injective h1
      have h3 : i.val = j.val := by
        rw [Fin.mk.injEq] at h2; exact h2
      exact Fin.ext h3
    · rw [dif_pos hi, dif_neg hj] at hij
      exact absurd hij (Fin.succAbove_ne u _)
    · rw [dif_neg hi, dif_pos hj] at hij
      exact absurd hij.symm (Fin.succAbove_ne u _)
    · exact Fin.ext (by omega)
  
  let σ : Fin (k + 1) ≃ Fin (k + 1) :=
    Equiv.ofBijective fwd
      ((Finite.injective_iff_bijective).mp fwd_inj)
  refine ⟨σ, fun i j => ?_⟩
  
  change adj (fwd i) (fwd j) = t_adj i j
  simp only [fwd]
  by_cases hi : i.val < k <;> by_cases hj : j.val < k
  · 
    rw [dif_pos hi, dif_pos hj, hadj_σ₀, ht_path i j hi hj]
  · 
    rw [dif_pos hi, dif_neg hj]
    have hj_val : j.val = k := by have := j.isLt; omega
    have hj_eq : j = ⟨k, by omega⟩ := Fin.ext hj_val
    rw [hj_eq, ht_branch _ hi, hadj_branch]
  · 
    rw [dif_neg hi, dif_pos hj]
    have hi_val : i.val = k := by have := i.isLt; omega
    have hi_eq : i = ⟨k, by omega⟩ := Fin.ext hi_val
    rw [hi_eq, ht_branch_symm _ hj, hsymm.apply, hadj_branch]
  · 
    have hi_val : i.val = k := by have := i.isLt; omega
    have hj_val : j.val = k := by have := j.isLt; omega
    have hi_eq : i = ⟨k, by omega⟩ := Fin.ext hi_val
    have hj_eq : j = ⟨k, by omega⟩ := Fin.ext hj_val
    rw [dif_neg hi, dif_neg hj, hi_eq, hj_eq, ht_diag_k, hdiag]



set_option maxHeartbeats 400000 in




/-- A nonempty adjacency matrix satisfying the specified condition admits the required finite-model reindexing when its associated vertex-valued function takes the value three. -/
lemma Matrix.exists_adjacency_reindexing_of_exists_vertex_value_eq_three {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (hn : 1 ≤ n)
    (hbranch : ∃ i, RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj i = 3) :
    ∃ t : RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.matrix i j := by
  obtain ⟨v, hv⟩ := hbranch
  
  have hn4 : 4 ≤ n := by
    obtain ⟨_, hdiag, _, _, _⟩ := hD
    by_contra h; push Not at h
    have : (Finset.univ.filter (fun j => adj v j = 1)).card ≤
        (Finset.univ.erase v).card := by
      apply Finset.card_le_card
      intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_erase.mpr ⟨fun h' => by subst h'; linarith [hdiag x], Finset.mem_univ _⟩
    simp [Finset.card_erase_of_mem] at this
    change RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj v ≤ n - 1 at this
    omega
  
  by_cases hn4e : n = 4
  · subst hn4e; exact branch_classification_n4 hD v hv
  · 
    have hn5 : 5 ≤ n := by omega
    
    obtain ⟨u, hu_adj, hu_deg⟩ := Matrix.exists_entry_one_and_vertex_value_one_of_vertex_value_three hD v hv
    obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
    have hu_ne : u ≠ v := by
      intro h; subst h; rw [hdiag] at hu_adj; omega
    
    have hu_unique : ∀ w, adj u w = 1 → w = v := by
      intro w hw
      by_contra hne_w
      have : 2 ≤ RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj u := by
        change 2 ≤ (Finset.univ.filter (fun j => adj u j = 1)).card
        have hv_mem : v ∈ Finset.univ.filter (fun j => adj u j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply u v ▸ hu_adj⟩
        have hw_mem : w ∈ Finset.univ.filter (fun j => adj u j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        calc 2 = ({v, w} : Finset _).card := by rw [Finset.card_pair (Ne.symm hne_w)]
          _ ≤ _ := Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hv_mem
            · exact hw_mem)
      omega
    
    have hn2 : 2 ≤ n := by omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk1 : 1 ≤ k := by omega
    set adj' : Matrix (Fin k) (Fin k) ℤ :=
      fun i j => adj (u.succAbove i) (u.succAbove j) with hadj'_def
    
    have hD' : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix k adj' := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact Matrix.IsSymm.ext (fun i j => hsymm.apply _ _)
      · intro i; exact hdiag _
      · intro i j; exact h01 _ _
      · 
        let G : SimpleGraph (Fin (k + 1)) :=
          { Adj := fun i j => adj i j = 1
            
            symm := ⟨fun i j (h : adj i j = 1) => (hsymm.apply i j).trans h⟩
            loopless := ⟨fun i (h : adj i i = 1) => by linarith [hdiag i]⟩ }
        haveI : DecidableRel G.Adj :=
          fun i j => show Decidable (adj i j = 1) from inferInstance
        have hG_conn : G.Connected := by
          constructor
          intro a b
          obtain ⟨path, hhead, hlast, hedges⟩ := hconn a b
          exact RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.reachable_of_list_path G path a b hhead hlast (fun k hk => hedges k hk)
        have hG_deg : G.degree u = 1 := by
          unfold SimpleGraph.degree
          have heq : G.neighborFinset u = Finset.univ.filter (adj u · = 1) := by
            ext j; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
              Finset.mem_univ, true_and]; exact ⟨fun h => h, fun h => h⟩
          rw [heq]; unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount at hu_deg; convert hu_deg
        have hG' := hG_conn.induce_compl_singleton_of_degree_eq_one hG_deg
        intro a b
        have ha_ne : u.succAbove a ≠ u := Fin.succAbove_ne u a
        have hb_ne : u.succAbove b ≠ u := Fin.succAbove_ne u b
        have ha_mem : u.succAbove a ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
          Set.mem_compl_singleton_iff.mpr ha_ne
        have hb_mem : u.succAbove b ∈ ({u}ᶜ : Set (Fin (k + 1))) :=
          Set.mem_compl_singleton_iff.mpr hb_ne
        obtain ⟨walk⟩ := hG'.preconnected ⟨u.succAbove a, ha_mem⟩ ⟨u.succAbove b, hb_mem⟩
        let toFink : ↥({u}ᶜ : Set (Fin (k + 1))) → Fin k :=
          fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq
            (Set.mem_compl_singleton_iff.mp hx)).choose
        have htoFink_spec : ∀ (x : ↥({u}ᶜ : Set (Fin (k + 1)))),
            u.succAbove (toFink x) = x.val :=
          fun ⟨x, hx⟩ => (Fin.exists_succAbove_eq
            (Set.mem_compl_singleton_iff.mp hx)).choose_spec
        have htoFink_adj : ∀ (x y : ↥({u}ᶜ : Set (Fin (k + 1)))),
            (G.induce ({u}ᶜ : Set _)).Adj x y →
            adj' (toFink x) (toFink y) = 1 := by
          intro x y hadj_xy
          simp only [hadj'_def, SimpleGraph.induce_adj] at hadj_xy ⊢
          rw [htoFink_spec x, htoFink_spec y]; exact hadj_xy
        suffices h_walk : ∀ (a b : ↥({u}ᶜ : Set (Fin (k+1))))
            (w' : (G.induce ({u}ᶜ : Set _)).Walk a b),
          ∃ path : List (Fin k),
            path.head? = some (toFink a) ∧
            path.getLast? = some (toFink b) ∧
            ∀ m, (hm : m + 1 < path.length) →
              adj' (path.get ⟨m, by omega⟩) (path.get ⟨m + 1, hm⟩) = 1 by
          obtain ⟨path, hhead, hlast, hedges⟩ := h_walk _ _ walk
          refine ⟨path, ?_, ?_, hedges⟩
          · convert hhead using 2
            exact (Fin.succAbove_right_injective
              (htoFink_spec ⟨u.succAbove a, ha_mem⟩)).symm
          · convert hlast using 2
            exact (Fin.succAbove_right_injective
              (htoFink_spec ⟨u.succAbove b, hb_mem⟩)).symm
        intro a b w'
        induction w' with
        | nil =>
          exact ⟨[toFink _], rfl, rfl, fun m hm => absurd hm (by simp)⟩
        | @cons c d _ hadj_edge rest ih =>
          obtain ⟨path_rest, hhead_rest, hlast_rest, hedges_rest⟩ := ih
          refine ⟨toFink c :: path_rest, by simp, ?_, ?_⟩
          · cases path_rest with
            | nil => simp at hhead_rest hlast_rest ⊢
            | cons y ys => simp only [List.getLast?_cons_cons]; exact hlast_rest
          · intro m hm
            match m with
            | 0 =>
              simp only [List.get_eq_getElem, List.getElem_cons_zero,
                List.getElem_cons_succ]
              have h0 : 0 < path_rest.length := by
                simp only [List.length_cons] at hm; omega
              have hd_eq : path_rest[0] = toFink d := by
                cases path_rest with
                | nil => simp at h0
                | cons y ys =>
                  simp only [List.head?, Option.some.injEq] at hhead_rest
                  simp only [List.getElem_cons_zero]; exact hhead_rest
              rw [hd_eq]; exact htoFink_adj c d hadj_edge
            | m' + 1 =>
              simp only [List.get_eq_getElem, List.getElem_cons_succ]
              exact hedges_rest m' (by simp only [List.length_cons] at hm; omega)
      · 
        intro x hx
        set x' : Fin (k + 1) → ℤ := fun a =>
          if h : a = u then 0 else x (Fin.exists_succAbove_eq h).choose
        have hx'_u : x' u = 0 := by simp [x']
        have hx'_sa : ∀ i, x' (u.succAbove i) = x i := by
          intro i; simp only [x']
          rw [dif_neg (Fin.succAbove_ne u i)]; congr 1
          exact Fin.succAbove_right_injective
            (Fin.exists_succAbove_eq (Fin.succAbove_ne u i)).choose_spec
        have hx'_ne : x' ≠ 0 := by
          intro heq; apply hx; ext b
          have := congr_fun heq (u.succAbove b)
          rw [hx'_sa, Pi.zero_apply] at this; exact this
        have hB_eq : dotProduct x' ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x') =
            dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj').mulVec x) := by
          simp only [dotProduct, Matrix.mulVec]
          conv_lhs => rw [Fin.sum_univ_succAbove _ u]
          simp only [hx'_u, zero_mul, zero_add]
          congr 1; ext i; rw [hx'_sa]; congr 1
          conv_lhs => rw [Fin.sum_univ_succAbove _ u]
          simp only [hx'_u, mul_zero, zero_add]
          congr 1; ext j; rw [hx'_sa]; congr 1
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hadj'_def,
            Fin.succAbove_right_inj]
        linarith [hpos x' hx'_ne]
    
    have hpath' : ∀ i, RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj' i ≤ 2 := by
      intro i
      unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount
      have h_image : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image u.succAbove)
          ⊆ Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨y, hy, rfl⟩ := hx; exact hy
      have h_card := Finset.card_le_card h_image
      rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card
      have hD_full : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix (k + 1) adj := ⟨hsymm, hdiag, h01, hconn, hpos⟩
      have hdeg_le3 := RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount_le_three hD_full (u.succAbove i)
      unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount at hdeg_le3
      by_cases hdeg3 : (Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1)).card = 3
      · have hvi : u.succAbove i = v :=
          Matrix.vertex_eq_of_values_eq_three hD_full (u.succAbove i) v (by unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount; exact hdeg3) hv
        have h_image2 : ((Finset.univ.filter (fun j : Fin k => adj' i j = 1)).image u.succAbove)
            ⊆ (Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1)).erase u := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          refine Finset.mem_erase.mpr ⟨Fin.succAbove_ne u y, ?_⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hvi]; exact hy
        have h_card2 := Finset.card_le_card h_image2
        rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective] at h_card2
        have hu_mem : u ∈ Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_adj⟩
        rw [Finset.card_erase_of_mem hu_mem] at h_card2
        have hv3 : (Finset.univ.filter (fun j : Fin (k + 1) => adj v j = 1)).card = 3 := hv
        omega
      · have : (Finset.univ.filter (fun j : Fin (k + 1) => adj (u.succAbove i) j = 1)).card ≤ 2 := by
          omega
        linarith
    
    obtain ⟨v₀', hv₀'_deg⟩ :=
      RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.exists_neighborCount_le_one
        hD' hk1 hpath'
    obtain ⟨σ', hσ'0, hσ'_fwd, hσ'_only⟩ :=
      RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.exists_pathLabeling_from_endpoint hD' hk1 hpath' v₀' hv₀'_deg
    
    have hv_ne_u : v ≠ u := Ne.symm hu_ne
    obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq hv_ne_u
    set bfin := σ'.symm v' with hbfin_def
    set b := bfin.val with hb_def
    have hb_lt : b < k := bfin.isLt
    have hσ'_b : σ' bfin = v' := σ'.apply_symm_apply v'
    have hv'_deg2 : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj' v' = 2 := by
      apply le_antisymm (hpath' v')
      unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount
      set Nv := Finset.univ.filter (fun j => adj v j = 1) with hNv_def
      have hNv_card : Nv.card = 3 := hv
      have hu_mem : u ∈ Nv :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsymm.apply v u ▸ hu_adj⟩
      have hNv_erase : (Nv.erase u).card = 2 := by
        rw [Finset.card_erase_of_mem hu_mem]; omega
      suffices h : 2 ≤ (Finset.univ.filter (fun j : Fin k => adj' v' j = 1)).card from h
      have h_image : ∀ w ∈ Nv.erase u, ∃ w' : Fin k,
          u.succAbove w' = w ∧ adj' v' w' = 1 := by
        intro w hw
        have hw_mem : w ∈ Nv := Finset.mem_of_mem_erase hw
        have hw_ne : w ≠ u := Finset.ne_of_mem_erase hw
        obtain ⟨w', hw'⟩ := Fin.exists_succAbove_eq hw_ne
        refine ⟨w', hw', ?_⟩
        change adj (u.succAbove v') (u.succAbove w') = 1
        rw [hv', hw']
        exact (Finset.mem_filter.mp hw_mem).2
      obtain ⟨a₁, a₂, ha_ne, ha_cover⟩ :=
        Finset.card_eq_two.mp hNv_erase
      have ha₁_mem : a₁ ∈ Nv.erase u := ha_cover ▸ Finset.mem_insert_self _ _
      have ha₂_mem : a₂ ∈ Nv.erase u :=
        ha_cover ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      obtain ⟨w₁, hw₁_eq, hw₁_adj⟩ := h_image a₁ ha₁_mem
      obtain ⟨w₂, hw₂_eq, hw₂_adj⟩ := h_image a₂ ha₂_mem
      have hne : w₁ ≠ w₂ := by
        intro h; apply ha_ne
        have := congr_arg u.succAbove h
        rw [hw₁_eq, hw₂_eq] at this; exact this
      calc 2 = ({w₁, w₂} : Finset _).card := (Finset.card_pair hne).symm
        _ ≤ (Finset.univ.filter (fun j : Fin k => adj' v' j = 1)).card :=
          Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by rcases hx with rfl | rfl
                 · exact hw₁_adj
                 · exact hw₂_adj⟩)
    have hb_pos : 0 < b := by
      by_contra h; push Not at h; have hb0 : b = 0 := by omega
      have hv'_eq : v' = v₀' := by
        have hbf0 : bfin = ⟨0, by omega⟩ := Fin.ext hb0
        have h1 : σ' bfin = v' := hσ'_b
        rw [hbf0] at h1
        exact h1.symm.trans hσ'0
      linarith [hv'_eq ▸ hv₀'_deg]
    have hb_lt_k1 : b < k - 1 := by
      by_contra h; push Not at h; have hbk : b = k - 1 := by omega
      have hdeg_le1 : RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj' v' ≤ 1 := by
        unfold RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount
        suffices h : (Finset.univ.filter
            (fun j : Fin k => adj' v' j = 1)).card ≤ 1 from h
        rw [show (1 : ℕ) = ({σ' ⟨k - 2, by omega⟩} : Finset _).card from by simp]
        apply Finset.card_le_card
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        simp only [Finset.mem_singleton]
        set wfin := σ'.symm w
        have hw_eq : σ' wfin = w := σ'.apply_symm_apply w
        rw [← hσ'_b, ← hw_eq] at hw
        have := hσ'_only bfin wfin hw
        rcases this with h1 | h2
        · exfalso; have := wfin.isLt
          change b + 1 = wfin.val at h1; omega
        · rw [← hw_eq]; congr 1
          apply Fin.ext; change wfin.val = k - 2
          change wfin.val + 1 = b at h2; omega
      linarith
    
    set q := min b (k - 1 - b) with hq_def
    set r := max b (k - 1 - b) with hr_def
    have hpq : 1 ≤ q := by
      simp only [q]; exact Nat.one_le_iff_ne_zero.mpr (by omega)
    have hqr : q ≤ r := by simp only [q, r]; omega
    have hn_eq : k + 1 = 1 + q + r + 1 := by
      simp only [q, r, min_def, max_def]
      split_ifs <;> omega
    have hrecip : (q + 1) * (r + 1) + 2 * (r + 1) + 2 * (q + 1) >
                  2 * (q + 1) * (r + 1) := by
      
      
      
      suffices h : 2 * (b + 1) + 2 * (k - b) > (b + 1) * (k - b) by
        have hprod : (q + 1) * (r + 1) = (b + 1) * (k - b) := by
          simp only [q, r, min_def, max_def]
          split_ifs with hle
          · congr 1; omega
          · rw [Nat.mul_comm]; congr 1; omega
        have hsum : 2 * (r + 1) + 2 * (q + 1) = 2 * (b + 1) + 2 * (k - b) := by
          simp only [q, r, min_def, max_def]; split_ifs <;> omega
        linarith
      
      set f : ℕ → ℤ := fun m =>
        if m ≤ b then 2 * (↑(k - b) : ℤ) * (↑m + 1)
        else 2 * (↑(b + 1) : ℤ) * (↑k - ↑m) with hf_def
      set y : Fin k → ℤ := fun i => f (σ'.symm i).val with hy_def
      set xu : ℤ := (↑(b + 1) : ℤ) * ↑(k - b) with hxu_def
      
      set x : Fin (k + 1) → ℤ := fun w =>
        if h : w = u then xu
        else y ((Fin.exists_succAbove_eq h).choose) with hx_def
      have hx_u : x u = xu := by simp [hx_def]
      have hx_sa : ∀ i, x (u.succAbove i) = y i := by
        intro i; simp only [hx_def, Fin.succAbove_ne u i, dite_false]
        congr 1; exact Fin.succAbove_right_injective
          (Fin.exists_succAbove_eq (Fin.succAbove_ne u i)).choose_spec
      
      have hy_at : ∀ (m : ℕ) (hm : m < k), y (σ' ⟨m, hm⟩) = f m := by
        intro m hm; simp only [hy_def, Equiv.symm_apply_apply]
      
      have hfb : f b = 2 * ↑(k - b) * (↑b + 1) := by simp [hf_def]
      have hxv : x v = f b := by
        change x v = f (σ'.symm v').val
        have : x v = x (u.succAbove v') := by rw [hv']
        rw [this, hx_sa]
      
      have hx_ne : x ≠ 0 := by
        intro heq; have := congr_fun heq u; rw [hx_u, Pi.zero_apply] at this
        simp [hxu_def] at this; omega
      
      have hBpos := hpos x hx_ne
      
      have hx_nonneg : ∀ i, 0 ≤ x i := by
        intro i
        by_cases hi : i = u
        · rw [hi, hx_u]; positivity
        · have ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
          rw [← hj, hx_sa]; simp only [hy_def]
          set m := (σ'.symm j).val
          simp only [hf_def]
          split_ifs with hle
          · have : (m : ℤ) ≥ 0 := Int.natCast_nonneg m; positivity
          · push Not at hle
            have hm_lt : m < k := (σ'.symm j).isLt
            have : (k : ℤ) - ↑m > 0 := by omega
            positivity
      
      
      
      
      
      
      
      
      have hadj'_char : ∀ i j : Fin k, adj' (σ' i) (σ' j) =
          if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0 := by
        intro i j
        by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
        · rw [if_pos h]
          rcases h with h | h
          · have hj : j = ⟨i.val + 1, by omega⟩ := Fin.ext (by simp; omega)
            rw [hj]; exact hσ'_fwd i (by omega)
          · have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by simp; omega)
            rw [hi]
            have hsymm' : adj'.IsSymm :=
              Matrix.IsSymm.ext (fun a c => hsymm.apply _ _)
            rw [hsymm'.apply]; exact hσ'_fwd j (by omega)
        · rw [if_neg h]
          rcases h01 (u.succAbove (σ' i)) (u.succAbove (σ' j)) with h0 | h1
          · exact h0
          · exfalso; exact h (hσ'_only i j h1)
      
      have hadj_u_path : ∀ m : Fin k,
          adj u (u.succAbove (σ' m)) = if (σ' m = v') then 1 else 0 := by
        intro m
        by_cases hm : σ' m = v'
        · rw [if_pos hm, hm, hv', hsymm.apply]; exact hu_adj
        · rw [if_neg hm]
          rcases h01 u (u.succAbove (σ' m)) with h0 | h1
          · exact h0
          · exfalso
            have hv_eq := hu_unique _ h1
            have : u.succAbove (σ' m) = v := hv_eq
            rw [← hv'] at this
            exact hm (Fin.succAbove_right_injective this)
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      have hfb_pos : (0 : ℤ) < f b := by
        rw [hfb]
        have : (0 : ℤ) < ↑(k - b) := by omega
        have : (0 : ℤ) < ↑b + 1 := by omega
        nlinarith
      suffices hB_eq : dotProduct x ((2 • (1 : Matrix _ _ ℤ) - adj).mulVec x) =
          f b * (2 * (↑(b + 1) : ℤ) + 2 * (↑(k - b) : ℤ) -
                 (↑(b + 1) : ℤ) * ↑(k - b)) by
        rw [hB_eq] at hBpos
        have hbracket_pos : 0 < 2 * (↑(b + 1) : ℤ) + 2 * ↑(k - b) -
            (↑(b + 1) : ℤ) * ↑(k - b) := by
          rcases mul_pos_iff.mp hBpos with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact h2
          · linarith
        zify at *; linarith
      
      
      
      have hxu_val : xu = (↑(b + 1) : ℤ) * ↑(k - b) := rfl
      have hfb_eq_2xu : f b = 2 * xu := by rw [hfb, hxu_val]; push_cast; ring
      
      have hsmul_ite : ∀ (i j : Fin (k + 1)),
          (2 : ℕ) • (if i = j then (1 : ℤ) else 0) = if i = j then (2 : ℤ) else 0 := by
        intros; split_ifs <;> simp
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        hsmul_ite]
      
      conv_lhs => rw [Fin.sum_univ_succAbove _ u]
      
      
      have hu_inner : ∑ j, ((if u = j then (2 : ℤ) else 0) - adj u j) * x j = 2 * xu - f b := by
        conv_lhs => rw [Fin.sum_univ_succAbove _ u]
        rw [hx_u, show (if u = u then (2 : ℤ) else 0) = 2 from if_pos rfl,
          show adj u u = 0 from hdiag u]
        have : ∀ i : Fin k,
            ((if u = u.succAbove i then (2 : ℤ) else 0) - adj u (u.succAbove i)) * x (u.succAbove i) =
            -adj u (u.succAbove i) * y i := by
          intro i
          rw [if_neg (Fin.succAbove_ne u i).symm, hx_sa]; ring
        simp_rw [this]
        have hneg_sum : ∑ i : Fin k, -adj u (u.succAbove i) * y i =
            -(∑ i : Fin k, adj u (u.succAbove i) * y i) := by
          simp only [neg_mul, Finset.sum_neg_distrib]
        rw [hneg_sum]
        
        have hadj_y_fb : ∑ i : Fin k, adj u (u.succAbove i) * y i = f b := by
          rw [(Equiv.sum_comp σ' _).symm]
          simp_rw [fun m : Fin k => show y (σ' m) = f (σ'.symm (σ' m)).val from rfl,
            fun m : Fin k => show (σ'.symm (σ' m)).val = m.val from
              congr_arg Fin.val (σ'.symm_apply_apply m), hadj_u_path]
          have : ∀ m : Fin k, (if σ' m = v' then (1 : ℤ) else 0) * f m.val =
              if m = bfin then f b else 0 := by
            intro m; by_cases hm : m = bfin
            · rw [hm, hσ'_b, if_pos rfl, one_mul, if_pos rfl]
            · rw [if_neg (fun h => hm (σ'.injective (h.trans hσ'_b.symm))), zero_mul, if_neg hm]
          simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [hadj_y_fb]; ring
      rw [hx_u, hu_inner, hfb_eq_2xu, show xu * (2 * xu - 2 * xu) = 0 from by ring, zero_add]
      
      
      rw [(Equiv.sum_comp σ' _).symm]
      simp_rw [hx_sa]
      
      have hinner : ∀ m : Fin k,
          ∑ j : Fin (k + 1), ((if u.succAbove (σ' m) = j then (2 : ℤ) else 0) - adj (u.succAbove (σ' m)) j) * x j =
          2 * f m.val - (if m = bfin then xu else 0) -
          (if 0 < m.val then f (m.val - 1) else 0) -
          (if m.val + 1 < k then f (m.val + 1) else 0) := by
        intro m
        conv_lhs => rw [Fin.sum_univ_succAbove _ u]
        
        rw [hx_u, show (if u.succAbove (σ' m) = u then (2 : ℤ) else 0) = 0 from
            if_neg (Fin.succAbove_ne u _),
          hsymm.apply, hadj_u_path m]
        
        rw [(Equiv.sum_comp σ' _).symm]
        simp_rw [hx_sa,
          fun n : Fin k => show (if u.succAbove (σ' m) = u.succAbove (σ' n) then (2 : ℤ) else 0) =
              if m = n then 2 else 0 from by
            simp only [Fin.succAbove_right_inj, σ'.injective.eq_iff],
          fun n : Fin k => show adj (u.succAbove (σ' m)) (u.succAbove (σ' n)) =
              if (m.val + 1 = n.val ∨ n.val + 1 = m.val) then 1 else 0 from hadj'_char m n,
          fun n : Fin k => show y (σ' n) = f (σ'.symm (σ' n)).val from rfl,
          fun n : Fin k => show (σ'.symm (σ' n)).val = n.val from
            congr_arg Fin.val (σ'.symm_apply_apply n)]
        
        have hu_col : (0 - (if σ' m = v' then (1 : ℤ) else 0)) * xu =
            -(if m = bfin then xu else 0) := by
          by_cases hm : m = bfin
          · rw [hm, hσ'_b, if_pos rfl, if_pos rfl]; ring
          · rw [if_neg (fun h => hm (σ'.injective (h.trans hσ'_b.symm))), if_neg hm]; ring
        rw [hu_col]
        
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        
        have hsum1 : ∑ n : Fin k, (if m = n then (2 : ℤ) else 0) * f ↑n = 2 * f ↑m := by
          conv_lhs =>
            arg 2; ext n
            rw [show (if m = n then (2 : ℤ) else 0) * f ↑n =
                if m = n then 2 * f ↑n else 0 from by split_ifs <;> ring]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
        
        have hsum2 : ∑ n : Fin k,
            (if (m.val + 1 = n.val ∨ n.val + 1 = m.val) then (1 : ℤ) else 0) * f n.val =
            (if 0 < m.val then f (m.val - 1) else 0) +
            (if m.val + 1 < k then f (m.val + 1) else 0) := by
          have htf : ∀ n : Fin k,
              (if (m.val + 1 = n.val ∨ n.val + 1 = m.val) then (1 : ℤ) else 0) * f n.val =
              if (m.val + 1 = n.val ∨ n.val + 1 = m.val) then f n.val else 0 := by
            intro n; split_ifs <;> ring
          simp_rw [htf]
          rw [← Finset.sum_filter]
          by_cases hm_pos : 0 < m.val <;> by_cases hm_lt : m.val + 1 < k
          · 
            have hfilt_eq : Finset.univ.filter (fun n : Fin k =>
                m.val + 1 = n.val ∨ n.val + 1 = m.val) =
                {⟨m.val - 1, by omega⟩, ⟨m.val + 1, hm_lt⟩} := by
              ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
              omega
            rw [hfilt_eq, Finset.sum_pair (by intro h; simp only [Fin.mk.injEq] at h; omega)]
            simp only [if_pos hm_pos, if_pos hm_lt]
          · 
            have hfilt_eq : Finset.univ.filter (fun n : Fin k =>
                m.val + 1 = n.val ∨ n.val + 1 = m.val) = {⟨m.val - 1, by omega⟩} := by
              ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_singleton, Fin.ext_iff]
              omega
            rw [hfilt_eq, Finset.sum_singleton]
            simp only [if_pos hm_pos, if_neg (show ¬m.val + 1 < k by omega), add_zero]
          · 
            have hfilt_eq : Finset.univ.filter (fun n : Fin k =>
                m.val + 1 = n.val ∨ n.val + 1 = m.val) = {⟨m.val + 1, by omega⟩} := by
              ext n; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_singleton, Fin.ext_iff]
              omega
            rw [hfilt_eq, Finset.sum_singleton]
            simp only [if_neg (show ¬0 < m.val by omega), if_pos (show m.val + 1 < k by omega), zero_add]
          · exfalso; have := m.isLt; omega
        rw [hsum1, hsum2]; ring
      simp_rw [hinner]
      simp_rw [fun m : Fin k => show y (σ' m) = f (σ'.symm (σ' m)).val from rfl,
        fun m : Fin k => show (σ'.symm (σ' m)).val = m.val from
          congr_arg Fin.val (σ'.symm_apply_apply m)]
      
      suffices h : ∀ m : Fin k,
          f (m : ℕ) * (((2 * f (m : ℕ) - if m = bfin then xu else 0) -
            if (0 : ℕ) < (m : ℕ) then f ((m : ℕ) - 1) else 0) -
            if (m : ℕ) + 1 < k then f ((m : ℕ) + 1) else 0) =
          if m = bfin then 2 * xu * (2 * ↑(b + 1) + 2 * ↑(k - b) - ↑(b + 1) * ↑(k - b)) else 0 by
        simp_rw [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      intro m
      by_cases hm : m = bfin
      · 
        subst hm
        rw [if_pos rfl, if_pos rfl, if_pos hb_pos, if_pos (show b + 1 < k by omega)]
        
        
        suffices hbracket_val : 2 * f b - xu - f (b - 1) - f (b + 1) =
            2 * ↑(b + 1) + 2 * ↑(k - b) - ↑(b + 1) * ↑(k - b) by
          rw [hbracket_val, hfb_eq_2xu]
        simp only [hf_def]
        rw [if_pos (show b ≤ b from le_refl _)]
        rw [if_pos (show b - 1 ≤ b by omega)]
        rw [if_neg (show ¬(b + 1 ≤ b) by omega)]
        simp only [hxu_def]
        push_cast
        rw [show (↑(b - 1) : ℤ) = ↑b - 1 from by omega]
        rw [show (↑(k - b) : ℤ) = ↑k - ↑b from by omega]
        ring
      · 
        rw [if_neg hm]
        have hm_ne_b : m.val ≠ b := fun h => hm (Fin.ext h)
        rw [if_neg hm, sub_zero]
        suffices hbracket : 2 * f m.val -
            (if 0 < m.val then f (m.val - 1) else 0) -
            (if m.val + 1 < k then f (m.val + 1) else 0) = 0 by
          rw [hbracket]; ring
        by_cases hm_lt_b : m.val < b
        · simp only [hf_def]
          by_cases hm_pos : 0 < m.val
          · rw [if_pos hm_pos, if_pos (show m.val + 1 < k by omega),
              if_pos (show m.val ≤ b by omega), if_pos (show m.val - 1 ≤ b by omega),
              if_pos (show m.val + 1 ≤ b by omega)]
            push_cast
            rw [show (↑(m.val - 1) : ℤ) = ↑m.val - 1 from by omega]
            ring
          · rw [if_neg (show ¬0 < m.val by omega), if_pos (show m.val + 1 < k by omega),
              if_pos (show m.val ≤ b by omega), if_pos (show m.val + 1 ≤ b by omega)]
            push_cast; rw [show (m.val : ℤ) = 0 from by exact_mod_cast (by omega : m.val = 0)]
            ring
        · push Not at hm_lt_b
          have hm_gt_b : b < m.val := by omega
          simp only [hf_def]
          rw [if_pos (show 0 < m.val by omega), if_neg (show ¬(m.val ≤ b) by omega)]
          by_cases hm_lt_k1 : m.val + 1 < k
          · rw [if_pos hm_lt_k1, if_neg (show ¬(m.val + 1 ≤ b) by omega)]
            by_cases hm1_le_b : m.val - 1 ≤ b
            · 
              have hm_eq : m.val = b + 1 := by omega
              rw [if_pos hm1_le_b]
              push_cast
              rw [show (↑(k - b) : ℤ) = ↑k - ↑b from by omega]
              rw [show (↑(m.val - 1) : ℤ) = ↑m.val - 1 from by omega]
              rw [show (m.val : ℤ) = ↑b + 1 from by exact_mod_cast hm_eq]
              ring
            · 
              rw [if_neg hm1_le_b]
              push_cast
              rw [show (↑(m.val - 1) : ℤ) = ↑m.val - 1 from by omega]
              ring
          · have hmk : m.val = k - 1 := by omega
            rw [if_neg (show ¬(m.val + 1 < k) by omega)]
            by_cases hm1_le_b : m.val - 1 ≤ b
            · 
              have hb_eq : b = k - 2 := by omega
              rw [if_pos hm1_le_b]
              push_cast
              rw [show (↑(k - b) : ℤ) = ↑k - ↑b from by omega]
              rw [show (↑(m.val - 1) : ℤ) = ↑m.val - 1 from by omega]
              rw [show (m.val : ℤ) = ↑k - 1 from by exact_mod_cast hmk]
              rw [show (b : ℤ) = ↑k - 2 from by omega]
              ring
            · rw [if_neg hm1_le_b]
              push_cast
              rw [show (↑(m.val - 1) : ℤ) = ↑m.val - 1 from by omega]
              rw [show (m.val : ℤ) = ↑k - 1 from by exact_mod_cast hmk]
              ring
    have hu_adj' : adj u (u.succAbove v') = 1 := by
      rw [hv', hsymm.apply]; exact hu_adj
    have hu_unique' : ∀ w, adj u w = 1 → w = u.succAbove v' := by
      intro w hw; have h := hu_unique w hw; rwa [← hv'] at h
    rcases RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.ordered_triple_cases_of_pairwise_sum_gt_product 1 q r (le_refl 1) hpq hqr hrecip with
      ⟨_, hq1⟩ | ⟨_, hq2, hr2⟩ | ⟨_, hq2, hr3⟩ | ⟨_, hq2, hr4⟩
    · 
      have hk4 : 4 ≤ k + 1 := by omega
      refine ⟨.D (k + 1) hk4, ?_⟩
      have hbm : b = k - 2 ∨ b = k - 1 - (k - 2) := by
        simp only [q, min_def] at hq1; split_ifs at hq1 <;> omega
      exact Matrix.exists_relabeling_of_erase_leaf_path_relabeling hsymm hdiag h01 u v' adj' hadj'_def
        hu_adj' hu_unique' σ' hσ'_fwd hσ'_only b hb_lt hσ'_b
        _ (k - 2) (by omega) hbm
        (by intro i j hi hj
            change (if ((i.val + 1 = j.val ∧ j.val ≤ (k + 1) - 2) ∨
                      (j.val + 1 = i.val ∧ i.val ≤ (k + 1) - 2)) ∨
                     ((i.val = (k + 1) - 3 ∧ j.val = (k + 1) - 1) ∨
                      (j.val = (k + 1) - 3 ∧ i.val = (k + 1) - 1))
                 then 1 else 0) = if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0
            split_ifs <;> omega)
        (by intro i hi
            change (if ((i.val + 1 = (⟨k, by omega⟩ : Fin (k + 1)).val ∧
                       (⟨k, by omega⟩ : Fin (k + 1)).val ≤ (k + 1) - 2) ∨
                      ((⟨k, by omega⟩ : Fin (k + 1)).val + 1 = i.val ∧
                       i.val ≤ (k + 1) - 2)) ∨
                     ((i.val = (k + 1) - 3 ∧ (⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 1) ∨
                      ((⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 3 ∧ i.val = (k + 1) - 1))
                 then 1 else 0) = if i.val = k - 2 then 1 else 0
            simp only [show (⟨k, by omega⟩ : Fin (k + 1)).val = k from rfl]
            split_ifs <;> omega)
        (by intro i hi
            change (if (((⟨k, by omega⟩ : Fin (k + 1)).val + 1 = i.val ∧
                       i.val ≤ (k + 1) - 2) ∨
                      (i.val + 1 = (⟨k, by omega⟩ : Fin (k + 1)).val ∧
                       (⟨k, by omega⟩ : Fin (k + 1)).val ≤ (k + 1) - 2)) ∨
                     (((⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 3 ∧ i.val = (k + 1) - 1) ∨
                      (i.val = (k + 1) - 3 ∧ (⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 1))
                 then 1 else 0) = if i.val = k - 2 then 1 else 0
            simp only [show (⟨k, by omega⟩ : Fin (k + 1)).val = k from rfl]
            split_ifs <;> omega)
        (by change (if (((⟨k, by omega⟩ : Fin (k + 1)).val + 1 = (⟨k, by omega⟩ : Fin (k + 1)).val ∧
                       (⟨k, by omega⟩ : Fin (k + 1)).val ≤ (k + 1) - 2) ∨
                      ((⟨k, by omega⟩ : Fin (k + 1)).val + 1 = (⟨k, by omega⟩ : Fin (k + 1)).val ∧
                       (⟨k, by omega⟩ : Fin (k + 1)).val ≤ (k + 1) - 2)) ∨
                     (((⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 3 ∧
                       (⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 1) ∨
                      ((⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 3 ∧
                       (⟨k, by omega⟩ : Fin (k + 1)).val = (k + 1) - 1))
                 then 1 else 0) = 0
            simp only [show (⟨k, by omega⟩ : Fin (k + 1)).val = k from rfl]
            split_ifs <;> omega)
    · 
      have hk5 : k = 5 := by omega
      subst hk5
      refine ⟨.E6, ?_⟩
      have hbm : b = 2 ∨ b = 5 - 1 - 2 := by
        simp only [q, min_def] at hq2
        simp only [r, max_def] at hr2
        split_ifs at hq2 hr2 <;> omega
      exact Matrix.exists_relabeling_of_erase_leaf_path_relabeling hsymm hdiag h01 u v' adj' hadj'_def
        hu_adj' hu_unique' σ' hσ'_fwd hσ'_only b hb_lt hσ'_b
        _ 2 (by omega) hbm
        (by intro i j hi hj; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by intro i hi; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by intro i hi; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
    · 
      have hk6 : k = 6 := by omega
      subst hk6
      refine ⟨.E7, ?_⟩
      have hbm : b = 2 ∨ b = 6 - 1 - 2 := by
        simp only [q, min_def] at hq2
        simp only [r, max_def] at hr3
        split_ifs at hq2 hr3 <;> omega
      exact Matrix.exists_relabeling_of_erase_leaf_path_relabeling hsymm hdiag h01 u v' adj' hadj'_def
        hu_adj' hu_unique' σ' hσ'_fwd hσ'_only b hb_lt hσ'_b
        _ 2 (by omega) hbm
        (by intro i j hi hj; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by intro i hi; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by intro i hi; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
    · 
      have hk7 : k = 7 := by omega
      subst hk7
      refine ⟨.E8, ?_⟩
      have hbm : b = 2 ∨ b = 7 - 1 - 2 := by
        simp only [q, min_def] at hq2
        simp only [r, max_def] at hr4
        split_ifs at hq2 hr4 <;> omega
      exact Matrix.exists_relabeling_of_erase_leaf_path_relabeling hsymm hdiag h01 u v' adj' hadj'_def
        hu_adj' hu_unique' σ' hσ'_fwd hσ'_only b hb_lt hσ'_b
        _ 2 (by omega) hbm
        (by intro i j hi hj; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by intro i hi; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by intro i hi; dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)
        (by dsimp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]; split_ifs <;> omega)



private lemma dynkin_classification_forward {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (hn : 1 ≤ n) :
    ∃ t : RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.matrix i j := by
  
  have hdeg := fun i => RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount_le_three hD i
  
  by_cases hbranch : ∃ i, RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj i = 3
  · 
    exact Matrix.exists_adjacency_reindexing_of_exists_vertex_value_eq_three hD hn hbranch
  · 
    push Not at hbranch
    have hpath : ∀ i, RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.neighborCount adj i ≤ 2 := by
      intro i; have := hdeg i
      rcases Nat.eq_or_lt_of_le this with h | h
      · exact absurd h (hbranch i)
      · omega
    obtain ⟨σ, hσ⟩ := RepresentationTheory.IntegerAdjacencyMatrixCombinatorics.exists_relabeling_eq_pathGraph hD hn hpath
    exact ⟨.A n hn, σ, hσ⟩









/-- A nonempty integer adjacency matrix satisfies the specified condition exactly when it contains a reindexed adjacency matrix of the given finite model. -/
@[source_ref "Chapter2/Theorem2.1.2/Derived3" (role := supporting),
  source_ref "Chapter6/Theorem_Dynkin_classification" (role := supporting)]
theorem Matrix.exists_adjacency_reindexing_iff (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n) :
    RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj ↔
    ∃ t : RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel, ∃ σ : Fin t.rank ≃ Fin n,
      ∀ i j, adj (σ i) (σ j) = t.matrix i j := by
  constructor
  · 
    exact fun hD => dynkin_classification_forward hD hn
  · 
    rintro ⟨t, σ, hiso⟩
    exact RepresentationTheory.FiniteIntegerMatrixModels.matrixCondition_of_relabeling σ hiso (RepresentationTheory.FiniteIntegerMatrixModels.matrix_satisfies_condition t)

end RepresentationTheory.Matrix.BinaryAdjacencyClassification

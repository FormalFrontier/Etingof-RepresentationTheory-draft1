/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.MatrixBoundedVectors
import RepresentationTheory.FiniteIntegerMatrixModels
import RepresentationTheory.Alignment.Attribute

/-!
# Finite-set cardinality

Finiteness and cardinality for a set determined by a finite integer matrix model.
-/

namespace RepresentationTheory.FiniteSetCardinality

set_option backward.isDefEq.respectTransparency false

section DnRootCount

open Matrix Finset


private lemma D4_sos (x₀ x₁ x₂ x₃ : ℤ) :
    2 * (2*(x₀^2+x₁^2+x₂^2+x₃^2) - 2*(x₀*x₁+x₁*x₂+x₁*x₃)) =
    (2*x₀-x₁)^2 + (2*x₂-x₁)^2 + (2*x₃-x₁)^2 + x₁^2 := by ring

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in

private lemma D4_qf (x : Fin 4 → ℤ) :
    dotProduct x
      ((2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) -
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D 4 le_rfl).matrix).mulVec x) =
    2*(x 0^2+x 1^2+x 2^2+x 3^2) -
    2*(x 0*x 1+x 1*x 2+x 1*x 3) := by
  simp only [dotProduct, mulVec, Finset.sum_fin_eq_sum_range,
    RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Fin.isValue]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  try simp only [Fin.reduceFinMk]
  ring


private lemma D4_bound (x : Fin 4 → ℤ)
    (hr : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix 4 (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D 4 le_rfl).matrix x)
    (hp : ∀ i, 0 ≤ x i) : ∀ i, x i < 3 := by
  have hq : 2*(x 0^2+x 1^2+x 2^2+x 3^2) -
      2*(x 0*x 1+x 1*x 2+x 1*x 3) = 2 := by
    have := hr.2; rw [D4_qf] at this; exact this
  set a := x 0
  set b := x 1
  set c := x 2
  set d := x 3
  have hs : (2*a-b)^2 + (2*c-b)^2 + (2*d-b)^2 + b^2 = 4 := by
    nlinarith [D4_sos a b c d]
  have hb : b ≤ 2 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*c-b),
      sq_nonneg (2*d-b), sq_nonneg (b - 3)]
  have ha : a ≤ 2 := by
    nlinarith [sq_nonneg (2*c-b), sq_nonneg (2*d-b),
      sq_nonneg b, sq_nonneg (2*a - b - 3)]
  have hc : c ≤ 2 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*d-b),
      sq_nonneg b, sq_nonneg (2*c - b - 3)]
  have hd : d ≤ 2 := by
    nlinarith [sq_nonneg (2*a-b), sq_nonneg (2*c-b),
      sq_nonneg b, sq_nonneg (2*d - b - 3)]
  intro i; fin_cases i <;> simp_all <;> omega







private lemma Dn_adj_succ_succ (m : ℕ) (hm : 4 ≤ m) (i j : Fin m) :
    (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix i.succ j.succ =
    (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix i j := by
  simp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Fin.val_succ]
  have hi := i.isLt
  have hj := j.isLt
  congr 1
  apply propext
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩))
    · left; left; exact ⟨by omega, by omega⟩
    · left; right; exact ⟨by omega, by omega⟩
    · right; left; exact ⟨by omega, by omega⟩
    · right; right; exact ⟨by omega, by omega⟩
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩))
    · left; left; exact ⟨by omega, by omega⟩
    · left; right; exact ⟨by omega, by omega⟩
    · right; left; exact ⟨by omega, by omega⟩
    · right; right; exact ⟨by omega, by omega⟩


private lemma Dn_adj_zero_succ (m : ℕ) (hm : 4 ≤ m) (j : Fin m) :
    (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix (⟨0, by omega⟩ : Fin (m + 1)) j.succ =
    if j.val = 0 then 1 else 0 := by
  simp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Fin.val_succ]
  have hj := j.isLt
  congr 1; apply propext; constructor
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩)) <;> omega
  · intro h; left; left; exact ⟨by omega, by omega⟩


private lemma Dn_adj_zero_zero (m : ℕ) (hm : 4 ≤ m) :
    (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix (⟨0, by omega⟩ : Fin (m + 1)) (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by
  simp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]
  have : ¬(((0 + 1 = 0 ∧ (0 : ℕ) ≤ m + 1 - 2) ∨ (0 + 1 = 0 ∧ (0 : ℕ) ≤ m + 1 - 2)) ∨
    ((0 = m + 1 - 3 ∧ (0 : ℕ) = m + 1 - 1) ∨ (0 = m + 1 - 3 ∧ (0 : ℕ) = m + 1 - 1))) := by omega
  rw [if_neg this]


private lemma Dn_adj_succ_zero (m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix i.succ (⟨0, by omega⟩ : Fin (m + 1)) =
    if i.val = 0 then 1 else 0 := by
  simp only [RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Fin.val_succ]
  have hi := i.isLt
  congr 1; apply propext; constructor
  · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | (⟨h5, h6⟩ | ⟨h7, h8⟩)) <;> omega
  · intro h; left; right; exact ⟨by omega, by omega⟩


private lemma Dn_cartan_succ_succ (m : ℕ) (hm : 4 ≤ m) (i j : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix) i.succ j.succ =
    (2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Dn_adj_succ_succ m hm i j, show (i.succ : Fin (m + 1)) = j.succ ↔ i = j from Fin.succ_inj]


private lemma Dn_cartan_zero_succ (m : ℕ) (hm : 4 ≤ m) (j : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix) 0 j.succ =
    if j.val = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Fin.val_succ]
  have hj := j.isLt
  have : ¬((0 : Fin (m + 1)) = j.succ) := (Fin.succ_ne_zero j).symm
  rw [if_neg this]; simp
  split_ifs <;> omega


private lemma Dn_cartan_succ_zero (m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix) i.succ 0 =
    if i.val = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Fin.val_succ]
  have hi := i.isLt
  have : ¬((i.succ : Fin (m + 1)) = 0) := Fin.succ_ne_zero i
  rw [if_neg this]; simp
  split_ifs <;> omega


private lemma Dn_cartan_zero_zero (m : ℕ) (hm : 4 ≤ m) :
    (2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix) 0 0 = 2 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  have h := Dn_adj_zero_zero m hm
  rw [show (⟨0, by omega⟩ : Fin (m + 1)) = (0 : Fin (m + 1)) from rfl] at h
  rw [h]; norm_num


private lemma Dn_qform_peel (m : ℕ) (hm : 4 ≤ m) (x : Fin (m + 1) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix).mulVec x) =
    dotProduct (x ∘ Fin.succ)
      ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix).mulVec (x ∘ Fin.succ)) +
    2 * x 0 ^ 2 - 2 * x 0 * x ⟨1, by omega⟩ := by
  
  simp only [dotProduct, mulVec, Function.comp, Fin.sum_univ_succ]
  
  simp only [Dn_cartan_zero_zero m hm, Dn_cartan_zero_succ m hm,
    Dn_cartan_succ_zero m hm, Dn_cartan_succ_succ m hm]
  
  simp only [ite_mul, one_mul, zero_mul, neg_mul]
  
  have hconv : ∀ (i : Fin m) (a b : ℤ),
      (if i.val = 0 then a else b) = if i = ⟨0, by omega⟩ then a else b := by
    intro i a b; congr 1; exact propext ⟨fun h => Fin.ext h, fun h => congr_arg _ h⟩
  simp_rw [hconv]
  
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hx1 : Fin.succ (⟨0, by omega⟩ : Fin m) = (⟨1, by omega⟩ : Fin (m + 1)) := by
    ext; simp
  simp only [hx1]
  
  simp_rw [mul_add, Finset.sum_add_distrib]
  
  have hite : ∑ i : Fin m, x i.succ * (if i = ⟨0, by omega⟩ then -x 0 else 0) =
      -x ⟨1, by omega⟩ * x 0 := by
    rw [Finset.sum_eq_single_of_mem ⟨0, by omega⟩ (Finset.mem_univ _)
      (fun b _ hb => by simp [hb])]
    simp
  linarith [hite, sq (x 0)]


private lemma Dn_qform_ge_sq_and_posDef : ∀ (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ),
    (x ⟨0, by omega⟩) ^ 2 ≤ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix).mulVec x) ∧
    (x ≠ 0 → 0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix).mulVec x)) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm x
    set q := dotProduct x ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) hm).matrix).mulVec x)
    by_cases hm4 : m = 3
    · subst hm4
      have hsos := D4_sos (x 0) (x 1) (x 2) (x 3)
      have hqf := D4_qf x
      have hq_eq : q = 2*(x 0^2+x 1^2+x 2^2+x 3^2) -
          2*(x 0*x 1+x 1*x 2+x 1*x 3) := hqf
      have hsos2 : 2 * q = (2*x 0-x 1)^2 + (2*x 2-x 1)^2 +
          (2*x 3-x 1)^2 + x 1^2 := by linarith
      constructor
      · 
        change (x 0) ^ 2 ≤ q
        nlinarith [hsos2, sq_nonneg (x 0 - x 1), sq_nonneg (2 * x 2 - x 1),
          sq_nonneg (2 * x 3 - x 1)]
      · intro hne
        show 0 < q
        by_cases h1 : x 1 = 0
        · 
          have : x 0 ≠ 0 ∨ x 2 ≠ 0 ∨ x 3 ≠ 0 := by
            by_contra h; push Not at h; apply hne; ext i; fin_cases i <;> simp_all
          simp only [h1, sub_zero] at hsos2
          rcases this with h | h | h <;>
            nlinarith [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3),
              mul_self_pos.mpr h]
        · 
          have := mul_self_pos.mpr h1
          nlinarith [sq_nonneg (2 * x 0 - x 1), sq_nonneg (2 * x 2 - x 1),
            sq_nonneg (2 * x 3 - x 1)]
    · have hm' : 4 ≤ m := by omega
      have hpeel := Dn_qform_peel m hm' x
      set tail := x ∘ Fin.succ with htail_def
      set q_tail := dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm').matrix).mulVec tail)
      have htail0 : tail ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by
        simp [htail_def]
      have hih := ih hm' tail
      rw [htail0] at hih
      have hq_eq : q = q_tail + 2 * x ⟨0, by omega⟩ ^ 2 -
          2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ := hpeel
      constructor
      · 
        
        
        nlinarith [hih.1, sq_nonneg (x ⟨0, by omega⟩ - x ⟨1, by omega⟩)]
      · intro hne
        by_cases hx0 : x ⟨0, by omega⟩ = 0
        · 
          have htail_ne : tail ≠ 0 := by
            intro h; apply hne; ext i
            by_cases hi : i = ⟨0, by omega⟩
            · rw [hi]; exact hx0
            · have hiv : i.val ≠ 0 := fun heq => hi (Fin.ext heq)
              have : ∃ j : Fin m, i = j.succ :=
                ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
              obtain ⟨j, rfl⟩ := this
              exact congr_fun h j
          nlinarith [hih.2 htail_ne, sq_nonneg (x ⟨1, by omega⟩)]
        · 
          have hx0_pos := mul_self_pos.mpr hx0
          nlinarith [hih.1, sq_nonneg (x ⟨0, by omega⟩ - x ⟨1, by omega⟩)]


private lemma Dn_posDef (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ) (hx : x ≠ 0) :
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix).mulVec x) :=
  (Dn_qform_ge_sq_and_posDef n hn x).2 hx


private lemma Dn_cascade_bound : ∀ (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ),
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix).mulVec x) = 2 * x ⟨0, by omega⟩ →
    x ⟨0, by omega⟩ ≤ 2 →
    (∀ i, 0 ≤ x i) → ∀ i, x i < 3 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm x hq hx0_le hpos
    by_cases hm4 : m = 3
    · subst hm4
      
      have hsos := D4_sos (x 0) (x 1) (x 2) (x 3)
      have hqf := D4_qf x
      
      have hq0 : x ⟨0, by omega⟩ = x 0 := rfl
      rw [hq0] at hq hx0_le
      have hsos_bound : (2*x 0-x 1)^2 + (2*x 2-x 1)^2 +
          (2*x 3-x 1)^2 + x 1^2 ≤ 8 := by nlinarith
      
      have hx1 : x 1 ≤ 2 := by nlinarith [sq_nonneg (x 1 - 3)]
      have hx2 : x 2 ≤ 2 := by nlinarith [sq_nonneg (2*x 2 - x 1 - 3), sq_nonneg (2*x 2 - x 1 + 3)]
      have hx3 : x 3 ≤ 2 := by nlinarith [sq_nonneg (2*x 3 - x 1 - 3), sq_nonneg (2*x 3 - x 1 + 3)]
      intro i; fin_cases i <;> simp_all <;> omega
    · have hm' : 4 ≤ m := by omega
      have hpeel := Dn_qform_peel m hm' x
      set tail := x ∘ Fin.succ
      have htail0 : tail ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by simp [tail]
      set q_tail := dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm').matrix).mulVec tail)
      have hge := (Dn_qform_ge_sq_and_posDef m hm' tail).1
      rw [htail0] at hge
      have hx0 := x ⟨0, by omega⟩
      by_cases hx0_eq : x ⟨0, by omega⟩ = 0
      · 
        have : q_tail = 0 := by nlinarith [hpeel]
        have htail_zero : tail = 0 := by
          by_contra h
          exact absurd this (ne_of_gt ((Dn_qform_ge_sq_and_posDef m hm' tail).2 h))
        intro i
        by_cases hi : i = ⟨0, by omega⟩
        · rw [hi, hx0_eq]; norm_num
        · have hiv : i.val ≠ 0 := fun heq => hi (Fin.ext heq)
          have : ∃ j : Fin m, i = j.succ :=
            ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
          obtain ⟨j, rfl⟩ := this
          have := congr_fun htail_zero j; simp [tail] at this
          linarith
      · 
        have hx0_pos : 0 < x ⟨0, by omega⟩ := by
          have h0 := hpos ⟨0, by omega⟩; omega
        
        have hpeel' := hpeel; rw [hq, show x (0 : Fin (m + 1)) = x ⟨0, by omega⟩ from rfl] at hpeel'
        have hq_tail_val : q_tail = 2 * x ⟨0, by omega⟩ -
            2 * x ⟨0, by omega⟩ ^ 2 + 2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ := by
          linarith [hpeel']
        
        have hx1_sq : (x ⟨1, by omega⟩) ^ 2 ≤ q_tail := hge
        
        
        
        
        have hx1_bound : x ⟨1, by omega⟩ ≤ 2 := by
          nlinarith [sq_nonneg (x ⟨1, by omega⟩ - 2)]
        have hq_tail_cascade : q_tail = 2 * tail ⟨0, by omega⟩ := by
          rw [htail0]
          by_cases hx0_1 : x ⟨0, by omega⟩ = 1
          · nlinarith [hq_tail_val, hx0_1]
          · have hx0_2 : x ⟨0, by omega⟩ = 2 := by omega
            have hq_t : q_tail = 4 * x ⟨1, by omega⟩ - 4 := by nlinarith
            have hx1_eq : x ⟨1, by omega⟩ = 2 := by
              nlinarith [sq_nonneg (x ⟨1, by omega⟩ - 2)]
            linarith
        have htail0_le : tail ⟨0, by omega⟩ ≤ 2 := by rw [htail0]; exact hx1_bound
        have htail_pos : ∀ i, 0 ≤ tail i := fun i => hpos i.succ
        have hih_result := ih hm' tail hq_tail_cascade htail0_le htail_pos
        intro i
        by_cases hi : i = ⟨0, by omega⟩
        · rw [hi]; linarith
        · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have : ∃ j : Fin m, i = j.succ :=
            ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
          obtain ⟨j, rfl⟩ := this
          exact hih_result j


private lemma Dn_bound : ∀ (n : ℕ) (hn : 4 ≤ n) (x : Fin n → ℤ),
    RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix x →
    (∀ i, 0 ≤ x i) → ∀ i, x i < 3 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm x hr hpos
    by_cases hm4 : m = 3
    · subst hm4; exact D4_bound x hr hpos
    · have hm' : 4 ≤ m := by omega
      have hge := (Dn_qform_ge_sq_and_posDef (m + 1) hm x).1
      have hq := hr.2
      have hx0_bound : x ⟨0, by omega⟩ ≤ 1 := by nlinarith [sq_nonneg (x ⟨0, by omega⟩ - 1)]
      have hpeel := Dn_qform_peel m hm' x
      set tail := x ∘ Fin.succ
      have htail0 : tail ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by simp [tail]
      have htail_pos : ∀ i, 0 ≤ tail i := fun i => hpos i.succ
      
      suffices h : ∀ j : Fin m, tail j < 3 by
        intro i
        by_cases hi : i.val = 0
        · have : i = ⟨0, by omega⟩ := Fin.ext hi; rw [this]; omega
        · have : ∃ j : Fin m, i = j.succ :=
            ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
          obtain ⟨j, rfl⟩ := this; exact h j
      have hpeel' := hpeel; rw [hq, show x (0 : Fin (m + 1)) = x ⟨0, by omega⟩ from rfl] at hpeel'
      by_cases hx0 : x ⟨0, by omega⟩ = 0
      · 
        have hq_tail : dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
            (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm').matrix).mulVec tail) = 2 := by
          have h1 : x ⟨0, by omega⟩ ^ 2 = 0 := by rw [hx0]; ring
          have h2 : x ⟨0, by omega⟩ * x ⟨1, by omega⟩ = 0 := by rw [hx0]; ring
          linarith [hpeel', h1, h2]
        have htail_ne : tail ≠ 0 := by
          intro h; apply hr.1; ext i
          by_cases hi : i.val = 0
          · have : i = ⟨0, by omega⟩ := Fin.ext hi; rw [this]; exact hx0
          · have : ∃ j : Fin m, i = j.succ :=
              ⟨⟨i.val - 1, by omega⟩, by ext; simp; omega⟩
            obtain ⟨j, rfl⟩ := this; exact congr_fun h j
        exact ih hm' tail ⟨htail_ne, hq_tail⟩ htail_pos
      · 
        have hx0_1 : x ⟨0, by omega⟩ = 1 := by
          have h0 := hpos ⟨0, by omega⟩; omega
        have hq_tail : dotProduct tail ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
            (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm').matrix).mulVec tail) =
            2 * tail ⟨0, by omega⟩ := by
          rw [htail0]
          have h1 : x ⟨0, by omega⟩ ^ 2 = 1 := by rw [hx0_1]; ring
          have h2 : x ⟨0, by omega⟩ * x ⟨1, by omega⟩ = x ⟨1, by omega⟩ := by rw [hx0_1]; ring
          linarith [hpeel', h1, h2]
        have hge_tail := (Dn_qform_ge_sq_and_posDef m hm' tail).1
        rw [htail0] at hge_tail
        have hx1_bound : x ⟨1, by omega⟩ ≤ 2 := by
          nlinarith [sq_nonneg (x ⟨1, by omega⟩ - 2)]
        have htail0_le : tail ⟨0, by omega⟩ ≤ 2 := by rw [htail0]; exact hx1_bound
        exact Dn_cascade_bound m hm' tail hq_tail htail0_le htail_pos

private lemma D4_count :
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors 4 (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D 4 le_rfl).matrix 3).card = 12 := by
  decide

private lemma D4_nonzero_count :
    ((RepresentationTheory.MatrixBoundedVectors.boundedVectors 4 (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D 4 le_rfl).matrix 3).filter
      (fun v => v ⟨0, by omega⟩ ≠ 0)).card = 2 * (4 - 1) := by
  decide

private lemma D5_count :
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors 5 (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D 5 (by omega)).matrix 3).card = 20 := by
  decide


private lemma Dn_filter_zero_card (m : ℕ) (hm : 4 ≤ m) :
    ((RepresentationTheory.MatrixBoundedVectors.boundedVectors (m + 1) (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix 3).filter
      (fun v => v 0 = 0)).card =
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors m (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix 3).card := by
  apply Finset.card_nbij' (fun v => v ∘ Fin.succ) (fun w => Fin.cons 0 w)
  · 
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv
    have hmem := hv.1
    have hv0 : v 0 = 0 := hv.2
    simp only [Finset.mem_coe, RepresentationTheory.MatrixBoundedVectors.boundedVectors, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq]
    simp only [RepresentationTheory.MatrixBoundedVectors.boundedVectors, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hmem
    refine ⟨?_, ?_⟩
    · 
      intro htail
      apply hmem.1; funext i; simp only [Pi.zero_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact_mod_cast hv0
      · have := congr_fun htail j; simp only [Function.comp, Pi.zero_apply] at this; exact this
    · 
      have hpeel := Dn_qform_peel m hm (fun i => (v i : ℤ))
      
      have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ =
          fun i ↦ (↑↑((v ∘ Fin.succ) i) : ℤ) := rfl
      rw [hcomp] at hpeel
      rw [hmem.2] at hpeel
      have hv0z : (↑↑(v 0) : ℤ) = 0 := by exact_mod_cast hv0
      have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 0 := by rw [hv0z]; ring
      have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 0 := by rw [hv0z]; ring
      linarith [hpeel, h0sq, h0prod]
  · 
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter]
    simp only [Finset.mem_coe, RepresentationTheory.MatrixBoundedVectors.boundedVectors, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hw
    set v : Fin (m + 1) → Fin 3 := Fin.cons 0 w with hv_def
    constructor
    · simp only [RepresentationTheory.MatrixBoundedVectors.boundedVectors, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · intro heq
        apply hw.1; funext i
        have := congr_fun heq (Fin.succ i)
        simp only [hv_def, Fin.cons_succ, Pi.zero_apply] at this; exact this
      · have hpeel := Dn_qform_peel m hm (fun i => (↑↑(v i) : ℤ))
        have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ = fun i ↦ (↑↑(w i) : ℤ) := by
          funext i; simp [hv_def, Fin.cons_succ]
        rw [hcomp] at hpeel
        have h0 : (↑↑(v 0) : ℤ) = 0 := by simp [hv_def, Fin.cons_zero]
        have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 0 := by rw [h0]; ring
        have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 0 := by rw [h0]; ring
        linarith [hpeel, hw.2, h0sq, h0prod]
    · show v 0 = 0
      simp [hv_def, Fin.cons_zero]
  · 
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact hv.2.symm
    · simp only [Function.comp, Fin.cons_succ]
  · 
    intro w _
    funext i; simp only [Function.comp, Fin.cons_succ]


private lemma Dn_no_coord2_at_zero : ∀ (n : ℕ) (hn : 4 ≤ n) (v : Fin n → Fin 3),
    v ∈ RepresentationTheory.MatrixBoundedVectors.boundedVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix 3 →
    v ⟨0, by omega⟩ ≠ 2 := by
  intro n hn v hv hv0
  simp only [RepresentationTheory.MatrixBoundedVectors.boundedVectors, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hne, hq⟩ := hv
  set x : Fin n → ℤ := fun i => (v i : ℤ)
  have hge := (Dn_qform_ge_sq_and_posDef n hn x).1
  rw [hq] at hge
  have hv0z : x ⟨0, by omega⟩ = 2 := by
    simp [x]; exact_mod_cast congr_arg Fin.val hv0
  nlinarith [hv0z, sq_nonneg (x ⟨0, by omega⟩ - 1)]


private def qFourFinset (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (hn : 0 < n := by omega) :
    Finset (Fin n → Fin 3) :=
  (Finset.univ : Finset (Fin n → Fin 3)).filter fun v =>
    v ⟨0, hn⟩ = 2 &&
    decide (dotProduct (fun i => (v i : ℤ))
      ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun i => (v i : ℤ))) = 4)

private lemma D4_qfour :
    (qFourFinset 4 (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D 4 le_rfl).matrix).card = 1 := by
  decide


private lemma qFourFinset_peel (m : ℕ) (hm : 4 ≤ m) :
    (qFourFinset (m + 1) (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix).card =
    (qFourFinset m (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix).card := by
  apply Finset.card_nbij' (fun v => v ∘ Fin.succ) (fun w => Fin.cons 2 w)
  · 
    intro v hv
    simp only [Finset.mem_coe, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    have hv0 := hv.1
    have hq := hv.2
    
    have hpeel := Dn_qform_peel m hm (fun i => (↑↑(v i) : ℤ))
    have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ =
        fun i ↦ (↑↑((v ∘ Fin.succ) i) : ℤ) := rfl
    rw [hcomp] at hpeel
    rw [hq] at hpeel
    
    have h0z : (↑↑(v 0) : ℤ) = 2 := by
      have := congr_arg Fin.val hv0; simp at this; omega
    have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 4 := by rw [h0z]; ring
    have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 2 * ↑↑(v ⟨1, by omega⟩) := by
      rw [h0z]
    
    
    
    
    
    
    have hv1bound : (↑↑(v ⟨1, by omega⟩) : ℤ) ∈ ({0, 1, 2} : Set ℤ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have := (v ⟨1, by omega⟩).2; omega
    have hge := (Dn_qform_ge_sq_and_posDef m hm (fun i => (↑↑((v ∘ Fin.succ) i) : ℤ))).1
    
    
    have htail0 : (↑↑((v ∘ Fin.succ) ⟨0, by omega⟩) : ℤ) = ↑↑(v ⟨1, by omega⟩) := rfl
    rw [htail0] at hge
    
    
    
    have hv1eq : (↑↑(v ⟨1, by omega⟩) : ℤ) = 2 := by
      nlinarith [hpeel, h0sq, h0prod, hge, sq_nonneg ((↑↑(v ⟨1, by omega⟩) : ℤ) - 2)]
    constructor
    · 
      have : (v ∘ Fin.succ) ⟨0, by omega⟩ = v ⟨1, by omega⟩ := rfl
      rw [this]; exact Fin.ext (by have := hv1eq; omega)
    · 
      linarith [hpeel, h0sq, h0prod, hv1eq]
  · 
    intro w hw
    simp only [Finset.mem_coe, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
    set v : Fin (m + 1) → Fin 3 := Fin.cons 2 w with hv_def
    constructor
    · change v ⟨0, by omega⟩ = 2
      simp [hv_def, Fin.cons_zero]
    · have hpeel := Dn_qform_peel m hm (fun i => (↑↑(v i) : ℤ))
      have hcomp : (fun i ↦ (↑↑(v i) : ℤ)) ∘ Fin.succ = fun i ↦ (↑↑(w i) : ℤ) := by
        funext i; simp [hv_def, Fin.cons_succ]
      rw [hcomp] at hpeel
      have h0 : (↑↑(v 0) : ℤ) = 2 := by simp [hv_def, Fin.cons_zero]
      have h0sq : (↑↑(v 0) : ℤ) ^ 2 = 4 := by rw [h0]; ring
      have hw0z : (↑↑(w ⟨0, by omega⟩) : ℤ) = 2 := congrArg (fun x => (↑↑x : ℤ)) hw.1
      
      have hv1z : (↑↑(v ⟨1, by omega⟩) : ℤ) = ↑↑(w ⟨0, by omega⟩) := by
        simp only [hv_def]; rfl
      have h0prod : (↑↑(v 0) : ℤ) * ↑↑(v ⟨1, by omega⟩) = 2 * ↑↑(w ⟨0, by omega⟩) := by
        rw [h0, hv1z]
      linarith [hpeel, h0sq, h0prod, hw0z, hw.2]
  · 
    intro v hv
    simp only [Finset.mem_coe, qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact hv.1.symm
    · simp only [Function.comp, Fin.cons_succ]
  · 
    intro w _
    funext i; simp only [Function.comp, Fin.cons_succ]


private lemma qFourFinset_card (m : ℕ) (hm : 4 ≤ m) :
    (qFourFinset m (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix).card = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm4 : m = 3
    · subst hm4; exact D4_qfour
    · have hm' : 4 ≤ m := by omega
      rw [qFourFinset_peel m hm', ih hm']


private lemma Dn_v0_eq_one (n : ℕ) (hn : 4 ≤ n) (v : Fin n → Fin 3)
    (hroot : v ∈ RepresentationTheory.MatrixBoundedVectors.boundedVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix 3)
    (hne : v ⟨0, by omega⟩ ≠ 0) : v ⟨0, by omega⟩ = (1 : Fin 3) := by
  have h2 := Dn_no_coord2_at_zero n hn v hroot
  have hlt := (v ⟨0, by omega⟩).isLt
  have hne_val : (v ⟨0, by omega⟩).val ≠ 0 := fun h => hne (Fin.ext h)
  have h2_val : (v ⟨0, by omega⟩).val ≠ 2 := fun h => h2 (Fin.ext h)
  exact Fin.ext (by omega)


private lemma rootCountFinset_mem_iff {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {v : Fin n → Fin 3} :
    v ∈ RepresentationTheory.MatrixBoundedVectors.boundedVectors n adj 3 ↔
    ((fun i => (↑(v i) : ℤ)) ≠ 0 ∧
      dotProduct (fun i => (↑(v i) : ℤ))
        ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun i => (↑(v i) : ℤ))) = 2) := by
  simp only [RepresentationTheory.MatrixBoundedVectors.boundedVectors, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.and_eq_true, decide_eq_true_eq]


private lemma Dn_peel_at_one (m : ℕ) (hm : 4 ≤ m) (v : Fin (m + 1) → Fin 3)
    (hq : dotProduct (fun i => (↑(v i) : ℤ)) ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
      (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix).mulVec (fun i => (↑(v i) : ℤ))) = 2)
    (hv0 : v 0 = (1 : Fin 3)) :
    dotProduct (fun i => (↑((v ∘ Fin.succ) i) : ℤ))
      ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) -
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix).mulVec (fun i => (↑((v ∘ Fin.succ) i) : ℤ))) =
    2 * (↑(v ⟨1, by omega⟩) : ℤ) := by
  have hpeel := Dn_qform_peel m hm (fun i => (↑(v i) : ℤ))
  have hcomp : (fun i ↦ (↑(v i) : ℤ)) ∘ Fin.succ =
      fun i ↦ (↑((v ∘ Fin.succ) i) : ℤ) := rfl
  rw [hcomp, hq] at hpeel
  have hv0z : (↑(v (0 : Fin (m + 1))) : ℤ) = 1 := by simp [hv0]
  linarith [show (↑(v (0 : Fin (m + 1))) : ℤ) ^ 2 = 1 by rw [hv0z]; ring,
    show (↑(v (0 : Fin (m + 1))) : ℤ) * ↑(v ⟨1, by omega⟩) =
      ↑(v ⟨1, by omega⟩) by rw [hv0z]; ring]


private lemma fin3_val_zero {x : Fin 3} (h : (↑x : ℤ) = 0) : x = 0 := by
  have : x.val = 0 := by exact_mod_cast h
  exact Fin.ext this


private lemma fin3_fun_zero {n : ℕ} {v : Fin n → Fin 3}
    (h : (fun i => (↑(v i) : ℤ)) = 0) : v = 0 := by
  funext i; exact fin3_val_zero (congr_fun h i)


private lemma fin3_fun_ne_zero {n : ℕ} {v : Fin n → Fin 3}
    (h : v ≠ 0) : (fun i => (↑(v i) : ℤ)) ≠ 0 :=
  fun heq => h (fin3_fun_zero heq)


private lemma Dn_nonzero_v1eq1_bij (m : ℕ) (hm : 4 ≤ m) :
    (((RepresentationTheory.MatrixBoundedVectors.boundedVectors (m + 1) (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix 3).filter
        (fun v => v 0 ≠ 0)).filter
      (fun v => v ⟨1, by omega⟩ = 1)).card =
    ((RepresentationTheory.MatrixBoundedVectors.boundedVectors m (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix 3).filter
      (fun v => v ⟨0, by omega⟩ ≠ 0)).card := by
  apply Finset.card_nbij' (fun v => v ∘ Fin.succ) (fun w => Fin.cons (1 : Fin 3) w)
  · 
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv ⊢
    obtain ⟨⟨hv_root, hv0_ne⟩, hv1_eq⟩ := hv
    have hv0_eq := Dn_v0_eq_one (m + 1) (by omega) v hv_root hv0_ne
    have ⟨_, hv_q⟩ := rootCountFinset_mem_iff.mp hv_root
    have hpeel := Dn_peel_at_one m hm v hv_q hv0_eq
    have hv1z : (↑(v ⟨1, by omega⟩) : ℤ) = 1 := by
      have := congr_arg Fin.val hv1_eq; simp at this; exact_mod_cast this
    rw [hv1z, mul_one] at hpeel
    constructor
    · rw [rootCountFinset_mem_iff]
      refine ⟨fun htail => ?_, hpeel⟩
      have h0 : (↑(v ⟨1, by omega⟩) : ℤ) = 0 := by
        have := congr_fun htail ⟨0, by omega⟩
        simp only [Pi.zero_apply, Function.comp_apply] at this
        exact this
      linarith
    · intro h0
      have h0z : (↑(v ⟨1, by omega⟩) : ℤ) = 0 := by
        have : (↑((v ∘ Fin.succ) ⟨0, by omega⟩) : ℤ) = 0 := by exact_mod_cast h0
        simpa [Function.comp_apply] using this
      linarith
  · 
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    obtain ⟨hw_root, hw0_ne⟩ := hw
    have hw0_eq := Dn_v0_eq_one m hm w hw_root hw0_ne
    have ⟨hw_ne, hw_q⟩ := rootCountFinset_mem_iff.mp hw_root
    set v : Fin (m + 1) → Fin 3 := Fin.cons (1 : Fin 3) w
    have hv_succ : v ∘ Fin.succ = w := funext fun i => Fin.cons_succ _ _ _
    have hv0z : (↑(v (0 : Fin (m + 1))) : ℤ) = 1 := by simp [v, Fin.cons_zero]
    have hw0z : (↑(w ⟨0, by omega⟩) : ℤ) = 1 := by
      exact_mod_cast congr_arg Fin.val hw0_eq
    have hv1z : (↑(v ⟨1, by omega⟩) : ℤ) = 1 := by
      change (↑(w ⟨0, by omega⟩) : ℤ) = 1; exact hw0z
    have hv_ne : (fun i => (↑(v i) : ℤ)) ≠ 0 := by
      intro heq; have := congr_fun heq (0 : Fin (m + 1))
      simp [v, Fin.cons_zero] at this
    have hv_q : dotProduct (fun i => (↑(v i) : ℤ))
        ((2 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) -
          (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix).mulVec
          (fun i => (↑(v i) : ℤ))) = 2 := by
      have hpeel := Dn_qform_peel m hm (fun i => (↑(v i) : ℤ))
      have hcomp : (fun i ↦ (↑(v i) : ℤ)) ∘ Fin.succ = fun i ↦ (↑(w i) : ℤ) := by
        funext i; simp [v, Fin.cons_succ]
      rw [hcomp] at hpeel
      linarith [hw_q,
        show (↑(v (0 : Fin (m + 1))) : ℤ) ^ 2 = 1 by rw [hv0z]; ring,
        show (↑(v (0 : Fin (m + 1))) : ℤ) * ↑(v ⟨1, by omega⟩) = 1 by rw [hv0z, hv1z]; ring]
    refine ⟨⟨rootCountFinset_mem_iff.mpr ⟨hv_ne, hv_q⟩, ?_⟩, ?_⟩
    · show v 0 ≠ 0; simp [v, Fin.cons_zero]
    · change v ⟨1, by omega⟩ = 1
      change w ⟨0, by omega⟩ = 1
      exact hw0_eq
  · 
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · exact (Dn_v0_eq_one (m + 1) (by omega) v hv.1.1 hv.1.2).symm ▸ Fin.cons_zero _ _
    · exact Fin.cons_succ _ _ _
  · 
    intro w _; funext i; exact Fin.cons_succ _ _ _


private lemma Dn_nonzero_v1ne1_bij (m : ℕ) (hm : 4 ≤ m) :
    (((RepresentationTheory.MatrixBoundedVectors.boundedVectors (m + 1) (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix 3).filter
        (fun v => v 0 ≠ 0)).filter
      (fun v => ¬(v ⟨1, by omega⟩ = 1))).card =
    (({(0 : Fin m → Fin 3)} : Finset _) ∪
      qFourFinset m (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix).card := by
  apply Finset.card_nbij' (fun v => v ∘ Fin.succ) (fun w => Fin.cons (1 : Fin 3) w)
  · 
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv
    obtain ⟨⟨hv_root, hv0_ne⟩, hv1_ne⟩ := hv
    have hv0_eq := Dn_v0_eq_one (m + 1) (by omega) v hv_root hv0_ne
    have ⟨_, hv_q⟩ := rootCountFinset_mem_iff.mp hv_root
    have hpeel := Dn_peel_at_one m hm v hv_q hv0_eq
    have hv1_ne_val : (v ⟨1, by omega⟩).val ≠ 1 := fun h => hv1_ne (Fin.ext h)
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_singleton]
    by_cases hv1_0 : v ⟨1, by omega⟩ = 0
    · 
      left
      have hv1z : (↑(v ⟨1, by omega⟩) : ℤ) = 0 := by simp [hv1_0]
      rw [hv1z, mul_zero] at hpeel
      exact fin3_fun_zero (by by_contra h; linarith [Dn_posDef m hm _ h])
    · 
      right
      have hv1_2 : v ⟨1, by omega⟩ = (2 : Fin 3) := by
        have h0 : (v ⟨1, by omega⟩).val ≠ 0 := fun h => hv1_0 (Fin.ext h)
        exact Fin.ext (by omega)
      have hv1z : (↑(v ⟨1, by omega⟩) : ℤ) = 2 := by simp [hv1_2]
      rw [hv1z] at hpeel
      simp only [qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by change (v ∘ Fin.succ) ⟨0, by omega⟩ = 2; exact hv1_2, hpeel⟩
  · 
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_singleton] at hw
    simp only [Finset.mem_coe, Finset.mem_filter]
    set v : Fin (m + 1) → Fin 3 := Fin.cons (1 : Fin 3) w
    have hv0z : (↑(v (0 : Fin (m + 1))) : ℤ) = 1 := by simp [v, Fin.cons_zero]
    have hv_ne : (fun i => (↑(v i) : ℤ)) ≠ 0 := by
      intro heq; have := congr_fun heq (0 : Fin (m + 1))
      simp [v, Fin.cons_zero] at this
    have hv1_is_w0 : v ⟨1, by omega⟩ = w ⟨0, by omega⟩ := rfl
    have hpeel := Dn_qform_peel m hm (fun i => (↑(v i) : ℤ))
    have hcomp : (fun i ↦ (↑(v i) : ℤ)) ∘ Fin.succ = fun i ↦ (↑(w i) : ℤ) := by
      funext i; simp [v, Fin.cons_succ]
    rw [hcomp] at hpeel
    rcases hw with rfl | hw_qf
    · 
      have hv1z : (↑(v ⟨1, by omega⟩) : ℤ) = 0 := by rw [hv1_is_w0]; simp
      rw [hv0z, hv1z] at hpeel
      have h_zvec : (fun i ↦ (↑↑((0 : Fin m → Fin 3) i) : ℤ)) = 0 := by ext; simp
      rw [h_zvec, zero_dotProduct] at hpeel
      simp only [one_pow, mul_one, mul_zero, sub_zero, zero_add] at hpeel
      have hv_q : dotProduct (fun i => (↑(v i) : ℤ))
          ((2 • (1 : Matrix _ _ ℤ) - (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix).mulVec
            (fun i => (↑(v i) : ℤ))) = 2 := hpeel
      refine ⟨⟨rootCountFinset_mem_iff.mpr ⟨hv_ne, hv_q⟩, ?_⟩, ?_⟩
      · show v 0 ≠ 0; simp [v, Fin.cons_zero]
      · intro habs; rw [hv1_is_w0] at habs; simp at habs
    · 
      simp only [qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hw_qf
      have hw0z : (↑(w ⟨0, by omega⟩) : ℤ) = 2 := by exact_mod_cast congr_arg Fin.val hw_qf.1
      have hv1z : (↑(v ⟨1, by omega⟩) : ℤ) = 2 := by rw [hv1_is_w0]; exact hw0z
      rw [hv0z, hv1z] at hpeel
      simp only [one_pow, mul_one, hw_qf.2] at hpeel
      
      
      have h_arith : (4 : ℤ) + 2 - 2 * 2 = 2 := by norm_num
      rw [h_arith] at hpeel
      have hv_q : dotProduct (fun i => (↑(v i) : ℤ))
          ((2 • (1 : Matrix _ _ ℤ) - (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) (by omega)).matrix).mulVec
            (fun i => (↑(v i) : ℤ))) = 2 := hpeel
      refine ⟨⟨rootCountFinset_mem_iff.mpr ⟨hv_ne, hv_q⟩, ?_⟩, ?_⟩
      · show v 0 ≠ 0; simp [v, Fin.cons_zero]
      · intro habs; rw [hv1_is_w0, hw_qf.1] at habs; exact absurd habs (by decide)
  · 
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter] at hv
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · exact (Dn_v0_eq_one (m + 1) (by omega) v hv.1.1 hv.1.2).symm ▸ Fin.cons_zero _ _
    · exact Fin.cons_succ _ _ _
  · 
    intro w _; funext i; exact Fin.cons_succ _ _ _


private lemma zero_union_qfour_card (m : ℕ) (hm : 4 ≤ m) :
    (({(0 : Fin m → Fin 3)} : Finset _) ∪
      qFourFinset m (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix).card = 2 := by
  have h_disj : Disjoint ({(0 : Fin m → Fin 3)} : Finset _)
      (qFourFinset m (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D m hm).matrix) := by
    simp only [Finset.disjoint_left, Finset.mem_singleton]
    intro x hx hxqf
    simp only [qFourFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true, decide_eq_true_eq] at hxqf
    rw [hx] at hxqf; simp at hxqf
  rw [Finset.card_union_of_disjoint h_disj, Finset.card_singleton, qFourFinset_card m hm]


private lemma Dn_count : ∀ (n : ℕ) (hn : 4 ≤ n),
    (RepresentationTheory.MatrixBoundedVectors.boundedVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix 3).card =
      n * (n - 1) := by
  suffices h : ∀ (n : ℕ) (hn : 4 ≤ n),
      (RepresentationTheory.MatrixBoundedVectors.boundedVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix 3).card = n * (n - 1) ∧
      ((RepresentationTheory.MatrixBoundedVectors.boundedVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix 3).filter
        (fun v => v ⟨0, by omega⟩ ≠ 0)).card = 2 * (n - 1) from
    fun n hn => (h n hn).1
  intro n; induction n with
  | zero => omega
  | succ m ih =>
    intro hm
    by_cases hm4 : m = 3
    · subst hm4; exact ⟨D4_count, D4_nonzero_count⟩
    · have hm' : 4 ≤ m := by omega
      obtain ⟨ih_total, ih_nonzero⟩ := ih hm'
      set S := RepresentationTheory.MatrixBoundedVectors.boundedVectors (m + 1) (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D (m + 1) hm).matrix 3
      have h_part := Finset.card_filter_add_card_filter_not (s := S) (p := fun v => v 0 = 0)
      have h_zero := Dn_filter_zero_card m hm'
      set S_ne := S.filter (fun v => ¬(v 0 = 0))
      have h_ne_part := Finset.card_filter_add_card_filter_not (s := S_ne)
        (p := fun v => v ⟨1, by omega⟩ = 1)
      have h_v1eq1 := Dn_nonzero_v1eq1_bij m hm'
      have h_v1ne1 := Dn_nonzero_v1ne1_bij m hm'
      have h_union := zero_union_qfour_card m hm'
      have h_v1eq1_val : (S_ne.filter (fun v => v ⟨1, by omega⟩ = 1)).card = 2 * (m - 1) :=
        h_v1eq1.trans ih_nonzero
      have h_v1ne1_val : (S_ne.filter (fun a => ¬a ⟨1, by omega⟩ = 1)).card = 2 :=
        h_v1ne1.trans h_union
      have h_nonzero : S_ne.card = 2 * m := by omega
      refine ⟨?_, ?_⟩
      · 
        have h_zero_val : (S.filter (fun v => v 0 = 0)).card = m * (m - 1) :=
          h_zero.trans ih_total
        have hm1 : m * (m - 1) + 2 * m = (m + 1) * m := by
          
          zify [show 1 ≤ m from by omega]
          ring
        
        change #S = (m + 1) * m
        linarith
      · 
        change S_ne.card = 2 * (m + 1 - 1)
        have : m + 1 - 1 = m := by omega
        omega

private lemma Dn_result (n : ℕ) (hn : 4 ≤ n) :
    (RepresentationTheory.MatrixBoundedVectors.integerVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix).Finite ∧
    Set.ncard (RepresentationTheory.MatrixBoundedVectors.integerVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix) =
      n * (n - 1) := by
  obtain ⟨hfin, hcard⟩ := RepresentationTheory.MatrixBoundedVectors.integerVectors_finite_ncard_eq_boundedVectors_card (Dn_bound n hn)
  exact ⟨hfin, hcard ▸ Dn_count n hn⟩

end DnRootCount

/-- For every natural number at least four, the specified set is finite and has exactly `n * (n - 1)` elements. -/
@[source_ref "Chapter6/Example6.4.9" (role := supporting)]
theorem finite_and_ncard_eq_mul_sub_one (n : ℕ) (hn : 4 ≤ n) :
    (RepresentationTheory.MatrixBoundedVectors.integerVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix).Finite ∧
    Set.ncard (RepresentationTheory.MatrixBoundedVectors.integerVectors n (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix) =
      n * (n - 1) :=
  Dn_result n hn

end RepresentationTheory.FiniteSetCardinality

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.Alignment.Attribute

/-!
# Finite integer matrix models

This module defines a family of finite square integer matrices and proves that each associated
matrix satisfies an auxiliary matrix condition.
-/

namespace RepresentationTheory.FiniteIntegerMatrixModels

/-- An index for a distinguished family of finite square integer matrices. -/
@[source_ref "Chapter2/Theorem2.1.2/Derived3" (role := supporting),
  source_ref "Chapter2/Theorem2.1.2/Derived4" (role := supporting)]
inductive FiniteMatrixModel where
  | A (n : ℕ) (hn : 1 ≤ n)
  | D (n : ℕ) (hn : 4 ≤ n)
  | E6
  | E7
  | E8


/-- The finite size associated with a finite matrix model. -/
def FiniteMatrixModel.rank : FiniteMatrixModel → ℕ
  | .A n _ => n
  | .D n _ => n
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8








/-- The square integer matrix associated with a finite matrix model. -/
def FiniteMatrixModel.matrix : (t : FiniteMatrixModel) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | .A _n _ => fun i j =>
      if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0
  | .D n _ => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨
          (j.val + 1 = i.val ∧ i.val ≤ n - 2)) ∨
         ((i.val = n - 3 ∧ j.val = n - 1) ∨
          (j.val = n - 3 ∧ i.val = n - 1))
      then 1 else 0
  | .E6 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 4) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 4)) ∨
         ((i.val = 2 ∧ j.val = 5) ∨ (j.val = 2 ∧ i.val = 5))
      then 1 else 0
  | .E7 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 5) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 5)) ∨
         ((i.val = 2 ∧ j.val = 6) ∨ (j.val = 2 ∧ i.val = 6))
      then 1 else 0
  | .E8 => fun i j =>
      if ((i.val + 1 = j.val ∧ j.val ≤ 6) ∨
          (j.val + 1 = i.val ∧ i.val ≤ 6)) ∨
         ((i.val = 2 ∧ j.val = 7) ∨ (j.val = 2 ∧ i.val = 7))
      then 1 else 0

set_option backward.isDefEq.respectTransparency false



open Matrix Finset


private theorem pow_eq_zero {M₀ : Type*} [MonoidWithZero M₀] [NoZeroDivisors M₀]
    {a : M₀} {n : ℕ} [NeZero n] (h : a ^ n = 0) : a = 0 :=
  (pow_eq_zero_iff (NeZero.ne n)).mp h





/-- The matrix condition is preserved when indices are relabeled through an equivalence. -/
lemma matrixCondition_of_relabeling {n m : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    {adj' : Matrix (Fin m) (Fin m) ℤ} (σ : Fin n ≃ Fin m)
    (hiso : ∀ i j, adj' (σ i) (σ j) = adj i j)
    (hD : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix m adj' := by
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  
  have rw_adj' : ∀ i j : Fin m, adj' i j = adj (σ.symm i) (σ.symm j) := by
    intro i j
    conv_lhs => rw [show i = σ (σ.symm i) from (σ.apply_symm_apply i).symm,
      show j = σ (σ.symm j) from (σ.apply_symm_apply j).symm]
    exact hiso _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · 
    exact Matrix.IsSymm.ext (fun i j => by rw [rw_adj', rw_adj']; exact hsymm.apply _ _)
  · 
    intro i; rw [rw_adj']; exact hdiag _
  · 
    intro i j; rw [rw_adj']; exact h01 _ _
  · 
    intro i j
    obtain ⟨path, hhead, hlast, hedges⟩ := hconn (σ.symm i) (σ.symm j)
    refine ⟨path.map σ, ?_, ?_, ?_⟩
    · 
      cases path with
      | nil => exact absurd hhead (by simp)
      | cons a _ => simp only [List.map, List.head?]; rw [List.head?] at hhead; exact congr_arg _ (Option.some.inj hhead ▸ σ.apply_symm_apply i)
    · 
      rw [List.getLast?_map]
      rw [hlast]; simp [σ.apply_symm_apply]
    · 
      intro k hk
      have hk' : k + 1 < path.length := by rwa [List.length_map] at hk
      
      change adj' (path.map σ)[k] (path.map σ)[k + 1] = 1
      rw [List.getElem_map, List.getElem_map, hiso]
      exact hedges k hk'
  · 
    intro x hx
    have hx' : x ∘ σ ≠ 0 := by
      intro h; apply hx; ext i
      have := congr_fun h (σ.symm i); simp [Function.comp] at this; exact this
    specialize hpos (x ∘ σ) hx'
    
    suffices heq : dotProduct x ((2 • (1 : Matrix (Fin m) (Fin m) ℤ) - adj').mulVec x) =
        dotProduct (x ∘ σ) ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (x ∘ σ)) by
      linarith
    simp only [dotProduct, mulVec, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Function.comp]
    symm
    apply Fintype.sum_equiv σ; intro i; congr 1
    apply Fintype.sum_equiv σ; intro j
    simp only [hiso, σ.injective.eq_iff]











private def DnQF : ℕ → (ℕ → ℤ) → ℤ
  | 0, x => 2*x 0^2 + 2*x 1^2 + 2*x 2^2 + 2*x 3^2 -
             2*x 0*x 1 - 2*x 1*x 2 - 2*x 1*x 3
  | m + 1, x => 2 * x 0 ^ 2 - 2 * x 0 * x 1 + DnQF m (fun i => x (i + 1))


private lemma DnQF_lower : ∀ (m : ℕ) (x : ℕ → ℤ), (x 0) ^ 2 ≤ DnQF m x := by
  intro m
  induction m with
  | zero =>
    intro x; simp only [DnQF]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2 - x 3), sq_nonneg (x 2 - x 3)]
  | succ k ih =>
    intro x; simp only [DnQF]
    have := ih (fun i => x (i + 1))
    nlinarith [sq_nonneg (x 0 - x 1)]


private lemma DnQF_le_zero_imp : ∀ (m : ℕ) (x : ℕ → ℤ),
    DnQF m x ≤ 0 → ∀ i, i ≤ m + 3 → x i = 0 := by
  intro m
  induction m with
  | zero =>
    intro x hle i hi
    simp only [DnQF] at hle
    have h0 : x 0 = 0 := by
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 0 - x 1),
        sq_nonneg (x 1 - x 2 - x 3), sq_nonneg (x 2 - x 3)]
    have h1 : x 1 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2 - x 3), sq_nonneg (x 2 - x 3)]
    have hle' : 2 * (x 2) ^ 2 + 2 * (x 3) ^ 2 ≤ 0 := by
      have : x 0 ^ 2 = 0 := by rw [h0]; ring
      have : x 1 ^ 2 = 0 := by rw [h1]; ring
      have : x 0 * x 1 = 0 := by rw [h0]; ring
      have : x 1 * x 2 = 0 := by rw [h1]; ring
      have : x 1 * x 3 = 0 := by rw [h1]; ring
      linarith
    have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    have h3 : x 3 = 0 := by nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    interval_cases i <;> assumption
  | succ k ih =>
    intro x hle i hi
    have hshift_lower := DnQF_lower k (fun j => x (j + 1))
    simp only [DnQF] at hle
    have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0)]
    have htail : DnQF k (fun j => x (j + 1)) ≤ 0 := by nlinarith
    rcases i with _ | i
    · exact hx0
    · exact ih (fun j => x (j + 1)) htail i (by omega)









private lemma cartan_Dn_succ' (k : ℕ) (i j : Fin (k + 4)) :
    (2 • (1 : Matrix (Fin (k + 5)) (Fin (k + 5)) ℤ) -
      FiniteMatrixModel.matrix (.D (k + 5) (by omega))) (Fin.succ i) (Fin.succ j) =
    (2 • (1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ) -
      FiniteMatrixModel.matrix (.D (k + 4) (by omega))) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, FiniteMatrixModel.matrix,
    Fin.val_succ, Fin.ext_iff]
  simp_all


private lemma Dn_dotProduct_recurrence' (k : ℕ) (x : Fin (k + 5) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (k + 5)) (Fin (k + 5)) ℤ) -
      FiniteMatrixModel.matrix (.D (k + 5) (by omega))).mulVec x) =
    2 * (x 0) ^ 2 - 2 * x 0 * x ⟨1, by omega⟩ +
    dotProduct (x ∘ Fin.succ) ((2 • (1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ) -
      FiniteMatrixModel.matrix (.D (k + 4) (by omega))).mulVec (x ∘ Fin.succ)) := by
  set C := (2 • (1 : Matrix (Fin (k + 5)) (Fin (k + 5)) ℤ) -
    FiniteMatrixModel.matrix (.D (k + 5) (by omega)))
  set C' := (2 • (1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ) -
    FiniteMatrixModel.matrix (.D (k + 4) (by omega)))
  
  rw [show dotProduct x (C.mulVec x) =
      x 0 * (C.mulVec x) 0 + ∑ i : Fin (k + 4), x (Fin.succ i) * (C.mulVec x) (Fin.succ i) from
    Fin.sum_univ_succ (f := fun i => x i * (C.mulVec x) i)]
  
  have hmv0 : (C.mulVec x) 0 = 2 * x 0 - x ⟨1, by omega⟩ := by
    change ∑ j, C 0 j * x j = _
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ (f := fun j : Fin (k + 4) => C 0 (Fin.succ j) * x (Fin.succ j))]
    have hC00 : C 0 0 = 2 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_zero]
      simp_all
    have hC01 : C 0 (Fin.succ (0 : Fin (k + 4))) = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      simp_all
    have hrest : ∑ i : Fin (k + 3), C 0 (Fin.succ (Fin.succ i)) * x (Fin.succ (Fin.succ i)) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        have : C 0 (Fin.succ (Fin.succ j)) = 0 := by
          simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
            FiniteMatrixModel.matrix, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
          simp_all
        rw [this, zero_mul]
    rw [hC00, hC01, hrest]
    have : x (Fin.succ (0 : Fin (k + 4))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hmv0]
  
  have hmv_succ : ∀ i : Fin (k + 4), (C.mulVec x) (Fin.succ i) =
      C (Fin.succ i) 0 * x 0 + (C'.mulVec (x ∘ Fin.succ)) i := by
    intro i; change ∑ j, C (Fin.succ i) j * x j = _
    rw [Fin.sum_univ_succ]; congr 1
    change _ = ∑ j, C' i j * (x ∘ Fin.succ) j
    apply Finset.sum_congr rfl; intro j _
    simp only [Function.comp]; congr 1
    simp only [C, C']
    exact cartan_Dn_succ' k i j
  simp_rw [hmv_succ, mul_add, Finset.sum_add_distrib]
  have hsum_C0 : ∑ i : Fin (k + 4), x (Fin.succ i) * (C (Fin.succ i) 0 * x 0) =
      -(x ⟨1, by omega⟩ * x 0) := by
    rw [Fin.sum_univ_succ]
    have hC10 : C (Fin.succ (0 : Fin (k + 4))) 0 = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      simp_all
    rw [hC10]
    have hrest : ∀ j : Fin (k + 3), C (Fin.succ (Fin.succ j)) 0 = 0 := by
      intro j
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      simp_all
    have : ∑ j : Fin (k + 3), x (Fin.succ (Fin.succ j)) *
        (C (Fin.succ (Fin.succ j)) 0 * x 0) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [hrest]; ring)
    rw [this, add_zero]
    have : x (Fin.succ (0 : Fin (k + 4))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hsum_C0]
  rw [show ∑ i : Fin (k + 4), x (Fin.succ i) * (C'.mulVec (x ∘ Fin.succ)) i =
    dotProduct (x ∘ Fin.succ) (C'.mulVec (x ∘ Fin.succ)) from rfl]
  ring


private lemma DnQF_eq_dotProduct : ∀ (m : ℕ) (x : Fin (m + 4) → ℤ),
    DnQF m (fun i => if h : i < m + 4 then x ⟨i, h⟩ else 0) =
    dotProduct x ((2 • (1 : Matrix (Fin (m + 4)) (Fin (m + 4)) ℤ) -
      FiniteMatrixModel.matrix (.D (m + 4) (by omega))).mulVec x) := by
  intro m
  induction m with
  | zero =>
    intro x
    simp only [DnQF]
    set C := 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) - FiniteMatrixModel.matrix (.D 4 (by omega))
    have hC : C = !![2,-1,0,0; -1,2,-1,-1; 0,-1,2,0; 0,-1,0,2] := by
      ext i j; fin_cases i <;> fin_cases j <;> decide
    rw [hC]
    simp [dotProduct, mulVec, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  | succ k ih =>
    intro x
    set ext_x : ℕ → ℤ := fun i => if h : i < k + 5 then x ⟨i, h⟩ else 0
    show DnQF (k + 1) ext_x = _
    simp only [DnQF]
    have hx0 : ext_x 0 = x 0 := by simp [ext_x]
    have hx1 : ext_x 1 = x ⟨1, by omega⟩ := by simp [ext_x, show (1 : ℕ) < k + 5 from by omega]
    rw [hx0, hx1]
    set x' : Fin (k + 4) → ℤ := fun j => x ⟨j.val + 1, by omega⟩
    have hshift : (fun i => ext_x (i + 1)) =
        fun i => if h : i < k + 4 then x' ⟨i, h⟩ else 0 := by
      ext i; simp only [ext_x, x']
      by_cases hi : i < k + 4
      · simp [hi, show i + 1 < k + 5 from by omega]
      · simp [hi, show ¬(i + 1 < k + 5) from by omega]
    rw [hshift, ih x']
    rw [Dn_dotProduct_recurrence' k x]
    have hx'_eq : x' = x ∘ Fin.succ := by ext j; simp [x', Function.comp, Fin.succ]
    rw [hx'_eq]


private lemma Dn_posDef (n : ℕ) (hn : 4 ≤ n) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      FiniteMatrixModel.matrix (.D n hn)).mulVec x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  intro x hx
  rw [← DnQF_eq_dotProduct m x]
  by_contra h
  push Not at h
  have hzero := DnQF_le_zero_imp m
    (fun i => if hi : i < m + 4 then x ⟨i, hi⟩ else 0) h
  apply hx; ext ⟨i, hi⟩
  have := hzero i (by omega)
  simp only [show (i < m + 4) = True from by simp; omega, dite_true] at this
  exact this









private def pathQF : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | 1, x => 2 * x 0 ^ 2
  | n + 2, x => 2 * x 0 ^ 2 - 2 * x 0 * x 1 + pathQF (n + 1) (fun i => x (i + 1))



private lemma pathQF_lower : ∀ (m : ℕ) (x : ℕ → ℤ),
    (x 0) ^ 2 + (x m) ^ 2 ≤ pathQF (m + 1) x := by
  intro m
  induction m with
  | zero => intro x; simp [pathQF]; nlinarith [sq_nonneg (x 0)]
  | succ k ih =>
    intro x
    simp only [pathQF]
    have ih' := ih (fun i => x (i + 1))
    
    
    nlinarith [sq_nonneg (x 0 - x 1)]


private lemma pathQF_le_zero_imp : ∀ (m : ℕ) (x : ℕ → ℤ),
    pathQF (m + 1) x ≤ 0 → ∀ i, i ≤ m → x i = 0 := by
  intro m
  induction m with
  | zero =>
    intro x hle i hi
    have : x 0 = 0 := by
      simp [pathQF] at hle; nlinarith [sq_nonneg (x 0)]
    interval_cases i; exact this
  | succ k ih =>
    intro x hle i hi
    
    have htb := pathQF_lower k (fun j => x (j + 1))
    
    simp only [pathQF] at hle
    
    have hx0 : x 0 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0), sq_nonneg (x (k + 1))]
    have htail : pathQF (k + 1) (fun j => x (j + 1)) ≤ 0 := by nlinarith
    rcases i with _ | i
    · exact hx0
    · exact ih (fun j => x (j + 1)) htail i (by omega)


private lemma cartan_An_succ (k : ℕ) (i j : Fin (k + 1)) :
    (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      FiniteMatrixModel.matrix (.A (k + 2) (by omega))) (Fin.succ i) (Fin.succ j) =
    (2 • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) -
      FiniteMatrixModel.matrix (.A (k + 1) (by omega))) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, FiniteMatrixModel.matrix,
    Fin.val_succ, Fin.ext_iff]
  simp_all


private lemma cartan_An_zero_ge2 (k : ℕ) (j : Fin k) :
    (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      FiniteMatrixModel.matrix (.A (k + 2) (by omega))) 0 (Fin.succ (Fin.succ j)) = 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, FiniteMatrixModel.matrix,
    Fin.val_zero, Fin.val_succ, Fin.ext_iff]
  simp_all


private lemma cartan_An_succ_zero (k : ℕ) (i : Fin (k + 1)) :
    (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      FiniteMatrixModel.matrix (.A (k + 2) (by omega))) (Fin.succ i) 0 =
    if (i : ℕ) = 0 then -1 else 0 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    FiniteMatrixModel.matrix, Fin.val_zero, Fin.val_succ, Fin.ext_iff]
  split_ifs <;> simp_all


private lemma An_dotProduct_recurrence (k : ℕ) (x : Fin (k + 2) → ℤ) :
    dotProduct x ((2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
      FiniteMatrixModel.matrix (.A (k + 2) (by omega))).mulVec x) =
    2 * (x 0) ^ 2 - 2 * x 0 * x ⟨1, by omega⟩ +
    dotProduct (x ∘ Fin.succ) ((2 • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) -
      FiniteMatrixModel.matrix (.A (k + 1) (by omega))).mulVec (x ∘ Fin.succ)) := by
  set C := (2 • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) -
    FiniteMatrixModel.matrix (.A (k + 2) (by omega)))
  set C' := (2 • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) -
    FiniteMatrixModel.matrix (.A (k + 1) (by omega)))
  
  rw [show dotProduct x (C.mulVec x) =
      x 0 * (C.mulVec x) 0 + ∑ i : Fin (k + 1), x (Fin.succ i) * (C.mulVec x) (Fin.succ i) from
    Fin.sum_univ_succ (f := fun i => x i * (C.mulVec x) i)]
  
  have hmv0 : (C.mulVec x) 0 = 2 * x 0 - x ⟨1, by omega⟩ := by
    change ∑ j, C 0 j * x j = _
    rw [Fin.sum_univ_succ]
    
    have hC00 : C 0 0 = 2 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_zero]
      simp_all
    
    rw [Fin.sum_univ_succ (f := fun j : Fin (k + 1) => C 0 (Fin.succ j) * x (Fin.succ j))]
    
    have hC01 : C 0 (Fin.succ (0 : Fin (k + 1))) = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      simp_all
    
    have hrest : ∑ i : Fin k, C 0 (Fin.succ (Fin.succ i)) * x (Fin.succ (Fin.succ i)) = 0 := by
      apply Finset.sum_eq_zero; intro j _; rw [show C 0 (Fin.succ (Fin.succ j)) = 0 from cartan_An_zero_ge2 k j, zero_mul]
    rw [hC00, hC01, hrest]
    have : x (Fin.succ (0 : Fin (k + 1))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hmv0]
  
  have hmv_succ : ∀ i : Fin (k + 1), (C.mulVec x) (Fin.succ i) =
      C (Fin.succ i) 0 * x 0 + (C'.mulVec (x ∘ Fin.succ)) i := by
    intro i
    change ∑ j, C (Fin.succ i) j * x j = _
    rw [Fin.sum_univ_succ]
    change C (Fin.succ i) 0 * x 0 + ∑ j : Fin (k + 1), C (Fin.succ i) (Fin.succ j) *
      x (Fin.succ j) = _
    congr 1
    change _ = ∑ j, C' i j * (x ∘ Fin.succ) j
    apply Finset.sum_congr rfl; intro j _
    simp only [Function.comp, C, C']
    rw [cartan_An_succ]
  simp_rw [hmv_succ]
  
  simp only [mul_add, Finset.sum_add_distrib]
  
  
  have hsum_C0 : ∑ i : Fin (k + 1), x (Fin.succ i) * (C (Fin.succ i) 0 * x 0) =
      -(x ⟨1, by omega⟩ * x 0) := by
    
    rw [Fin.sum_univ_succ]
    
    have hC10 : C (Fin.succ (0 : Fin (k + 1))) 0 = -1 := by
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      simp_all
    rw [hC10]
    
    have hrest : ∀ j : Fin k, C (Fin.succ (Fin.succ j)) 0 = 0 := by
      intro j
      simp only [C, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        FiniteMatrixModel.matrix, Fin.val_succ, Fin.val_zero, Fin.ext_iff]
      simp_all
    have : ∑ j : Fin k, x (Fin.succ (Fin.succ j)) *
        (C (Fin.succ (Fin.succ j)) 0 * x 0) = 0 := by
      apply Finset.sum_eq_zero; intro j _; rw [hrest]; ring
    rw [this, add_zero]
    have : x (Fin.succ (0 : Fin (k + 1))) = x ⟨1, by omega⟩ := by congr 1
    rw [this]; ring
  rw [hsum_C0]
  
  
  rw [show ∑ i : Fin (k + 1), x (Fin.succ i) * (C'.mulVec (x ∘ Fin.succ)) i =
    dotProduct (x ∘ Fin.succ) (C'.mulVec (x ∘ Fin.succ)) from rfl]
  ring



private lemma pathQF_eq_dotProduct (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ) :
    pathQF n (fun i => if h : i < n then x ⟨i, h⟩ else 0) =
    dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      FiniteMatrixModel.matrix (.A n hn)).mulVec x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero =>
    
    simp only [pathQF, show (0 : ℕ) < 1 from by omega, dite_true]
    simp only [dotProduct, mulVec]
    simp only [show Finset.univ (α := Fin (0 + 1)) = {0} from rfl, Finset.sum_singleton]
    have hmat : (2 • (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℤ) -
        FiniteMatrixModel.matrix (.A (0 + 1) (by omega))) 0 0 = 2 := by
      change (2 : ℤ) = 2
      rfl
    rw [hmat]; simp ; ring
  | succ k ih =>
    
    set ext_x : ℕ → ℤ := fun i => if h : i < k + 2 then x ⟨i, h⟩ else 0
    change pathQF (k + 2) ext_x = _
    simp only [pathQF]
    
    have hx0 : ext_x 0 = x 0 := by simp [ext_x]
    have hx1 : ext_x 1 = x ⟨1, by omega⟩ := by
      simp [ext_x, show (1 : ℕ) < k + 2 from by omega]
    rw [hx0, hx1]
    
    set x' : Fin (k + 1) → ℤ := fun j => x ⟨j.val + 1, by omega⟩
    have hshift : (fun i => ext_x (i + 1)) =
        fun i => if h : i < k + 1 then x' ⟨i, h⟩ else 0 := by
      ext i; simp only [ext_x, x']
      by_cases hi : i < k + 1
      · simp [hi, show i + 1 < k + 2 from by omega]
      · simp [hi, show ¬(i + 1 < k + 2) from by omega]
    rw [hshift, ih (by omega) x']
    
    rw [An_dotProduct_recurrence k x]
    
    have hx'_eq : x' = x ∘ Fin.succ := by ext j; simp [x', Function.comp, Fin.succ]
    rw [hx'_eq]


private lemma An_posDef (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : Fin n → ℤ, x ≠ 0 →
    0 < dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
      FiniteMatrixModel.matrix (.A n hn)).mulVec x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro x hx
  rw [← pathQF_eq_dotProduct (m + 1) (by omega) x]
  by_contra h
  push Not at h
  have hzero := pathQF_le_zero_imp m
    (fun i => if hi : i < m + 1 then x ⟨i, hi⟩ else 0) h
  apply hx; ext ⟨i, hi⟩
  have := hzero i (by omega)
  simp only [show (i < m + 1) = True from by simp; omega, dite_true] at this
  exact this


private lemma An_isDynkin (n : ℕ) (hn : 1 ≤ n) :
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n (FiniteMatrixModel.matrix (.A n hn)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · 
    exact Matrix.IsSymm.ext (fun i j => by
      simp only [FiniteMatrixModel.matrix]; congr 1; exact propext or_comm)
  · 
    intro i; simp only [FiniteMatrixModel.matrix]; split_ifs with h
    · exact absurd h (by push Not; constructor <;> omega)
    · rfl
  · 
    intro i j; simp only [FiniteMatrixModel.matrix]; split_ifs <;> simp
  · 
    intro i j
    by_cases hij : i.val ≤ j.val
    · 
      refine ⟨List.ofFn (fun (k : Fin (j.val - i.val + 1)) =>
        (⟨i.val + k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · 
        rw [List.ofFn_succ, List.head?_cons]; simp
      · 
        rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; ext; simp [Fin.last]; omega
      · 
        intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, FiniteMatrixModel.matrix, Fin.val_mk]
        rw [if_pos (Or.inl (by omega))]
    · 
      push Not at hij
      refine ⟨List.ofFn (fun (k : Fin (i.val - j.val + 1)) =>
        (⟨i.val - k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · 
        rw [List.ofFn_succ, List.head?_cons]; simp
      · 
        rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; ext; simp [Fin.last]; omega
      · 
        intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, FiniteMatrixModel.matrix, Fin.val_mk]
        rw [if_pos (Or.inr (by omega))]
  · 
    exact An_posDef n hn


private lemma Dn_isDynkin (n : ℕ) (hn : 4 ≤ n) :
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n (FiniteMatrixModel.matrix (.D n hn)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · 
    exact Matrix.IsSymm.ext (fun i j => by
      simp only [FiniteMatrixModel.matrix]; congr 1; exact propext ⟨fun h => by tauto, fun h => by tauto⟩)
  · 
    intro i; simp only [FiniteMatrixModel.matrix]; split_ifs with h
    · exfalso; rcases h with (⟨h1, _⟩ | ⟨h2, _⟩) | (⟨h3, h4⟩ | ⟨h5, h6⟩) <;> omega
    · rfl
  · 
    intro i j; simp only [FiniteMatrixModel.matrix]; split_ifs <;> simp
  · 
    
    intro i j
    
    have main_asc : ∀ (a b : Fin n), a.val < n - 1 → b.val < n - 1 → a.val ≤ b.val →
        ∃ path : List (Fin n), path.head? = some a ∧ path.getLast? = some b ∧
        ∀ k, (h : k + 1 < path.length) →
          (FiniteMatrixModel.matrix (.D n hn)) (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1 := by
      intro a b ha hb hab
      refine ⟨List.ofFn (fun (k : Fin (b.val - a.val + 1)) =>
        (⟨a.val + k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · rw [List.ofFn_succ, List.head?_cons]; simp
      · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; simp only [Fin.ext_iff, Fin.val_last]; omega
      · intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, FiniteMatrixModel.matrix, Fin.val_mk]
        rw [if_pos]; left; left; constructor <;> omega
    
    have main_desc : ∀ (a b : Fin n), a.val < n - 1 → b.val < n - 1 → b.val < a.val →
        ∃ path : List (Fin n), path.head? = some a ∧ path.getLast? = some b ∧
        ∀ k, (h : k + 1 < path.length) →
          (FiniteMatrixModel.matrix (.D n hn)) (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1 := by
      intro a b ha hb hab
      refine ⟨List.ofFn (fun (k : Fin (a.val - b.val + 1)) =>
        (⟨a.val - k.val, by omega⟩ : Fin n)), ?_, ?_, ?_⟩
      · rw [List.ofFn_succ, List.head?_cons]; simp
      · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
        congr 1; simp only [Fin.ext_iff, Fin.val_last]; omega
      · intro k hk
        simp only [List.length_ofFn] at hk
        simp only [List.get_eq_getElem, List.getElem_ofFn, FiniteMatrixModel.matrix, Fin.val_mk]
        rw [if_pos]; left; right; constructor <;> omega
    
    by_cases hi : i.val = n - 1
    · by_cases hj : j.val = n - 1
      · 
        have hij : i = j := Fin.ext (by omega)
        subst hij
        exact ⟨[i], by simp, by simp, fun k hk => by simp at hk⟩
      · 
        have hjlt : j.val < n - 1 := by omega
        
        rcases Nat.lt_or_eq_of_le (show j.val ≤ n - 2 by omega) with hjlt2 | hjn2
        · rcases Nat.lt_or_eq_of_le (show j.val ≤ n - 3 by omega) with hjlt3 | hjn3
          · 
            obtain ⟨path, hhead, hlast, hedges⟩ := main_desc ⟨n - 3, by omega⟩ j
              (show (n - 3 : ℕ) < n - 1 by omega) hjlt (show j.val < n - 3 from hjlt3)
            refine ⟨⟨n - 1, by omega⟩ :: path, ?_, ?_, ?_⟩
            · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
            · cases path with
              | nil => simp at hhead
              | cons p ps => simp only [List.getLast?_cons_cons]; exact hlast
            · intro k hk
              simp only [List.length_cons] at hk
              match k with
              | 0 =>
                cases path with
                | nil => simp at hhead
                | cons p ps =>
                  simp only [List.head?_cons, Option.some.injEq] at hhead
                  simp only [List.get_eq_getElem, List.getElem_cons_zero,
                    List.getElem_cons_succ]
                  rw [hhead]; simp only [FiniteMatrixModel.matrix]
                  rw [if_pos]; right; right; refine ⟨?_, ?_⟩ <;> dsimp
              | k + 1 =>
                simp only [List.get_eq_getElem, List.getElem_cons_succ]
                exact hedges k (by omega)
          · 
            refine ⟨[⟨n - 1, by omega⟩, ⟨n - 3, by omega⟩], ?_, ?_, ?_⟩
            · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
            · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
              exact Fin.ext (by dsimp; omega)
            · intro k hk
              simp only [List.length_cons, List.length_nil] at hk
              match k with
              | 0 =>
                dsimp only [List.get]; simp only [FiniteMatrixModel.matrix]
                rw [if_pos]; right; right; refine ⟨?_, ?_⟩ <;> dsimp
        · 
          refine ⟨[⟨n - 1, by omega⟩, ⟨n - 3, by omega⟩, ⟨n - 2, by omega⟩], ?_, ?_, ?_⟩
          · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
          · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
            exact Fin.ext (by dsimp; omega)
          · intro k hk
            simp only [List.length_cons, List.length_nil] at hk
            match k with
            | 0 =>
              dsimp only [List.get]; simp only [FiniteMatrixModel.matrix]
              rw [if_pos]; right; right; refine ⟨?_, ?_⟩ <;> dsimp
            | 1 =>
              dsimp only [List.get]; simp only [FiniteMatrixModel.matrix]
              
              rw [if_pos]; left; left; refine ⟨?_, ?_⟩ <;> omega
    · by_cases hj : j.val = n - 1
      · 
        have hilt : i.val < n - 1 := by omega
        rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 2 by omega) with hilt2 | hin2
        · rcases Nat.lt_or_eq_of_le (show i.val ≤ n - 3 by omega) with hilt3 | hin3
          · 
            obtain ⟨path, hhead, hlast, hedges⟩ := main_asc i ⟨n - 3, by omega⟩
              hilt (show (n - 3 : ℕ) < n - 1 by omega)
              (show i.val ≤ n - 3 from Nat.le_of_lt hilt3)
            refine ⟨path ++ [⟨n - 1, by omega⟩], ?_, ?_, ?_⟩
            · cases path with
              | nil => simp at hhead
              | cons p ps =>
                simp only [List.cons_append, List.head?_cons]
                exact hhead
            · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
              simp only [List.getLast?_singleton, Option.some.injEq]
              exact Fin.ext (by dsimp; omega)
            · intro k hk
              simp only [List.length_append, List.length_cons, List.length_nil] at hk
              by_cases hk_main : k + 1 < path.length
              · simp only [List.get_eq_getElem]
                rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
                exact hedges k hk_main
              · 
                have hk_eq : k + 1 = path.length := by omega
                have hpne : path ≠ [] := by
                  cases path with | nil => simp at hhead | cons _ _ => exact List.cons_ne_nil _ _
                
                have hpath_last : path.getLast hpne = ⟨n - 3, by omega⟩ := by
                  have h := List.getLast?_eq_getLast_of_ne_nil hpne
                  rw [hlast] at h; exact Option.some.inj h.symm
                
                have hk_last : k = path.length - 1 := by omega
                have hpath_k : path[k]'(by omega) = ⟨n - 3, by omega⟩ := by
                  subst hk_last
                  rw [List.getLast_eq_getElem] at hpath_last; exact hpath_last
                
                have hsucc : (path ++ [⟨n - 1, by omega⟩])[k + 1]'(by simp; omega) =
                    ⟨n - 1, by omega⟩ := by
                  rw [List.getElem_append_right (by omega)]
                  simp [hk_eq]
                simp only [List.get_eq_getElem]
                
                change (FiniteMatrixModel.matrix (.D n hn))
                  ((path ++ [⟨n - 1, by omega⟩])[k]'(by simp; omega))
                  ((path ++ [⟨n - 1, by omega⟩])[k + 1]'(by simp; omega)) = 1
                rw [List.getElem_append_left (by omega), hpath_k, hsucc]
                simp only [FiniteMatrixModel.matrix]
                rw [if_pos]; right; left; refine ⟨?_, ?_⟩ <;> dsimp
          · 
            refine ⟨[⟨n - 3, by omega⟩, ⟨n - 1, by omega⟩], ?_, ?_, ?_⟩
            · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
            · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
              exact Fin.ext (by dsimp; omega)
            · intro k hk
              simp only [List.length_cons, List.length_nil] at hk
              match k with
              | 0 =>
                dsimp only [List.get]; simp only [FiniteMatrixModel.matrix]
                rw [if_pos]; right; left; refine ⟨?_, ?_⟩ <;> dsimp
        · 
          refine ⟨[⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩, ⟨n - 1, by omega⟩], ?_, ?_, ?_⟩
          · simp only [List.head?_cons, Option.some.injEq]; exact Fin.ext (by dsimp; omega)
          · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq]
            exact Fin.ext (by dsimp; omega)
          · intro k hk
            simp only [List.length_cons, List.length_nil] at hk
            match k with
            | 0 =>
              dsimp only [List.get]; simp only [FiniteMatrixModel.matrix]
              
              rw [if_pos]; left; right; refine ⟨?_, ?_⟩ <;> omega
            | 1 =>
              dsimp only [List.get]; simp only [FiniteMatrixModel.matrix]
              rw [if_pos]; right; left; refine ⟨?_, ?_⟩ <;> dsimp
      · 
        by_cases hij : i.val ≤ j.val
        · exact main_asc i j (by omega) (by omega) hij
        · exact main_desc i j (by omega) (by omega) (by omega)
  · 
    exact Dn_posDef n hn


private def E6_treePath : Fin 6 → Fin 6 → List (Fin 6) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 5]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 5]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 5]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 2, 5]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 3, 2, 5]
  | 5, 0 => [5, 2, 1, 0] | 5, 1 => [5, 2, 1] | 5, 2 => [5, 2]
  | 5, 3 => [5, 2, 3] | 5, 4 => [5, 2, 3, 4] | 5, 5 => [5]




private lemma E6_isDynkin : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 6 (FiniteMatrixModel.matrix .E6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · 
    exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> decide)
  · 
    intro i; fin_cases i <;> decide
  · 
    intro i j; fin_cases i <;> fin_cases j <;> decide
  · 
    intro i j
    refine ⟨E6_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E6_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | _))) <;>
        (first | omega | (dsimp only [E6_treePath, List.get]; decide))
  · 
    
    
    
    
    intro x hx
    
    set a := x 0; set b := x 1; set c := x 2; set d := x 3; set e := x 4; set f := x 5
    
    suffices h60 : 0 < 60 * dotProduct x
        ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) - FiniteMatrixModel.matrix .E6).mulVec x) by nlinarith
    
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) -
        FiniteMatrixModel.matrix .E6).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*c*f := by
      
      set C := 2 • (1 : Matrix (Fin 6) (Fin 6) ℤ) - FiniteMatrixModel.matrix .E6
      have hC : C = !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,-1;
                        0,0,-1,2,-1,0; 0,0,0,-1,2,0; 0,0,-1,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    
    rw [expand]
    have sos : 60 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*c*f) =
        30*(2*a-b)^2 + 10*(3*b-2*c)^2 + 5*(4*c-3*d-3*f)^2 +
        3*(5*d-4*e-3*f)^2 + 18*(2*e-f)^2 + 30*f^2 := by ring
    rw [sos]
    
    by_contra h_le
    push Not at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*f)
    have s4 := sq_nonneg (5*d-4*e-3*f)
    have s5 := sq_nonneg (2*e-f)
    have s6 := sq_nonneg f
    
    have hf : f = 0 := by
      have : f ^ 2 ≤ 0 := by nlinarith
      have := le_antisymm this (sq_nonneg f)
      exact pow_eq_zero (show f ^ 2 = 0 from this)
    have he : e = 0 := by
      have : (2*e-f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*e-f)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*f)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*f) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*f)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)


private def E7_treePath : Fin 7 → Fin 7 → List (Fin 7) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 3, 4, 5]
  | 0, 6 => [0, 1, 2, 6]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 3, 4, 5]
  | 1, 6 => [1, 2, 6]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 3, 4, 5]
  | 2, 6 => [2, 6]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 4, 5]
  | 3, 6 => [3, 2, 6]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 5]
  | 4, 6 => [4, 3, 2, 6]
  | 5, 0 => [5, 4, 3, 2, 1, 0] | 5, 1 => [5, 4, 3, 2, 1] | 5, 2 => [5, 4, 3, 2]
  | 5, 3 => [5, 4, 3] | 5, 4 => [5, 4] | 5, 5 => [5]
  | 5, 6 => [5, 4, 3, 2, 6]
  | 6, 0 => [6, 2, 1, 0] | 6, 1 => [6, 2, 1] | 6, 2 => [6, 2]
  | 6, 3 => [6, 2, 3] | 6, 4 => [6, 2, 3, 4] | 6, 5 => [6, 2, 3, 4, 5]
  | 6, 6 => [6]

set_option maxHeartbeats 400000 in

private lemma E7_isDynkin : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 7 (FiniteMatrixModel.matrix .E7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> decide)
  · intro i; fin_cases i <;> decide
  · intro i j; fin_cases i <;> fin_cases j <;> decide
  · 
    intro i j
    refine ⟨E7_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E7_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | (_ | _)))) <;>
        (first | omega | (dsimp only [E7_treePath, List.get]; decide))
  · 
    
    
    intro x hx
    set a := x 0; set b := x 1; set c := x 2; set d := x 3
    set e := x 4; set f := x 5; set g := x 6
    suffices h420 : 0 < 420 * dotProduct x
        ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - FiniteMatrixModel.matrix .E7).mulVec x) by nlinarith
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) -
        FiniteMatrixModel.matrix .E7).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*c*g := by
      set C := 2 • (1 : Matrix (Fin 7) (Fin 7) ℤ) - FiniteMatrixModel.matrix .E7
      have hC : C = !![2,-1,0,0,0,0,0; -1,2,-1,0,0,0,0; 0,-1,2,-1,0,0,-1;
                        0,0,-1,2,-1,0,0; 0,0,0,-1,2,-1,0; 0,0,0,0,-1,2,0;
                        0,0,-1,0,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    rw [expand]
    have sos : 420 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*c*g) =
        210*(2*a-b)^2 + 70*(3*b-2*c)^2 + 35*(4*c-3*d-3*g)^2 + 21*(5*d-4*e-3*g)^2 +
        14*(6*e-5*f-3*g)^2 + 10*(7*f-3*g)^2 + 120*g^2 := by ring
    rw [sos]
    by_contra h_le
    push Not at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*g)
    have s4 := sq_nonneg (5*d-4*e-3*g)
    have s5 := sq_nonneg (6*e-5*f-3*g)
    have s6 := sq_nonneg (7*f-3*g)
    have s7 := sq_nonneg g
    have hg : g = 0 := by
      have : g ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero (le_antisymm this (sq_nonneg g))
    have hf : f = 0 := by
      have : (7*f-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (7*f-3*g)))
      omega
    have he : e = 0 := by
      have : (6*e-5*f-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (6*e-5*f-3*g)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*g)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*g) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*g)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have h := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)


private def E8_treePath : Fin 8 → Fin 8 → List (Fin 8) := fun i j =>
  match i, j with
  | 0, 0 => [0] | 0, 1 => [0, 1] | 0, 2 => [0, 1, 2]
  | 0, 3 => [0, 1, 2, 3] | 0, 4 => [0, 1, 2, 3, 4] | 0, 5 => [0, 1, 2, 3, 4, 5]
  | 0, 6 => [0, 1, 2, 3, 4, 5, 6] | 0, 7 => [0, 1, 2, 7]
  | 1, 0 => [1, 0] | 1, 1 => [1] | 1, 2 => [1, 2]
  | 1, 3 => [1, 2, 3] | 1, 4 => [1, 2, 3, 4] | 1, 5 => [1, 2, 3, 4, 5]
  | 1, 6 => [1, 2, 3, 4, 5, 6] | 1, 7 => [1, 2, 7]
  | 2, 0 => [2, 1, 0] | 2, 1 => [2, 1] | 2, 2 => [2]
  | 2, 3 => [2, 3] | 2, 4 => [2, 3, 4] | 2, 5 => [2, 3, 4, 5]
  | 2, 6 => [2, 3, 4, 5, 6] | 2, 7 => [2, 7]
  | 3, 0 => [3, 2, 1, 0] | 3, 1 => [3, 2, 1] | 3, 2 => [3, 2]
  | 3, 3 => [3] | 3, 4 => [3, 4] | 3, 5 => [3, 4, 5]
  | 3, 6 => [3, 4, 5, 6] | 3, 7 => [3, 2, 7]
  | 4, 0 => [4, 3, 2, 1, 0] | 4, 1 => [4, 3, 2, 1] | 4, 2 => [4, 3, 2]
  | 4, 3 => [4, 3] | 4, 4 => [4] | 4, 5 => [4, 5]
  | 4, 6 => [4, 5, 6] | 4, 7 => [4, 3, 2, 7]
  | 5, 0 => [5, 4, 3, 2, 1, 0] | 5, 1 => [5, 4, 3, 2, 1] | 5, 2 => [5, 4, 3, 2]
  | 5, 3 => [5, 4, 3] | 5, 4 => [5, 4] | 5, 5 => [5]
  | 5, 6 => [5, 6] | 5, 7 => [5, 4, 3, 2, 7]
  | 6, 0 => [6, 5, 4, 3, 2, 1, 0] | 6, 1 => [6, 5, 4, 3, 2, 1] | 6, 2 => [6, 5, 4, 3, 2]
  | 6, 3 => [6, 5, 4, 3] | 6, 4 => [6, 5, 4] | 6, 5 => [6, 5]
  | 6, 6 => [6] | 6, 7 => [6, 5, 4, 3, 2, 7]
  | 7, 0 => [7, 2, 1, 0] | 7, 1 => [7, 2, 1] | 7, 2 => [7, 2]
  | 7, 3 => [7, 2, 3] | 7, 4 => [7, 2, 3, 4] | 7, 5 => [7, 2, 3, 4, 5]
  | 7, 6 => [7, 2, 3, 4, 5, 6] | 7, 7 => [7]

set_option maxHeartbeats 1600000 in

private lemma E8_isDynkin : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 8 (FiniteMatrixModel.matrix .E8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.IsSymm.ext (fun i j => by fin_cases i <;> fin_cases j <;> decide)
  · intro i; fin_cases i <;> decide
  · intro i j; fin_cases i <;> fin_cases j <;> decide
  · 
    intro i j
    refine ⟨E8_treePath i j, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> rfl
    · fin_cases i <;> fin_cases j <;> rfl
    · intro k hk
      fin_cases i <;> fin_cases j <;>
        simp only [E8_treePath, List.length_cons, List.length_nil, Nat.reduceAdd] at hk <;>
        rcases k with _ | (_ | (_ | (_ | (_ | (_ | _))))) <;>
        (first | omega | (dsimp only [E8_treePath, List.get]; decide))
  · 
    
    
    intro x hx
    set a := x 0; set b := x 1; set c := x 2; set d := x 3
    set e := x 4; set f := x 5; set g := x 6; set h := x 7
    suffices h840 : 0 < 840 * dotProduct x
        ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - FiniteMatrixModel.matrix .E8).mulVec x) by nlinarith
    have expand : dotProduct x ((2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) -
        FiniteMatrixModel.matrix .E8).mulVec x) =
        2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 + 2*h^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*f*g - 2*c*h := by
      set C := 2 • (1 : Matrix (Fin 8) (Fin 8) ℤ) - FiniteMatrixModel.matrix .E8
      have hC : C = !![2,-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,-1;
                        0,0,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
                        0,0,0,0,0,-1,2,0; 0,0,-1,0,0,0,0,2] := by
        ext i j; fin_cases i <;> fin_cases j <;> decide
      rw [hC]
      simp [dotProduct, mulVec, Fin.sum_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    rw [expand]
    have sos : 840 * (2*a^2 + 2*b^2 + 2*c^2 + 2*d^2 + 2*e^2 + 2*f^2 + 2*g^2 + 2*h^2 -
        2*a*b - 2*b*c - 2*c*d - 2*d*e - 2*e*f - 2*f*g - 2*c*h) =
        420*(2*a-b)^2 + 140*(3*b-2*c)^2 + 70*(4*c-3*d-3*h)^2 + 42*(5*d-4*e-3*h)^2 +
        28*(6*e-5*f-3*h)^2 + 20*(7*f-6*g-3*h)^2 + 15*(8*g-3*h)^2 + 105*h^2 := by ring
    rw [sos]
    by_contra h_le
    push Not at h_le
    have s1 := sq_nonneg (2*a-b)
    have s2 := sq_nonneg (3*b-2*c)
    have s3 := sq_nonneg (4*c-3*d-3*h)
    have s4 := sq_nonneg (5*d-4*e-3*h)
    have s5 := sq_nonneg (6*e-5*f-3*h)
    have s6 := sq_nonneg (7*f-6*g-3*h)
    have s7 := sq_nonneg (8*g-3*h)
    have s8 := sq_nonneg h
    have hh : h = 0 := by
      have : h ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero (le_antisymm this (sq_nonneg h))
    have hg : g = 0 := by
      have : (8*g-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (8*g-3*h)))
      omega
    have hf : f = 0 := by
      have : (7*f-6*g-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (7*f-6*g-3*h)))
      omega
    have he : e = 0 := by
      have : (6*e-5*f-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (6*e-5*f-3*h)))
      omega
    have hd : d = 0 := by
      have : (5*d-4*e-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (5*d-4*e-3*h)))
      omega
    have hc : c = 0 := by
      have : (4*c-3*d-3*h) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (4*c-3*d-3*h)))
      omega
    have hb : b = 0 := by
      have : (3*b-2*c) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (3*b-2*c)))
      omega
    have ha : a = 0 := by
      have : (2*a-b) ^ 2 ≤ 0 := by nlinarith
      have := pow_eq_zero (le_antisymm this (sq_nonneg (2*a-b)))
      omega
    exact hx (funext fun i => by fin_cases i <;> assumption)


/-- The matrix associated with every finite matrix model satisfies the matrix condition. -/
lemma matrix_satisfies_condition (t : FiniteMatrixModel) :
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix t.rank t.matrix := by
  cases t with
  | A n hn => exact An_isDynkin n hn
  | D n hn => exact Dn_isDynkin n hn
  | E6 => exact E6_isDynkin
  | E7 => exact E7_isDynkin
  | E8 => exact E8_isDynkin


end RepresentationTheory.FiniteIntegerMatrixModels

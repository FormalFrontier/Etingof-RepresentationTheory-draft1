/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.FiniteIntegerMatrixModels
import RepresentationTheory.Matrix.TwoIdentitySub
import RepresentationTheory.Alignment.Attribute

/-!
# Finite Simply Laced Dynkin Diagrams
-/

set_option backward.isDefEq.respectTransparency false

namespace RepresentationTheory.DynkinDiagram.FiniteSimplyLaced

open Matrix Finset


/-- The integer Cartan matrix associated with a finite simply laced Dynkin type. -/
def cartanMatrix (t : FiniteIntegerMatrixModels.FiniteMatrixModel) : Matrix (Fin t.rank) (Fin t.rank) ℤ :=
  2 • (1 : Matrix (Fin t.rank) (Fin t.rank) ℤ) - t.matrix



/-- The degree of a vertex determined by an integer adjacency matrix. -/
def vertexDegree {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) : ℕ :=
  (univ.filter (fun j => adj v j = 1)).card







/-- Parser description for the notation denoting the degree of a vertex in an adjacency matrix. -/
macro (name := vertexDegreeSyntax) "cartan_det" : tactic =>
  `(tactic|
    (simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.zero_succAbove,
        Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, Fin.val_zero, Fin.val_succ,
        Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const, mul_zero, zero_mul,
        add_zero, zero_add, neg_zero, mul_neg, neg_neg, mul_one, one_mul, pow_zero, pow_succ]
     <;>
     norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.head_fin_const, Matrix.vecHead,
        Matrix.vecTail]))

















private def pathCartan (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val = j.val then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0


private lemma pathCartan_diag {n : ℕ} {i j : Fin n} (h : i.val = j.val) :
    pathCartan n i j = 2 := by simp only [pathCartan, if_pos h]


private lemma pathCartan_offdiag {n : ℕ} {i j : Fin n}
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : pathCartan n i j = -1 := by
  have hne : ¬ (i.val = j.val) := by omega
  simp only [pathCartan, if_neg hne, if_pos h]


private lemma pathCartan_far {n : ℕ} {i j : Fin n} (h1 : ¬ (i.val = j.val))
    (h2 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) : pathCartan n i j = 0 := by
  simp only [pathCartan, if_neg h1, if_neg h2]


private lemma cartan_A_eq_pathCartan (n : ℕ) (hn : 1 ≤ n) :
    cartanMatrix (FiniteIntegerMatrixModels.FiniteMatrixModel.A n hn) = pathCartan n := by
  ext i j
  simp only [cartanMatrix, pathCartan, FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Matrix.sub_apply, two_nsmul,
    Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega



private lemma pathCartan_submatrix_succ (m : ℕ) :
    (pathCartan (m + 1)).submatrix Fin.succ Fin.succ = pathCartan m := by
  ext i j
  simp only [pathCartan, Matrix.submatrix_apply, Fin.val_succ]
  split_ifs <;> omega




private lemma det_pathCartan_minor_one (n : ℕ) :
    ((pathCartan (n + 2)).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove).det
      = -(pathCartan n).det := by
  have hz : ∀ i : Fin n,
      ((pathCartan (n + 2)).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove)
        (Fin.succ i) 0 = 0 := by
    intro i
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact pathCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : ((pathCartan (n + 2)).submatrix Fin.succ (Fin.succ (0 : Fin (n + 1))).succAbove)
      0 0 = -1 := by
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact pathCartan_offdiag (Or.inr (by simp only [Fin.val_succ, Fin.val_zero]))
  have hsub : ((pathCartan (n + 2)).submatrix Fin.succ
      (Fin.succ (0 : Fin (n + 1))).succAbove).submatrix Fin.succ Fin.succ = pathCartan n := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succ_succAbove_succ, Fin.zero_succAbove, pathCartan,
      Fin.val_succ]
    split_ifs <;> omega
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hsub]
  ring



private lemma det_pathCartan_rec (n : ℕ) :
    (pathCartan (n + 2)).det = 2 * (pathCartan (n + 1)).det - (pathCartan n).det := by
  have hz : ∀ j : Fin n, pathCartan (n + 2) 0 (Fin.succ (Fin.succ j)) = 0 := fun j =>
    pathCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : pathCartan (n + 2) 0 0 = 2 := pathCartan_diag rfl
  have e1 : pathCartan (n + 2) 0 (Fin.succ 0) = -1 :=
    pathCartan_offdiag (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]))
  have hs0 : (pathCartan (n + 2)).submatrix Fin.succ (0 : Fin (n + 2)).succAbove
      = pathCartan (n + 1) := by
    rw [Fin.succAbove_zero]; exact pathCartan_submatrix_succ (n + 1)
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0, e1, hs0,
    det_pathCartan_minor_one, Fin.val_zero, Fin.val_succ, zero_add, pow_zero, one_mul]
  ring



private lemma det_pathCartan : ∀ n : ℕ, (pathCartan n).det = (n : ℤ) + 1
  | 0 => by simp
  | 1 => by rw [Matrix.det_fin_one]; norm_num [pathCartan]
  | (n + 2) => by
      rw [det_pathCartan_rec, det_pathCartan (n + 1), det_pathCartan n]
      push_cast; ring


/-- The Cartan determinant of type A of rank n is n + 1. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem det_cartanMatrix_typeA (n : ℕ) (hn : 1 ≤ n) :
    (cartanMatrix (FiniteIntegerMatrixModels.FiniteMatrixModel.A n hn)).det = (n : ℤ) + 1 := by
  rw [cartan_A_eq_pathCartan n hn, det_pathCartan n]











private def dCartan (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val = j.val then 2
    else if (i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨ (j.val + 1 = i.val ∧ i.val ≤ n - 2) ∨
            (i.val = n - 3 ∧ j.val = n - 1) ∨ (j.val = n - 3 ∧ i.val = n - 1) then -1
    else 0


private lemma dCartan_diag {n : ℕ} {i j : Fin n} (h : i.val = j.val) :
    dCartan n i j = 2 := by simp only [dCartan, if_pos h]


private lemma dCartan_offdiag {n : ℕ} {i j : Fin n} (hne : i.val ≠ j.val)
    (h : (i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨ (j.val + 1 = i.val ∧ i.val ≤ n - 2) ∨
         (i.val = n - 3 ∧ j.val = n - 1) ∨ (j.val = n - 3 ∧ i.val = n - 1)) :
    dCartan n i j = -1 := by simp only [dCartan, if_neg hne, if_pos h]


private lemma dCartan_far {n : ℕ} {i j : Fin n} (hne : i.val ≠ j.val)
    (h : ¬ ((i.val + 1 = j.val ∧ j.val ≤ n - 2) ∨ (j.val + 1 = i.val ∧ i.val ≤ n - 2) ∨
         (i.val = n - 3 ∧ j.val = n - 1) ∨ (j.val = n - 3 ∧ i.val = n - 1))) :
    dCartan n i j = 0 := by simp only [dCartan, if_neg hne, if_neg h]


private lemma cartan_D_eq_dCartan (n : ℕ) (hn : 4 ≤ n) :
    cartanMatrix (FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn) = dCartan n := by
  ext i j
  simp only [cartanMatrix, dCartan, FiniteIntegerMatrixModels.FiniteMatrixModel.matrix, Matrix.sub_apply, two_nsmul,
    Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega


private lemma det_dCartan_four : (dCartan 4).det = 4 := by
  have hC : dCartan 4 = !![2,-1,0,0; -1,2,-1,-1; 0,-1,2,0; 0,-1,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det


private lemma det_dCartan_five : (dCartan 5).det = 4 := by
  have hC : dCartan 5 = !![2,-1,0,0,0; -1,2,-1,0,0; 0,-1,2,-1,-1; 0,0,-1,2,0; 0,0,-1,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det



private lemma dCartan_submatrix_succ (m : ℕ) :
    (dCartan (m + 5)).submatrix Fin.succ Fin.succ = dCartan (m + 4) := by
  ext i j
  simp only [dCartan, Matrix.submatrix_apply, Fin.val_succ]
  split_ifs <;> omega



private lemma det_dCartan_minor_one (m : ℕ) :
    ((dCartan (m + 6)).submatrix Fin.succ (Fin.succ (0 : Fin (m + 5))).succAbove).det
      = -(dCartan (m + 4)).det := by
  have hz : ∀ i : Fin (m + 4),
      ((dCartan (m + 6)).submatrix Fin.succ (Fin.succ (0 : Fin (m + 5))).succAbove)
        (Fin.succ i) 0 = 0 := by
    intro i
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact dCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : ((dCartan (m + 6)).submatrix Fin.succ (Fin.succ (0 : Fin (m + 5))).succAbove)
      0 0 = -1 := by
    rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero]
    exact dCartan_offdiag (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (Or.inr (Or.inl ⟨by simp only [Fin.val_succ, Fin.val_zero],
        by simp only [Fin.val_succ, Fin.val_zero]; omega⟩))
  have hsub : ((dCartan (m + 6)).submatrix Fin.succ
      (Fin.succ (0 : Fin (m + 5))).succAbove).submatrix Fin.succ Fin.succ = dCartan (m + 4) := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succ_succAbove_succ, Fin.zero_succAbove, dCartan,
      Fin.val_succ]
    split_ifs <;> omega
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hsub]
  ring


private lemma det_dCartan_rec (m : ℕ) :
    (dCartan (m + 6)).det = 2 * (dCartan (m + 5)).det - (dCartan (m + 4)).det := by
  have hz : ∀ j : Fin (m + 4), dCartan (m + 6) 0 (Fin.succ (Fin.succ j)) = 0 := fun j =>
    dCartan_far (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (by simp only [Fin.val_succ, Fin.val_zero]; omega)
  have e0 : dCartan (m + 6) 0 0 = 2 := dCartan_diag rfl
  have e1 : dCartan (m + 6) 0 (Fin.succ 0) = -1 :=
    dCartan_offdiag (by simp only [Fin.val_succ, Fin.val_zero]; omega)
      (Or.inl ⟨by simp only [Fin.val_succ, Fin.val_zero],
        by simp only [Fin.val_succ, Fin.val_zero]; omega⟩)
  have hs0 : (dCartan (m + 6)).submatrix Fin.succ (0 : Fin (m + 6)).succAbove
      = dCartan (m + 5) := by
    rw [Fin.succAbove_zero]; exact dCartan_submatrix_succ (m + 1)
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, e0, e1, hs0,
    det_dCartan_minor_one, Fin.val_zero, Fin.val_succ, zero_add, pow_zero, one_mul]
  ring


private lemma det_dCartan : ∀ m : ℕ, (dCartan (m + 4)).det = 4
  | 0 => det_dCartan_four
  | 1 => det_dCartan_five
  | (m + 2) => by
      have h1 : (dCartan (m + 5)).det = 4 := det_dCartan (m + 1)
      have h2 : (dCartan (m + 4)).det = 4 := det_dCartan m
      have hrec : (dCartan (m + 2 + 4)).det
          = 2 * (dCartan (m + 5)).det - (dCartan (m + 4)).det := det_dCartan_rec m
      rw [hrec, h1, h2]; ring


/-- The Cartan determinant of type D is four. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem det_cartanMatrix_typeD (n : ℕ) (hn : 4 ≤ n) :
    (cartanMatrix (FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn)).det = 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [cartan_D_eq_dCartan (m + 4) hn, det_dCartan m]





/-- Every type A adjacency matrix satisfies the finite simply laced Dynkin condition. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem typeA_isFiniteSimplyLaced (n : ℕ) (hn : 1 ≤ n) :
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix (FiniteIntegerMatrixModels.FiniteMatrixModel.A n hn).rank (FiniteIntegerMatrixModels.FiniteMatrixModel.A n hn).matrix :=
  FiniteIntegerMatrixModels.matrix_satisfies_condition (.A n hn)




/-- Every type D adjacency matrix satisfies the finite simply laced Dynkin condition. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem typeD_isFiniteSimplyLaced (n : ℕ) (hn : 4 ≤ n) :
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix (FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).rank (FiniteIntegerMatrixModels.FiniteMatrixModel.D n hn).matrix :=
  FiniteIntegerMatrixModels.matrix_satisfies_condition (.D n hn)




/-- The Cartan determinant of type E6 is three. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem det_cartanMatrix_typeE6 : (cartanMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E6).det = 3 := by
  have hC : cartanMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E6 =
      !![2,-1,0,0,0,0; -1,2,-1,0,0,0; 0,-1,2,-1,0,-1;
         0,0,-1,2,-1,0; 0,0,0,-1,2,0; 0,0,-1,0,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det


/-- The Cartan determinant of type E7 is two. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem det_cartanMatrix_typeE7 : (cartanMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E7).det = 2 := by
  have hC : cartanMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E7 =
      !![2,-1,0,0,0,0,0; -1,2,-1,0,0,0,0; 0,-1,2,-1,0,0,-1;
         0,0,-1,2,-1,0,0; 0,0,0,-1,2,-1,0; 0,0,0,0,-1,2,0;
         0,0,-1,0,0,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det


/-- The Cartan determinant of type E8 is one. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem det_cartanMatrix_typeE8 : (cartanMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E8).det = 1 := by
  have hC : cartanMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E8 =
      !![2,-1,0,0,0,0,0,0; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,-1;
         0,0,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
         0,0,0,0,0,-1,2,0; 0,0,-1,0,0,0,0,2] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  rw [hC]; cartan_det


/-- The adjacency matrices of types E6, E7, and E8 satisfy the finite simply laced Dynkin condition. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem exceptionalTypes_areFiniteSimplyLaced :
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E6.rank FiniteIntegerMatrixModels.FiniteMatrixModel.E6.matrix ∧
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E7.rank FiniteIntegerMatrixModels.FiniteMatrixModel.E7.matrix ∧
    AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix FiniteIntegerMatrixModels.FiniteMatrixModel.E8.rank FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix :=
  ⟨FiniteIntegerMatrixModels.matrix_satisfies_condition .E6, FiniteIntegerMatrixModels.matrix_satisfies_condition .E7, FiniteIntegerMatrixModels.matrix_satisfies_condition .E8⟩





/-- The integer adjacency matrix of the cycle on the given number of vertices. -/
def cycleAdjacencyMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then 1 else 0




/-- For a cycle with at least three vertices, the all-ones vector lies in the kernel of twice the identity minus the adjacency matrix. -/
theorem two_smul_one_sub_cycleAdjacencyMatrix_mulVec_one_eq_zero (n : ℕ) (hn : 3 ≤ n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - cycleAdjacencyMatrix n).mulVec (fun _ => 1) = 0 := by
  have hn0 : 0 < n := by omega
  funext i
  
  
  have hdeg : ∑ j : Fin n, cycleAdjacencyMatrix n i j = (2 : ℤ) := by
    
    
    have hmod : ∀ m : ℕ, m < n → (m + 1) % n = if m + 1 = n then 0 else m + 1 := by
      intro m hm
      by_cases h : m + 1 = n
      · rw [if_pos h, h]; exact Nat.mod_self n
      · rw [if_neg h]; exact Nat.mod_eq_of_lt (by omega)
    have hlt1 : (i.val + 1) % n < n := Nat.mod_lt _ hn0
    have hlt2 : (if i.val = 0 then n - 1 else i.val - 1) < n := by split <;> omega
    have hfil : (Finset.univ.filter
          (fun j : Fin n => (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val))
        = {(⟨(i.val + 1) % n, hlt1⟩ : Fin n),
            ⟨if i.val = 0 then n - 1 else i.val - 1, hlt2⟩} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      rw [hmod i.val i.isLt, hmod j.val j.isLt]
      split_ifs <;> omega
    have hab : (⟨(i.val + 1) % n, hlt1⟩ : Fin n)
        ≠ ⟨if i.val = 0 then n - 1 else i.val - 1, hlt2⟩ := by
      simp only [ne_eq, Fin.mk.injEq]
      rw [hmod i.val i.isLt]
      split_ifs <;> omega
    have hsum : ∑ j : Fin n, cycleAdjacencyMatrix n i j
        = ∑ j : Fin n,
            if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then (1 : ℤ) else 0 := by
      simp only [cycleAdjacencyMatrix]
    rw [hsum, Finset.sum_boole, hfil, Finset.card_pair hab]
    norm_num
  
  have h1 : ∑ j : Fin n, (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = (2 : ℤ) := by
    simp [Matrix.smul_apply, Matrix.one_apply, Finset.sum_ite_eq]
  simp only [Matrix.mulVec, dotProduct, mul_one, Matrix.sub_apply, Pi.zero_apply]
  rw [Finset.sum_sub_distrib, h1, hdeg]
  norm_num



/-- For a cycle with at least three vertices, twice the identity minus its adjacency matrix has zero determinant. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem det_two_smul_one_sub_cycleAdjacencyMatrix_eq_zero (n : ℕ) (hn : 3 ≤ n) :
    (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - cycleAdjacencyMatrix n).det = 0 := by
  have hn0 : 0 < n := by omega
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun _ => 1, ?_, two_smul_one_sub_cycleAdjacencyMatrix_mulVec_one_eq_zero n hn⟩
  intro h
  have := congrFun h ⟨0, hn0⟩
  simp at this





















/-- The entries of a nonempty finite simply laced Dynkin adjacency matrix sum to twice its rank minus two. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem sum_adjacency_entries_eq_twice_rank_sub_two_of_isFiniteSimplyLaced {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hn : 1 ≤ n) (hD : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    (∑ i, ∑ j, adj i j) = 2 * ((n : ℤ) - 1) := by
  classical
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h; exact h
  
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      symm := ⟨fun i j h => by rw [hsymm' j i]; exact h⟩
      loopless := ⟨fun i h => by rw [hdiag i] at h; exact absurd h (by norm_num)⟩ }
  have hGadj : ∀ a b, adj a b = 1 → G.Adj a b := fun _ _ h => h
  haveI hNe : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  
  have hpre : G.Preconnected := by
    intro i j
    obtain ⟨p, hhead, hlast, hpath⟩ := hconn i j
    have hne : p ≠ [] := by rintro rfl; simp at hhead
    have hchain : List.IsChain (fun a b => adj a b = 1) p := by
      rw [List.isChain_iff_getElem]; intro k hk; exact hpath k hk
    have hi : p.head hne = i :=
      Option.some_inj.mp ((List.head?_eq_some_head hne).symm.trans hhead)
    have hj : p.getLast hne = j := by
      have := (List.getLast?_eq_getLast_of_ne_nil hne).symm.trans hlast
      exact Option.some_inj.mp this
    have hrtg := List.relationReflTransGen_of_exists_isChain p hchain hne
    rw [hi, hj] at hrtg
    exact (SimpleGraph.reachable_iff_reflTransGen i j).mpr
      (Relation.ReflTransGen.mono (fun a b h => hGadj a b h) i j hrtg)
  have hconn' : G.Connected := ⟨hpre⟩
  
  have hcount : (∑ i, ∑ j, adj i j) = 2 * (#G.edgeFinset : ℤ) := by
    have hterm : ∀ p : Fin n × Fin n,
        adj p.1 p.2 = (if adj p.1 p.2 = 1 then (1 : ℤ) else 0) := by
      intro p; rcases h01 p.1 p.2 with h | h <;> simp [h]
    calc (∑ i, ∑ j, adj i j)
        = ∑ p : Fin n × Fin n, adj p.1 p.2 := (Fintype.sum_prod_type' adj).symm
      _ = ∑ p : Fin n × Fin n, (if adj p.1 p.2 = 1 then (1 : ℤ) else 0) :=
            Finset.sum_congr rfl (fun p _ => hterm p)
      _ = ((univ.filter fun p : Fin n × Fin n => adj p.1 p.2 = 1).card : ℤ) := by
            rw [Finset.sum_boole]
      _ = ((2 * #G.edgeFinset : ℕ) : ℤ) := by rw [G.two_mul_card_edgeFinset]
      _ = 2 * (#G.edgeFinset : ℤ) := by push_cast; ring
  
  have hlb : n ≤ #G.edgeFinset + 1 := by
    have h := hconn'.card_vert_le_card_edgeSet_add_one
    rwa [Nat.card_fin, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h
  
  have hub : (∑ i, ∑ j, adj i j) < 2 * (n : ℤ) := by
    have hxne : (fun _ : Fin n => (1 : ℤ)) ≠ 0 := by
      intro h; have := congrFun h ⟨0, by omega⟩; simp at this
    have hp := hpos (fun _ => 1) hxne
    have hone : ∀ i j : Fin n,
        (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = if i = j then 2 else 0 := by
      intro i j; simp only [Matrix.smul_apply, Matrix.one_apply, two_nsmul]
      split_ifs <;> norm_num
    have hrow : ∀ i : Fin n,
        ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1)) i
          = 2 - ∑ j, adj i j := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, hone, mul_one,
        Finset.sum_sub_distrib]
      rw [Finset.sum_ite_eq univ i (fun _ => (2 : ℤ))]; simp
    have hval : dotProduct (fun _ : Fin n => (1 : ℤ))
        ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec (fun _ => 1))
        = 2 * (n : ℤ) - ∑ i, ∑ j, adj i j := by
      simp only [dotProduct, hrow, one_mul, Finset.sum_sub_distrib]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hval] at hp; linarith
  
  have hcard_ub : #G.edgeFinset < n := by
    have : 2 * (#G.edgeFinset : ℤ) < 2 * (n : ℤ) := by rw [← hcount]; exact hub
    exact_mod_cast (by linarith : (#G.edgeFinset : ℤ) < (n : ℤ))
  have hcard_eq : #G.edgeFinset = n - 1 := by omega
  rw [hcount, hcard_eq, Nat.cast_sub hn]; push_cast; ring












/-- Every vertex in a finite simply laced Dynkin diagram has degree at most three. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem vertexDegree_le_three_of_isFiniteSimplyLaced {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (v : Fin n) : vertexDegree adj v ≤ 3 := by
  by_contra hdeg
  push Not at hdeg
  simp only [vertexDegree] at hdeg
  obtain ⟨hsymm, hdiag, h01, _hconn, hpos⟩ := hD
  set N := univ.filter (fun j => adj v j = 1) with hN_def
  have hNcard : 4 ≤ N.card := hdeg
  obtain ⟨S, hSN, hScard⟩ := Finset.exists_subset_card_eq hNcard
  
  have hvnotN : v ∉ N := by
    rw [hN_def]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdiag v]; norm_num
  have hvnotS : v ∉ S := fun h => hvnotN (hSN h)
  have hSadjv : ∀ j ∈ S, adj v j = 1 := by
    intro j hj
    have hjN := hSN hj
    rw [hN_def, Finset.mem_filter] at hjN
    exact hjN.2
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a
    rw [Matrix.transpose_apply] at h
    exact h
  have hnn : ∀ a b, 0 ≤ adj a b := fun a b => by
    rcases h01 a b with h | h <;> rw [h] ; norm_num
  
  set x : Fin n → ℤ := fun j => 2 * (if j = v then 1 else 0) + (if j ∈ S then 1 else 0)
    with hx_def
  have hxv : x v = 2 := by simp [hx_def, hvnotS]
  have hxS : ∀ i ∈ S, x i = 1 := by
    intro i hi
    have hiv : i ≠ v := fun h => hvnotS (h ▸ hi)
    simp [hx_def, hiv, hi]
  set A := 2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj with hA_def
  have hone : ∀ i j : Fin n, (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = if i = j then 2 else 0 := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.one_apply, two_nsmul]
    split_ifs <;> norm_num
  
  have hrow : ∀ i, ∑ j, adj i j * x j = 2 * adj i v + ∑ j ∈ S, adj i j := by
    intro i
    have expand : ∀ j, adj i j * x j
        = 2 * (if j = v then adj i j else 0) + (if j ∈ S then adj i j else 0) := by
      intro j
      simp only [hx_def]
      rw [mul_add]
      congr 1
      · split_ifs <;> ring
      · split_ifs <;> ring
    simp only [expand, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.mul_sum, Finset.sum_ite_eq']; simp
    · rw [Finset.sum_ite_mem, Finset.univ_inter]
  
  have hAx : ∀ i, (A.mulVec x) i = 2 * x i - ∑ j, adj i j * x j := by
    intro i
    have hentry : ∀ j, A i j * x j = (if i = j then 2 else 0) * x j - adj i j * x j := by
      intro j; rw [hA_def, Matrix.sub_apply, hone, sub_mul]
    simp only [Matrix.mulVec, dotProduct, hentry, Finset.sum_sub_distrib]
    congr 1
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]; simp
  
  have hterm : ∀ i, x i * (A.mulVec x) i ≤ 0 := by
    intro i
    rw [hAx i, hrow i]
    by_cases hiv : i = v
    · subst hiv
      rw [hxv, hdiag i]
      have hsum : ∑ j ∈ S, adj i j = 4 := by
        rw [Finset.sum_congr rfl hSadjv]
        simp [Finset.sum_const, hScard]
      rw [hsum]; norm_num
    · by_cases hiS : i ∈ S
      · rw [hxS i hiS]
        have hiv1 : adj i v = 1 := by rw [hsymm' i v]; exact hSadjv i hiS
        rw [hiv1]
        have hnnsum : 0 ≤ ∑ j ∈ S, adj i j := Finset.sum_nonneg (fun j _ => hnn i j)
        nlinarith [hnnsum]
      · have hx0 : x i = 0 := by simp only [hx_def, if_neg hiv, if_neg hiS, mul_zero, add_zero]
        rw [hx0]; simp
  
  have hnonpos : dotProduct x (A.mulVec x) ≤ 0 := by
    simp only [dotProduct]
    exact Finset.sum_nonpos (fun i _ => hterm i)
  have hxne : x ≠ 0 := by
    intro h
    have hv0 : x v = 0 := by rw [h]; rfl
    rw [hxv] at hv0; norm_num at hv0
  have := hpos x hxne
  linarith




private lemma reachable_of_isChain {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ {l : List (Fin n)} (hne : l ≠ []), l.IsChain G.Adj →
      G.Reachable (l.head hne) (l.getLast hne)
  | [_], _, _ => by simp
  | (x :: y :: t), hne, h => by
      rw [List.isChain_cons_cons] at h
      have ih := reachable_of_isChain G (l := y :: t) (by simp) h.2
      have hgl : (x :: y :: t).getLast hne = (y :: t).getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hgl]
      exact h.1.reachable.trans ih



/-- A finite simply laced Dynkin diagram has at most one vertex of degree three. -/
@[source_ref "Chapter6/Problem6.1.3_continued_E7_E8" (role := supporting)]
theorem eq_of_vertexDegree_eq_three_of_isFiniteSimplyLaced {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hD : AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) (v w : Fin n)
    (hv : vertexDegree adj v = 3) (hw : vertexDegree adj w = 3) : v = w := by
  classical
  by_contra hvw
  obtain ⟨hsymm, hdiag, h01, hconn, hpos⟩ := hD
  have hsymm' : ∀ a b, adj a b = adj b a := fun a b => by
    have h := congrFun (congrFun hsymm b) a; rwa [Matrix.transpose_apply] at h
  have hnn : ∀ a b, 0 ≤ adj a b := fun a b => by
    rcases h01 a b with h | h <;> rw [h] ; norm_num
  
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => adj i j = 1
      symm := ⟨fun i j (h : adj i j = 1) => by rw [hsymm' j i]; exact h⟩
      loopless := ⟨fun i (h : adj i i = 1) => by change adj i i = 1 at h; linarith [hdiag i]⟩ }
  letI : DecidableRel G.Adj := fun i j => decEq (adj i j) 1
  have hGadj : ∀ {i j}, G.Adj i j ↔ adj i j = 1 := Iff.rfl
  
  have hreach : G.Reachable v w := by
    obtain ⟨l, hh, hl, hc⟩ := hconn v w
    have hne : l ≠ [] := by rintro rfl; simp at hh
    have hchain : l.IsChain G.Adj := by
      rw [List.isChain_iff_getElem]
      intro k hk; simpa [List.get_eq_getElem, hGadj] using hc k hk
    have hR := reachable_of_isChain G hne hchain
    have hhv : l.head hne = v := by
      have h1 := List.head?_eq_some_head hne; rw [hh] at h1; exact (Option.some_inj.mp h1).symm
    have hlw : l.getLast hne = w := by
      have h1 := List.getLast?_eq_some_getLast hne
      rw [hl] at h1; exact (Option.some_inj.mp h1).symm
    rwa [hhv, hlw] at hR
  
  obtain ⟨p, hpath, hlen⟩ := hreach.exists_path_of_dist
  set m := G.dist v w with hmdef
  have hm1 : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero]; intro h0
    exact hvw (hreach.dist_eq_zero_iff.mp h0)
  have hp0 : p.getVert 0 = v := p.getVert_zero
  have hpm : p.getVert m = w := by rw [← hlen]; exact p.getVert_length
  
  have hadjc : ∀ k, k < m → adj (p.getVert k) (p.getVert (k + 1)) = 1 := by
    intro k hk
    exact hGadj.mp (p.adj_getVert_succ (by rw [hlen]; exact hk))
  
  have hinj : ∀ i j, i ≤ m → j ≤ m → p.getVert i = p.getVert j → i = j := by
    intro i j hi hj he
    exact hpath.getVert_injOn (by simp only [Set.mem_setOf_eq, hlen]; exact hi)
      (by simp only [Set.mem_setOf_eq, hlen]; exact hj) he
  
  have hdistk : ∀ k, k ≤ m → G.dist v (p.getVert k) = k := by
    intro k hk
    have hle : G.dist v (p.getVert k) ≤ k :=
      calc G.dist v (p.getVert k) ≤ (p.take k).length := G.dist_le _
        _ = k ⊓ p.length := p.take_length k
        _ = k := by rw [hlen]; exact inf_eq_left.mpr hk
    have hdw : G.dist (p.getVert k) w ≤ m - k :=
      calc G.dist (p.getVert k) w ≤ (p.drop k).length := G.dist_le _
        _ = p.length - k := p.drop_length k
        _ = m - k := by rw [hlen]
    have htri := ((p.take k).reachable).dist_triangle_left w
    omega
  have hdistk2 : ∀ k, k ≤ m → G.dist (p.getVert k) w = m - k := by
    intro k hk
    have hdw : G.dist (p.getVert k) w ≤ m - k :=
      calc G.dist (p.getVert k) w ≤ (p.drop k).length := G.dist_le _
        _ = p.length - k := p.drop_length k
        _ = m - k := by rw [hlen]
    have hdk := hdistk k hk
    have htri := ((p.take k).reachable).dist_triangle_left w
    omega
  
  set p1 := p.getVert 1 with hp1def
  set pm1 := p.getVert (m - 1) with hpm1def
  have hp1v : adj v p1 = 1 := by have := hadjc 0 hm1; rwa [hp0] at this
  have hpm1w : adj w pm1 = 1 := by
    have := hadjc (m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega, hpm] at this
    rw [hsymm' w pm1]; exact this
  
  have hp1mem : p1 ∈ univ.filter (fun j => adj v j = 1) := by
    simp only [mem_filter, mem_univ, true_and]; exact hp1v
  have hpm1mem : pm1 ∈ univ.filter (fun j => adj w j = 1) := by
    simp only [mem_filter, mem_univ, true_and]; exact hpm1w
  have hcardV : ((univ.filter (fun j => adj v j = 1)).erase p1).card = 2 := by
    rw [Finset.card_erase_of_mem hp1mem]
    have : (univ.filter (fun j => adj v j = 1)).card = 3 := hv
    omega
  have hcardW : ((univ.filter (fun j => adj w j = 1)).erase pm1).card = 2 := by
    rw [Finset.card_erase_of_mem hpm1mem]
    have : (univ.filter (fun j => adj w j = 1)).card = 3 := hw
    omega
  obtain ⟨a, b, hab, hVset⟩ := Finset.card_eq_two.mp hcardV
  obtain ⟨c, d, hcd, hWset⟩ := Finset.card_eq_two.mp hcardW
  have haE : a ∈ (univ.filter (fun j => adj v j = 1)).erase p1 := by rw [hVset]; simp
  have hbE : b ∈ (univ.filter (fun j => adj v j = 1)).erase p1 := by rw [hVset]; simp
  have hcE : c ∈ (univ.filter (fun j => adj w j = 1)).erase pm1 := by rw [hWset]; simp
  have hdE : d ∈ (univ.filter (fun j => adj w j = 1)).erase pm1 := by rw [hWset]; simp
  have hap1 : a ≠ p1 := (Finset.mem_erase.mp haE).1
  have hbp1 : b ≠ p1 := (Finset.mem_erase.mp hbE).1
  have hcpm1 : c ≠ pm1 := (Finset.mem_erase.mp hcE).1
  have hdpm1 : d ≠ pm1 := (Finset.mem_erase.mp hdE).1
  have hav : adj v a = 1 := by
    have := (mem_filter.mp (Finset.mem_erase.mp haE).2).2; exact this
  have hbv : adj v b = 1 := by
    have := (mem_filter.mp (Finset.mem_erase.mp hbE).2).2; exact this
  have hcw : adj w c = 1 := by
    have := (mem_filter.mp (Finset.mem_erase.mp hcE).2).2; exact this
  have hdw' : adj w d = 1 := by
    have := (mem_filter.mp (Finset.mem_erase.mp hdE).2).2; exact this
  
  have hoff_v : ∀ e, adj v e = 1 → e ≠ p1 → ∀ k, k ≤ m → e ≠ p.getVert k := by
    intro e hve hep1 k hk hcontra
    have hd1 : G.dist v e = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr (hGadj.mpr hve)
    have hdk : G.dist v (p.getVert k) = k := hdistk k hk
    rw [hcontra, hdk] at hd1
    exact hep1 (by rw [hcontra, hd1])
  have hoff_w : ∀ e, adj w e = 1 → e ≠ pm1 → ∀ k, k ≤ m → e ≠ p.getVert k := by
    intro e hwe hepm1 k hk hcontra
    have hd1 : G.dist e w = 1 := by
      rw [SimpleGraph.dist_comm]; exact SimpleGraph.dist_eq_one_iff_adj.mpr (hGadj.mpr hwe)
    have hdk : G.dist (p.getVert k) w = m - k := hdistk2 k hk
    rw [hcontra, hdk] at hd1
    exact hepm1 (by rw [hcontra, show k = m - 1 by omega])
  
  have hoffmem : ∀ e, (∀ k, k ≤ m → e ≠ p.getVert k) → e ∉ p.support := by
    intro e he hmem
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
    obtain ⟨k, hk_eq, hk_le⟩ := hmem
    exact he k (by rw [hlen] at hk_le; exact hk_le) hk_eq.symm
  have ha_ns : a ∉ p.support := hoffmem a (hoff_v a hav hap1)
  have hb_ns : b ∉ p.support := hoffmem b (hoff_v b hbv hbp1)
  have hc_ns : c ∉ p.support := hoffmem c (hoff_w c hcw hcpm1)
  have hd_ns : d ∉ p.support := hoffmem d (hoff_w d hdw' hdpm1)
  
  set x : Fin n → ℤ :=
    fun i => (if i ∈ p.support then 2 else 0) +
      (if i = a ∨ i = b ∨ i = c ∨ i = d then 1 else 0) with hxdef
  have hxnn : ∀ i, 0 ≤ x i := by intro i; simp only [hxdef]; split_ifs <;> norm_num
  
  have hxpath : ∀ i, i ∈ p.support → x i = 2 := by
    intro i hi
    have hnotQ : ¬(i = a ∨ i = b ∨ i = c ∨ i = d) := by
      rintro (h | h | h | h)
      · exact ha_ns (h ▸ hi)
      · exact hb_ns (h ▸ hi)
      · exact hc_ns (h ▸ hi)
      · exact hd_ns (h ▸ hi)
    simp only [hxdef, if_pos hi, if_neg hnotQ, add_zero]
  have hxpend : ∀ e, e ∉ p.support → (e = a ∨ e = b ∨ e = c ∨ e = d) → x e = 1 := by
    intro e he hQ; simp only [hxdef, if_neg he, if_pos hQ, zero_add]
  have hxa : x a = 1 := hxpend a ha_ns (Or.inl rfl)
  have hxb : x b = 1 := hxpend b hb_ns (Or.inr (Or.inl rfl))
  have hxc : x c = 1 := hxpend c hc_ns (Or.inr (Or.inr (Or.inl rfl)))
  have hxd : x d = 1 := hxpend d hd_ns (Or.inr (Or.inr (Or.inr rfl)))
  have hxv : x v = 2 := by rw [← hp0]; exact hxpath _ (p.getVert_mem_support 0)
  have hxw : x w = 2 := by rw [← hpm]; exact hxpath _ (p.getVert_mem_support m)
  have hxp1 : x p1 = 2 := hxpath _ (p.getVert_mem_support 1)
  have hxpm1 : x pm1 = 2 := hxpath _ (p.getVert_mem_support (m - 1))
  
  
  have hSbound : ∀ (i : Fin n) (T : Finset (Fin n)), (∀ j ∈ T, adj i j = 1) →
      (∑ j ∈ T, x j) ≤ ∑ j, adj i j * x j := by
    intro i T hT
    calc ∑ j ∈ T, x j = ∑ j ∈ T, adj i j * x j :=
          Finset.sum_congr rfl (fun j hj => by rw [hT j hj, one_mul])
      _ ≤ ∑ j, adj i j * x j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun j _ _ => mul_nonneg (hnn i j) (hxnn j))
  
  have hkey : ∀ i, 2 * x i ≤ ∑ j, adj i j * x j := by
    intro i
    by_cases hiP : i ∈ p.support
    · rw [hxpath i hiP]
      obtain ⟨k, hk_eq, hk_le'⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hiP
      have hk_le : k ≤ m := by rw [hlen] at hk_le'; exact hk_le'
      by_cases hk0 : k = 0
      · 
        have hiv : i = v := by rw [hk0, hp0] at hk_eq; exact hk_eq.symm
        subst hiv
        have hp1_ns : p1 ∉ ({a, b} : Finset (Fin n)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h)
          · exact hap1 h.symm
          · exact hbp1 h.symm
        have hab_ns : a ∉ ({b} : Finset (Fin n)) := by simp [hab]
        have hT : ∀ j ∈ ({p1, a, b} : Finset (Fin n)), adj i j = 1 := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with h | h | h <;> subst h
          · exact hp1v
          · exact hav
          · exact hbv
        have hsum : ∑ j ∈ ({p1, a, b} : Finset (Fin n)), x j = 4 := by
          rw [Finset.sum_insert hp1_ns, Finset.sum_insert hab_ns, Finset.sum_singleton,
            hxp1, hxa, hxb]; norm_num
        have := hSbound i {p1, a, b} hT
        rw [hsum] at this; linarith
      · by_cases hkm : k = m
        · 
          have hiw : i = w := by rw [hkm, hpm] at hk_eq; exact hk_eq.symm
          subst hiw
          have hpm1_ns : pm1 ∉ ({c, d} : Finset (Fin n)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rintro (h | h)
            · exact hcpm1 h.symm
            · exact hdpm1 h.symm
          have hcd_ns : c ∉ ({d} : Finset (Fin n)) := by simp [hcd]
          have hT : ∀ j ∈ ({pm1, c, d} : Finset (Fin n)), adj i j = 1 := by
            intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with h | h | h <;> subst h
            · exact hpm1w
            · exact hcw
            · exact hdw'
          have hsum : ∑ j ∈ ({pm1, c, d} : Finset (Fin n)), x j = 4 := by
            rw [Finset.sum_insert hpm1_ns, Finset.sum_insert hcd_ns, Finset.sum_singleton,
              hxpm1, hxc, hxd]; norm_num
          have := hSbound i {pm1, c, d} hT
          rw [hsum] at this; linarith
        · 
          have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          have hkm' : k < m := lt_of_le_of_ne hk_le hkm
          set j1 := p.getVert (k - 1) with hj1def
          set j2 := p.getVert (k + 1) with hj2def
          have hadj1 : adj i j1 = 1 := by
            have h := hadjc (k - 1) (by omega)
            rw [show k - 1 + 1 = k by omega, hk_eq] at h
            rw [hsymm' i j1]; exact h
          have hadj2 : adj i j2 = 1 := by
            have h := hadjc k hkm'; rw [hk_eq] at h; exact h
          have hj12 : j1 ≠ j2 := by
            intro h; have := hinj (k - 1) (k + 1) (by omega) (by omega) h; omega
          have hxj1 : x j1 = 2 := hxpath _ (p.getVert_mem_support (k - 1))
          have hxj2 : x j2 = 2 := hxpath _ (p.getVert_mem_support (k + 1))
          have hj1_ns : j1 ∉ ({j2} : Finset (Fin n)) := by simp [hj12]
          have hT : ∀ j ∈ ({j1, j2} : Finset (Fin n)), adj i j = 1 := by
            intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with h | h <;> subst h
            · exact hadj1
            · exact hadj2
          have hsum : ∑ j ∈ ({j1, j2} : Finset (Fin n)), x j = 4 := by
            rw [Finset.sum_insert hj1_ns, Finset.sum_singleton, hxj1, hxj2]; norm_num
          have := hSbound i {j1, j2} hT
          rw [hsum] at this; linarith
    · by_cases hiQ : i = a ∨ i = b ∨ i = c ∨ i = d
      · have hxi1 : x i = 1 := by simp only [hxdef, if_neg hiP, if_pos hiQ, zero_add]
        rw [hxi1]
        rcases hiQ with h | h | h | h
        · have hiadj : adj i v = 1 := by rw [h, hsymm' a v]; exact hav
          have hT : ∀ j ∈ ({v} : Finset (Fin n)), adj i j = 1 := by
            intro j hj; rw [Finset.mem_singleton] at hj; rw [hj]; exact hiadj
          have := hSbound i {v} hT; rw [Finset.sum_singleton, hxv] at this; linarith
        · have hiadj : adj i v = 1 := by rw [h, hsymm' b v]; exact hbv
          have hT : ∀ j ∈ ({v} : Finset (Fin n)), adj i j = 1 := by
            intro j hj; rw [Finset.mem_singleton] at hj; rw [hj]; exact hiadj
          have := hSbound i {v} hT; rw [Finset.sum_singleton, hxv] at this; linarith
        · have hiadj : adj i w = 1 := by rw [h, hsymm' c w]; exact hcw
          have hT : ∀ j ∈ ({w} : Finset (Fin n)), adj i j = 1 := by
            intro j hj; rw [Finset.mem_singleton] at hj; rw [hj]; exact hiadj
          have := hSbound i {w} hT; rw [Finset.sum_singleton, hxw] at this; linarith
        · have hiadj : adj i w = 1 := by rw [h, hsymm' d w]; exact hdw'
          have hT : ∀ j ∈ ({w} : Finset (Fin n)), adj i j = 1 := by
            intro j hj; rw [Finset.mem_singleton] at hj; rw [hj]; exact hiadj
          have := hSbound i {w} hT; rw [Finset.sum_singleton, hxw] at this; linarith
      · have hxi0 : x i = 0 := by simp only [hxdef, if_neg hiP, if_neg hiQ, add_zero]
        rw [hxi0]
        have : (0 : ℤ) ≤ ∑ j, adj i j * x j :=
          Finset.sum_nonneg (fun j _ => mul_nonneg (hnn i j) (hxnn j))
        linarith
  
  set A := 2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj with hAdef
  have hone : ∀ i j : Fin n,
      (2 • (1 : Matrix (Fin n) (Fin n) ℤ)) i j = if i = j then 2 else 0 := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.one_apply, two_nsmul]
    split_ifs <;> norm_num
  have hAx : ∀ i, (A.mulVec x) i = 2 * x i - ∑ j, adj i j * x j := by
    intro i
    have hentry : ∀ j, A i j * x j = (if i = j then 2 else 0) * x j - adj i j * x j := by
      intro j; rw [hAdef, Matrix.sub_apply, hone, sub_mul]
    simp only [Matrix.mulVec, dotProduct, hentry, Finset.sum_sub_distrib]
    congr 1
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]; simp
  have hterm : ∀ i, x i * (A.mulVec x) i ≤ 0 := by
    intro i; rw [hAx i]; nlinarith [hkey i, hxnn i]
  have hnonpos : dotProduct x (A.mulVec x) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => hterm i)
  have hxne : x ≠ 0 := by
    intro h; have hv0 : x v = 0 := by rw [h]; rfl
    rw [hxv] at hv0; norm_num at hv0
  have := hpos x hxne
  linarith

end RepresentationTheory.DynkinDiagram.FiniteSimplyLaced

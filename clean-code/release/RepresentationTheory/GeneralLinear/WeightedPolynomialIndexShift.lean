/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.MvPolynomial.UniformIndexShift

set_option linter.style.longLine false

namespace RepresentationTheory.GeneralLinear.WeightedPolynomialIndexShift

open MvPolynomial

/-- Two auxiliary indexed objects are equal whenever their `parts` functions are equal. -/
theorem auxiliaryIndexedObject_ext_parts {N n : ℕ} {a b : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N n} (h : a.parts = b.parts) :
    a = b := by
  cases a; cases b; simp only [RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition.mk.injEq]; exact h

/-- Maps an auxiliary object indexed by `d - N` to one indexed by `d` when `N ≤ d`. -/
def auxiliaryIncreaseIndex {N d : ℕ} (hd : N ≤ d) (μ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N (d - N)) :
    RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N d where
  parts i := μ.parts i + 1
  parts_antitone i j hij := Nat.add_le_add_right (μ.parts_antitone hij) 1
  sum_parts := by
    have h : ∑ i : Fin N, (μ.parts i + 1) = (∑ i : Fin N, μ.parts i) + N := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    rw [h, μ.sum_parts]; omega

/-- Lowers the natural-number index by `N` for an auxiliary object whose parts never take the value zero. -/
def auxiliaryDecreaseIndex {N d : ℕ} (hd : N ≤ d) (ν : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N d)
    (hν : (0 : ℕ) ∉ Set.range ν.parts) : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N (d - N) where
  parts i := ν.parts i - 1
  parts_antitone i j hij := Nat.sub_le_sub_right (ν.parts_antitone hij) 1
  sum_parts := by
    have h1 : ∀ i, 1 ≤ ν.parts i := by
      intro i
      rcases Nat.eq_zero_or_pos (ν.parts i) with h | h
      · exact absurd (Set.mem_range.2 ⟨i, h⟩) hν
      · exact h
    have hsum : ∑ i : Fin N, ν.parts i = (∑ i : Fin N, (ν.parts i - 1)) + N := by
      have hsplit : ∑ i : Fin N, ν.parts i = ∑ i : Fin N, ((ν.parts i - 1) + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := h1 i; omega
      rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    rw [ν.sum_parts] at hsum; omega

/-- Evaluating every variable at one sends their finite product to one. -/
theorem evalOne_prod_variables (N : ℕ) :
    MvPolynomial.eval (fun _ => (1 : ℚ))
        (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) = 1 := by
  rw [map_prod]; simp

/-- The polynomial evaluations at one agree before and after applying the auxiliary index-increasing map. -/
theorem evalOne_auxiliaryIncreaseIndex {N d : ℕ} (hd : N ≤ d)
    (μ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N (d - N)) :
    MvPolynomial.eval (fun _ => (1 : ℚ)) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N (auxiliaryIncreaseIndex hd μ).parts)
      = MvPolynomial.eval (fun _ => (1 : ℚ)) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N μ.parts) := by
  have hs : RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N (auxiliaryIncreaseIndex hd μ).parts
      = (∏ i : Fin N, MvPolynomial.X i) * RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N μ.parts := by
    change RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N (fun i => μ.parts i + 1) = _
    rw [RepresentationTheory.MvPolynomial.UniformIndexShift.auxiliary_eq_prod_variables_mul]
  rw [hs, map_mul, evalOne_prod_variables, one_mul]

/-- Multiplying the weighted polynomial sum by the product of all variables gives the corresponding sum over indices whose parts avoid zero. -/
theorem weightedPolynomialSum_mul_prod_variables {N d : ℕ} (hd : N ≤ d) :
    (∑ μ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N (d - N),
        (MvPolynomial.eval (fun _ => (1 : ℚ)) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N μ.parts)) • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N μ.parts)
        * (∏ i : Fin N, MvPolynomial.X i)
      = ∑ ν ∈ Finset.univ.filter
            (fun ν : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N d => (0 : ℕ) ∉ Set.range ν.parts),
          (MvPolynomial.eval (fun _ => (1 : ℚ)) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.parts)) • RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N ν.parts := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_bij'
    (fun μ _ => auxiliaryIncreaseIndex hd μ)
    (fun ν hν => auxiliaryDecreaseIndex hd ν (Finset.mem_filter.1 hν).2)
    ?_ ?_ ?_ ?_ ?_
  · intro μ _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rintro ⟨i, hi⟩
    have : μ.parts i + 1 = 0 := hi
    omega
  · intro ν _; exact Finset.mem_univ _
  · intro μ _
    apply auxiliaryIndexedObject_ext_parts
    funext i
    change (μ.parts i + 1) - 1 = μ.parts i
    omega
  · intro ν hν
    apply auxiliaryIndexedObject_ext_parts
    funext i
    have hpos : 1 ≤ ν.parts i := by
      rcases Nat.eq_zero_or_pos (ν.parts i) with h | h
      · exact absurd (Set.mem_range.2 ⟨i, h⟩) (Finset.mem_filter.1 hν).2
      · exact h
    change (ν.parts i - 1) + 1 = ν.parts i
    omega
  · intro μ _
    rw [evalOne_auxiliaryIncreaseIndex hd μ]
    have hs : RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N (auxiliaryIncreaseIndex hd μ).parts
        = (∏ i : Fin N, MvPolynomial.X i) * RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N μ.parts := by
      change RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N (fun i => μ.parts i + 1) = _
      rw [RepresentationTheory.MvPolynomial.UniformIndexShift.auxiliary_eq_prod_variables_mul]
    rw [hs, smul_mul_assoc, mul_comm (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N μ.parts) (∏ i : Fin N, MvPolynomial.X i)]

end RepresentationTheory.GeneralLinear.WeightedPolynomialIndexShift

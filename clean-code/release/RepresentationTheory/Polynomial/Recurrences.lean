/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.Sl2Representations
import RepresentationTheory.Alignment.Attribute

open Polynomial Finset

namespace RepresentationTheory.Polynomial.Recurrences

/-- The integer polynomial indexed by a natural number used in the displayed recurrence. -/
noncomputable def geometricSeriesPolynomial (n : ℕ) : Polynomial ℤ := ∑ j ∈ range (n + 1), X ^ j

/-- Multiplication by `X - 1` converts the indexed polynomial into `X^(n + 1) - 1`. -/
theorem geometricSeriesPolynomial_mul_X_sub_one (n : ℕ) :
    geometricSeriesPolynomial n * (X - 1) = X ^ (n + 1) - 1 := by
  rw [geometricSeriesPolynomial]; exact geom_sum_mul X (n + 1)

/-- The polynomial `X - 1` is nonzero. -/
theorem X_sub_one_ne_zero : (X - 1 : Polynomial ℤ) ≠ 0 := by
  rw [← C_1]; exact (monic_X_sub_C 1).ne_zero

/-- Multiplying the displayed polynomial sum by `X - 1` gives the stated product. -/
theorem indexPolynomialSum_mul_X_sub_one (lam mu : ℕ) :
    (∑ k ∈ range (min lam mu + 1), X ^ k * geometricSeriesPolynomial (lam + mu - 2 * k)) * (X - 1)
      = geometricSeriesPolynomial (min lam mu) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
  set m := min lam mu with hm
  rw [Finset.sum_mul]
  have hterm : ∀ k ∈ range (m + 1),
      X ^ k * geometricSeriesPolynomial (lam + mu - 2 * k) * (X - 1)
        = X ^ (lam + mu + 1 - k) - X ^ k := by
    intro k hk
    rw [mem_range] at hk
    have h2k : 2 * k ≤ lam + mu := by omega
    rw [mul_assoc, geometricSeriesPolynomial_mul_X_sub_one, mul_sub, mul_one, ← pow_add,
      show k + (lam + mu - 2 * k + 1) = lam + mu + 1 - k from by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have hreidx : ∑ k ∈ range (m + 1), X ^ (lam + mu + 1 - k)
      = X ^ (lam + mu + 1 - m) * geometricSeriesPolynomial m := by
    rw [geometricSeriesPolynomial, Finset.mul_sum, ← Finset.sum_range_reflect
      (fun k => X ^ (lam + mu + 1 - k)) (m + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    rw [← pow_add, show lam + mu + 1 - (m + 1 - 1 - i) = lam + mu + 1 - m + i from by omega]
  rw [hreidx, ← geometricSeriesPolynomial]
  ring

/-- Expands a product of two indexed polynomials as the displayed finite polynomial sum. -/
@[source_ref "Chapter2/Problem2.15.1/Derived14" (role := supporting), source_ref "Chapter2/Problem2.15.1" (role := supporting)]
theorem mul_geometricSeriesPolynomial (lam mu : ℕ) :
    geometricSeriesPolynomial lam * geometricSeriesPolynomial mu
      = ∑ k ∈ range (min lam mu + 1), X ^ k * geometricSeriesPolynomial (lam + mu - 2 * k) := by
  have key : geometricSeriesPolynomial lam * geometricSeriesPolynomial mu * ((X - 1) * (X - 1))
      = (∑ k ∈ range (min lam mu + 1), X ^ k * geometricSeriesPolynomial (lam + mu - 2 * k))
          * ((X - 1) * (X - 1)) := by
    have hL : geometricSeriesPolynomial lam * geometricSeriesPolynomial mu * ((X - 1) * (X - 1))
        = (X ^ (lam + 1) - 1) * (X ^ (mu + 1) - 1) := by
      calc geometricSeriesPolynomial lam * geometricSeriesPolynomial mu * ((X - 1) * (X - 1))
          = (geometricSeriesPolynomial lam * (X - 1)) * (geometricSeriesPolynomial mu * (X - 1)) := by ring
        _ = (X ^ (lam + 1) - 1) * (X ^ (mu + 1) - 1) := by
            rw [geometricSeriesPolynomial_mul_X_sub_one, geometricSeriesPolynomial_mul_X_sub_one]
    have hR : (∑ k ∈ range (min lam mu + 1), X ^ k * geometricSeriesPolynomial (lam + mu - 2 * k))
          * ((X - 1) * (X - 1))
        = (X ^ (min lam mu + 1) - 1) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
      rw [← mul_assoc, indexPolynomialSum_mul_X_sub_one]
      calc geometricSeriesPolynomial (min lam mu) * (X ^ (lam + mu + 1 - min lam mu) - 1) * (X - 1)
          = (geometricSeriesPolynomial (min lam mu) * (X - 1)) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
            ring
        _ = (X ^ (min lam mu + 1) - 1) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
            rw [geometricSeriesPolynomial_mul_X_sub_one]
    rw [hL, hR]
    rcases le_total lam mu with h | h
    · rw [min_eq_left h, show lam + mu + 1 - lam = mu + 1 from by omega]
    · rw [min_eq_right h, show lam + mu + 1 - mu = lam + 1 from by omega, mul_comm]
  exact mul_right_cancel₀ (mul_ne_zero X_sub_one_ne_zero X_sub_one_ne_zero) key

/-- Evaluating the indexed polynomial at one gives the successor of its index. -/
theorem eval_geometricSeriesPolynomial_one (n : ℕ) : (geometricSeriesPolynomial n).eval 1 = (n : ℤ) + 1 := by
  rw [geometricSeriesPolynomial, eval_finsetSum]
  simp [Finset.sum_const, Finset.card_range]

/-- Expresses a product of two successors as the stated finite sum of successors. -/
theorem succ_mul_succ_eq_indexSum (lam mu : ℕ) :
    ((lam : ℤ) + 1) * ((mu : ℤ) + 1)
      = ∑ k ∈ range (min lam mu + 1), (((lam + mu - 2 * k : ℕ) : ℤ) + 1) := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (mul_geometricSeriesPolynomial lam mu)
  rw [eval_mul, eval_geometricSeriesPolynomial_one, eval_geometricSeriesPolynomial_one, eval_finsetSum] at h
  simp only [eval_mul, eval_pow, eval_X, one_pow, eval_geometricSeriesPolynomial_one, one_mul] at h
  exact h

end RepresentationTheory.Polynomial.Recurrences

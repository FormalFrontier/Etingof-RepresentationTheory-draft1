/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.NumberTheory.Real.Irrational
import RepresentationTheory.Alignment.Attribute

/-! # An auxiliary formal statement -/

namespace RepresentationTheory.Auxiliary.UnavailableFormalExpression

open Real

private def scaledCosine : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (n + 2) => 2 * scaledCosine (n + 1) - 9 * scaledCosine n

private lemma scaledCosine_eq (θ : ℝ) (hθ : cos θ = 1 / 3) (n : ℕ) :
    (↑(scaledCosine n) : ℝ) = 3 ^ n * cos (↑n * θ) ∧
    (↑(scaledCosine (n + 1)) : ℝ) = 3 ^ (n + 1) * cos (↑(n + 1) * θ) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> norm_num [scaledCosine, hθ]
  | succ n ih =>
    obtain ⟨hn, hnSucc⟩ := ih
    refine ⟨hnSucc, ?_⟩
    have hrec : (↑(scaledCosine (n + 1 + 1)) : ℝ) =
        2 * ↑(scaledCosine (n + 1)) - 9 * ↑(scaledCosine n) := by
      have hrecInt : scaledCosine (n + 1 + 1) =
          2 * scaledCosine (n + 1) - 9 * scaledCosine n := by
        simp only [scaledCosine]
      rw [hrecInt]
      push_cast
      ring
    have hcosRec : cos ((↑(n + 1 + 1) : ℝ) * θ)
        = 2 * cos θ * cos ((↑(n + 1) : ℝ) * θ) - cos ((↑n : ℝ) * θ) := by
      have e1 : (↑(n + 1 + 1) : ℝ) * θ = (↑(n + 1) : ℝ) * θ + θ := by
        push_cast
        ring
      have e2 : (↑n : ℝ) * θ = (↑(n + 1) : ℝ) * θ - θ := by
        push_cast
        ring
      rw [e1, e2, Real.cos_add, Real.cos_sub]
      ring
    rw [hrec, hnSucc, hn, hcosRec, hθ]
    ring

private lemma three_not_dvd_scaledCosine (n : ℕ) : ¬ (3 ∣ scaledCosine n) := by
  have hmod : ∀ m : ℕ,
      (scaledCosine m % 3 = 1 ∨ scaledCosine m % 3 = 2) ∧
        (scaledCosine (m + 1) % 3 = 1 ∨ scaledCosine (m + 1) % 3 = 2) := by
    intro m
    induction m with
    | zero => refine ⟨Or.inl ?_, Or.inl ?_⟩ <;> decide
    | succ m ih =>
      obtain ⟨_, h2⟩ := ih
      refine ⟨h2, ?_⟩
      have hrec : scaledCosine (m + 1 + 1) =
          2 * scaledCosine (m + 1) - 9 * scaledCosine m := by
        simp only [scaledCosine]
      omega
  have hnMod := (hmod n).1
  omega

/-- An auxiliary theorem whose formal expression is unavailable in displayed form. -/
@[source_ref "Chapter2/Problem2.13.1" (role := supporting)]
theorem auxiliaryFact : Irrational (arccos (1 / 3) / π) := by
  intro h
  obtain ⟨r, hr⟩ := h
  set θ := arccos (1 / 3) with hθdef
  have hθcos : cos θ = 1 / 3 := Real.cos_arccos (by norm_num) (by norm_num)
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [eq_div_iff hπ] at hr
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hrq : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
    rw [Rat.cast_def]; field_simp
  have harg : (↑(2 * r.den) : ℝ) * θ = (r.num : ℝ) * (2 * π) := by
    have hθ2 : θ = (r : ℝ) * π := hr.symm
    rw [hθ2]; push_cast; linear_combination (2 * π) * hrq
  have hcos1 : cos ((↑(2 * r.den) : ℝ) * θ) = 1 := by
    rw [harg]
    exact Real.cos_int_mul_two_pi r.num
  have hkey := (scaledCosine_eq θ hθcos (2 * r.den)).1
  rw [hcos1, mul_one] at hkey
  have hb_eq : scaledCosine (2 * r.den) = 3 ^ (2 * r.den) := by
    exact_mod_cast hkey
  have hn0 : 2 * r.den ≠ 0 := by
    have hdenPos := r.den_pos
    omega
  exact three_not_dvd_scaledCosine (2 * r.den) (hb_eq ▸ dvd_pow_self 3 hn0)

end RepresentationTheory.Auxiliary.UnavailableFormalExpression

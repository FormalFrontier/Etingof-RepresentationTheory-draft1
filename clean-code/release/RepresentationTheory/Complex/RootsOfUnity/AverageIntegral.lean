/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Complex.RootsOfUnity.AverageIntegral

open Finset Complex in
private lemma roots_of_unity_avg_norm_bound
    (n : ℕ) (hn : 0 < n)
    (ε : Fin n → ℂ)
    (hε : ∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1)
    (hint : IsIntegral ℤ ((∑ i, ε i) / n))
    (hsum : (∑ i, ε i) ≠ 0)
    (hlt : ‖(∑ i, ε i) / (n : ℂ)‖ < 1) :
    False := by
  set L := IntermediateField.adjoin ℚ (Set.range ε) with hL_def
  have hε_int : ∀ i, IsIntegral ℤ (ε i) := by
    intro i
    obtain ⟨m, hm, hpow⟩ := hε i
    exact ⟨Polynomial.X ^ m - 1,
      Polynomial.monic_X_pow_sub_C 1 (Nat.pos_iff_ne_zero.mp hm),
      by simp [hpow]⟩
  have hε_intQ : ∀ x ∈ Set.range ε, IsIntegral ℚ x := by
    intro x ⟨i, hi⟩; rw [← hi]; exact (hε_int i).tower_top
  haveI hL_fd : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin hε_intQ
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : NumberField L := ⟨⟩
  have hε_mem : ∀ i, ε i ∈ L :=
    fun i => IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)
  set ε' : Fin n → L := fun i => ⟨ε i, hε_mem i⟩ with hε'_def
  have hα_mem : (∑ i, ε i) / (n : ℂ) ∈ L :=
    L.div_mem (L.sum_mem (fun i _ => hε_mem i)) (L.natCast_mem n)
  set α : L := ⟨(∑ i, ε i) / (n : ℂ), hα_mem⟩ with hα_def
  have hα_ne : α ≠ 0 := by
    intro h
    apply hsum
    have h0 : (α : ℂ) = 0 := congr_arg Subtype.val h
    change (∑ i, ε i) / (n : ℂ) = 0 at h0
    have hnn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    rwa [div_eq_zero_iff, or_iff_left hnn'] at h0
  have hσε_norm : ∀ (σ : L →ₐ[ℚ] ℂ) (i : Fin n), ‖σ (ε' i)‖ = 1 := by
    intro σ i
    obtain ⟨m, hm, hpow⟩ := hε i
    apply Complex.norm_eq_one_of_pow_eq_one _ (Nat.pos_iff_ne_zero.mp hm)
    calc (σ (ε' i)) ^ m = σ ((ε' i) ^ m) := (map_pow σ _ m).symm
      _ = σ ⟨1, L.one_mem⟩ := by
          congr 1; ext; simp [hε'_def, hpow]
      _ = 1 := map_one σ
  have hσ_bound : ∀ (σ : L →ₐ[ℚ] ℂ), ‖σ α‖ ≤ 1 := by
    intro σ
    have hnn : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
    have hσα : σ α = (∑ i, σ (ε' i)) / (n : ℂ) := by
      have key : α = (∑ i, ε' i) / (n : L) := by
        apply_fun (algebraMap L ℂ) using (algebraMap L ℂ).injective
        simp only [map_div₀, map_sum, map_natCast]
        rfl
      rw [key, map_div₀, map_sum, map_natCast]
    rw [hσα, norm_div, Complex.norm_natCast, div_le_one hnn]
    calc ‖∑ i, σ (ε' i)‖ ≤ ∑ i, ‖σ (ε' i)‖ := norm_sum_le _ _
      _ = ∑ _i : Fin n, (1 : ℝ) := by congr 1; ext i; exact hσε_norm σ i
      _ = n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  set ι₀ : L →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ L ℂ with hι₀_def
  have hι_val : ι₀ α = (α : ℂ) := rfl
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ (α : L)
  have hprod_lt : ∏ σ : L →ₐ[ℚ] ℂ, ‖σ α‖ < 1 := by
    have hσ_pos : ∀ σ : L →ₐ[ℚ] ℂ, 0 < ‖σ α‖ := by
      intro σ; rw [norm_pos_iff, ne_eq, ← map_zero σ]; exact σ.injective.ne hα_ne
    calc
      ∏ σ : L →ₐ[ℚ] ℂ, ‖σ α‖ < ∏ _σ : L →ₐ[ℚ] ℂ, (1 : ℝ) :=
        Finset.prod_lt_prod (fun σ _ => hσ_pos σ) (fun σ _ => hσ_bound σ)
          ⟨ι₀, Finset.mem_univ _, by simpa only [hι_val] using hlt⟩
      _ = 1 := by simp
  have hα_int_L : IsIntegral ℤ (α : L) := by
    have : IsIntegral ℤ (algebraMap L ℂ α) := hint
    rwa [isIntegral_algebraMap_iff (algebraMap L ℂ).injective] at this
  have hnorm_int : IsIntegral ℤ (Algebra.norm ℚ (α : L)) :=
    Algebra.isIntegral_norm ℚ hα_int_L
  have hnorm_ne : Algebra.norm ℚ (α : L) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hα_ne
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm_int
  have hm_ne : m ≠ 0 := by
    intro h; exact hnorm_ne (by rw [← hm]; simp [h])
  have h1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ (α : L))‖ < 1 := by
    rw [hprod]
    rw [show ‖∏ σ : L →ₐ[ℚ] ℂ, σ α‖ = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ α‖ from
      norm_prod (Finset.univ : Finset (L →ₐ[ℚ] ℂ)) (fun σ => σ α)]
    exact hprod_lt
  have h2 : 1 ≤ ‖algebraMap ℚ ℂ (Algebra.norm ℚ (α : L))‖ := by
    rw [← hm, ← IsScalarTower.algebraMap_apply ℤ ℚ ℂ m]
    rw [show (algebraMap ℤ ℂ) m = (m : ℂ) from map_intCast (algebraMap ℤ ℂ) m,
        Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm_ne
  linarith

open Finset in
/-- If the average of a nonempty finite family of complex roots of unity is integral over the integers, then the family is constant or its sum vanishes. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.4.4" (role := supporting),
  source_ref "Chapter5/Discussion_before_Lemma5.4.5" (role := supporting),
  source_ref "Chapter5/Lemma5.4.5" (role := primary)]
theorem rootsOfUnity_all_eq_or_sum_eq_zero_of_average_integral
    (n : ℕ) (hn : 0 < n)
    (ε : Fin n → ℂ)
    (hε : ∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1)
    (hint : IsIntegral ℤ ((∑ i, ε i) / n)) :
    (∀ i j, ε i = ε j) ∨ (∑ i, ε i) = 0 := by
  by_cases hsum : (∑ i, ε i) = 0
  · exact Or.inr hsum
  · left
    have hnorm_one : ∀ i, ‖ε i‖ = 1 := by
      intro i
      obtain ⟨m, hm, hpow⟩ := hε i
      exact Complex.norm_eq_one_of_pow_eq_one hpow (Nat.pos_iff_ne_zero.mp hm)
    by_contra h
    push Not at h
    obtain ⟨i, j, hij⟩ := h
    have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    have hlt : ‖(∑ i, ε i) / (n : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_natCast, div_lt_one (Nat.cast_pos.mpr hn)]
      have : ‖∑ k : Fin n, ((1 : ℝ) / n) • ε k‖ < 1 := by
        apply norm_sum_lt_of_strictConvexSpace (t := Finset.univ) (w := fun _ => (1 : ℝ) / n)
          (r := 1) (z := ε)
        · intro k _; positivity
        · simp [hnn]
        · exact Finset.mem_univ i
        · exact Finset.mem_univ j
        · exact hij
        · positivity
        · positivity
        · intro k _; rw [hnorm_one k]
      have hsum_mul :
          (∑ k : Fin n, ((1 : ℝ) / n) • ε k) =
            (n : ℂ)⁻¹ * ∑ k : Fin n, ε k := by
        simp [one_div, Finset.mul_sum]
      rw [hsum_mul] at this
      simp only [norm_mul, norm_inv, Complex.norm_natCast] at this
      have hlt_sum : ‖∑ k : Fin n, ε k‖ < (n : ℝ) * 1 :=
        (inv_mul_lt_iff₀ (Nat.cast_pos.mpr hn)).1 (by simpa using this)
      simpa [mul_one] using hlt_sum
    exact roots_of_unity_avg_norm_bound n hn ε hε hint hsum hlt

end RepresentationTheory.Complex.RootsOfUnity.AverageIntegral

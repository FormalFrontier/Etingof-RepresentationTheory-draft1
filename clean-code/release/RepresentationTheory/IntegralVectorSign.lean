/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty
import RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub
import RepresentationTheory.Alignment.Attribute

/-! # Integral vector sign -/

namespace RepresentationTheory.IntegralVectorSign

private abbrev cartanQ (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ :=
  dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x)

/-- Under the given matrix and vector hypotheses, the integer vector has either only nonnegative coordinates or only nonpositive coordinates. -/
@[source_ref "Chapter6/Lemma6.4.6" (role := supporting),
  source_ref "Chapter6/Remark6.4.8" (role := supporting)]
theorem all_nonnegative_or_all_nonpositive (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hdyn : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (x : Fin n → ℤ)
    (hroot : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x) :
    (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨i₀, hi₀⟩, ⟨j₀, hj₀⟩⟩ := h
  set A := (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) with hA_def
  set β : Fin n → ℤ := fun i => max (x i) 0
  set γ : Fin n → ℤ := fun i => min (x i) 0
  have hsum : x = β + γ := by ext i; simp only [β, γ, Pi.add_apply]; omega
  have hβ_ne : β ≠ 0 := by
    intro heq; have := congr_fun heq j₀; simp only [β, Pi.zero_apply] at this; omega
  have hγ_ne : γ ≠ 0 := by
    intro heq; have := congr_fun heq i₀; simp only [γ, Pi.zero_apply] at this; omega
  have hβ_nonneg : ∀ i, 0 ≤ β i := fun i => le_max_right _ _
  have hγ_nonpos : ∀ i, γ i ≤ 0 := fun i => min_le_right _ _
  have hβγ_zero : ∀ i, β i * γ i = 0 := by
    intro i; simp only [β, γ]
    rcases le_or_gt (x i) 0 with h | h
    · simp [max_eq_right h, min_eq_left h]
    · simp [max_eq_left h.le, min_eq_right h.le]
  have hBβ : 2 ≤ cartanQ n adj β := by
    have hpos : (0 : ℤ) < cartanQ n adj β :=
      RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub.Matrix.dotProduct_mulVec_two_smul_one_sub_pos n adj hdyn β hβ_ne
    obtain ⟨k, hk⟩ : Even (cartanQ n adj β) :=
      RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub.Matrix.even_dotProduct_mulVec_two_smul_one_sub n adj hdyn.1 hdyn.2.1 β
    omega
  have hBγ : 2 ≤ cartanQ n adj γ := by
    have hpos : (0 : ℤ) < cartanQ n adj γ :=
      RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub.Matrix.dotProduct_mulVec_two_smul_one_sub_pos n adj hdyn γ hγ_ne
    obtain ⟨k, hk⟩ : Even (cartanQ n adj γ) :=
      RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub.Matrix.even_dotProduct_mulVec_two_smul_one_sub n adj hdyn.1 hdyn.2.1 γ
    omega
  set cross := dotProduct β (A.mulVec γ)
  have hcross : 0 ≤ cross := by
    simp only [cross, dotProduct, Matrix.mulVec]
    have key : ∀ i : Fin n,
        0 ≤ β i * ∑ j,
          (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * γ j := by
      intro i
      have inner_eq :
          ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * γ j =
          2 * γ i - ∑ j, adj i j * γ j := by
        simp_rw [Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
        congr 1
        simp [Finset.sum_ite_eq, Finset.mem_univ]
      rw [inner_eq]
      rcases eq_or_lt_of_le (hβ_nonneg i) with hi | hi
      · simp [← hi]
      have hγi : γ i = 0 := by
        rcases mul_eq_zero.mp (hβγ_zero i) with h | h
        · linarith
        · exact h
      rw [hγi, mul_zero, zero_sub]
      apply mul_nonneg hi.le
      rw [neg_nonneg]
      apply Finset.sum_nonpos
      intro j _
      rcases hdyn.2.2.1 i j with h0 | h1
      · simp [h0]
      · rw [h1, one_mul]; exact hγ_nonpos j
    exact Finset.sum_nonneg (fun i _ => key i)
  set cross' := dotProduct γ (A.mulVec β)
  have hcross' : 0 ≤ cross' := by
    simp only [cross', dotProduct, Matrix.mulVec]
    have key : ∀ i : Fin n,
        0 ≤ γ i * ∑ j,
          (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * β j := by
      intro i
      have inner_eq :
          ∑ j, (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) i j * β j =
          2 * β i - ∑ j, adj i j * β j := by
        simp_rw [Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]
        congr 1
        simp [Finset.sum_ite_eq, Finset.mem_univ]
      rw [inner_eq]
      rcases eq_or_lt_of_le (hγ_nonpos i) with hi | hi
      · simp [hi]
      · have hγi_neg : γ i < 0 := by linarith
        have hβi : β i = 0 := by
          rcases mul_eq_zero.mp (hβγ_zero i) with h | h
          · exact h
          · linarith
        rw [hβi, mul_zero, zero_sub]
        apply mul_nonneg_of_nonpos_of_nonpos (hγ_nonpos i)
        rw [neg_nonpos]
        apply Finset.sum_nonneg
        intro j _
        rcases hdyn.2.2.1 i j with h0 | h1
        · simp [h0]
        · rw [h1, one_mul]; exact hβ_nonneg j
    exact Finset.sum_nonneg (fun i _ => key i)
  have hBx : cartanQ n adj x =
      cartanQ n adj β + cross + cross' + cartanQ n adj γ := by
    change dotProduct x (A.mulVec x) = _
    conv_lhs => rw [hsum]
    simp only [add_dotProduct, dotProduct_add, Matrix.mulVec_add]
    ring
  have : cartanQ n adj x = 2 := hroot.2
  linarith

end RepresentationTheory.IntegralVectorSign

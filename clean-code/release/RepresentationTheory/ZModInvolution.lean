/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib

/-!
# ZMod involution
-/

namespace RepresentationTheory.ZModInvolution

variable (q : ℕ)

/-- A transformation of integers modulo `q^2 - 1`. -/
def zmodTransform (x : ZMod (q ^ 2 - 1)) : ZMod (q ^ 2 - 1) := (q : ZMod (q ^ 2 - 1)) * x

/-- An auxiliary finite set of integers modulo `q^2 - 1`. -/
def auxiliaryZModFinsetA [NeZero (q ^ 2 - 1)] : Finset (ZMod (q ^ 2 - 1)) :=
  Finset.univ.filter (fun x => zmodTransform q x ≠ x)

/-- Another auxiliary finite set of integers modulo `q^2 - 1`. -/
def auxiliaryZModFinsetB [NeZero (q ^ 2 - 1)] : Finset (ZMod (q ^ 2 - 1)) :=
  (auxiliaryZModFinsetA q).filter (fun x => x.val < (zmodTransform q x).val)

private lemma four_le (hq : 2 ≤ q) : 4 ≤ q ^ 2 := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2

private lemma factor_eq (hq : 2 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have h1 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
  have h2 : (m + 1 - 1) * (m + 1 + 1) = m * m + 2 * m := by
    have hm : m + 1 - 1 = m := by omega
    rw [hm]; ring
  rw [h1, h2]; omega

/-- Characterizes fixed points by divisibility of their natural representatives. -/
lemma zmodTransform_fixed_iff (hq : 2 ≤ q) (x : ZMod (q ^ 2 - 1)) :
    zmodTransform q x = x ↔ (q + 1) ∣ x.val := by
  haveI : NeZero (q ^ 2 - 1) := ⟨by have := four_le q hq; omega⟩
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := factor_eq q hq
  have hq1 : (q - 1 : ℕ) ≠ 0 := by omega
  simp only [zmodTransform]
  constructor
  · intro h
    have hz : ((q - 1 : ℕ) : ZMod (q ^ 2 - 1)) * x = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_mul, one_mul, sub_eq_zero]
      exact h
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hz
    rw [← mul_dvd_mul_iff_left hq1, ← hfac]
    exact hz
  · intro h
    have hz : (q ^ 2 - 1) ∣ (q - 1) * x.val := by
      have h2 : (q - 1) * (q + 1) ∣ (q - 1) * x.val := mul_dvd_mul_left _ h
      rwa [← hfac] at h2
    have hzero : ((q - 1 : ℕ) : ZMod (q ^ 2 - 1)) * x = 0 := by
      rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact hz
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_mul, one_mul, sub_eq_zero] at hzero
    exact hzero

/-- The transformation has `q - 1` fixed points. -/
lemma card_zmodTransform_fixedPoints [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    (Finset.univ.filter (fun x : ZMod (q ^ 2 - 1) => zmodTransform q x = x)).card = q - 1 := by
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := factor_eq q hq
  have hlt_k : ∀ k, k < q - 1 → (q + 1) * k < q ^ 2 - 1 := by
    intro k hk
    rw [hfac, mul_comm (q - 1) (q + 1)]
    gcongr
  rw [show q - 1 = (Finset.range (q - 1)).card from (Finset.card_range _).symm]
  apply Finset.card_nbij' (fun x => x.val / (q + 1))
    (fun k => (((q + 1) * k : ℕ) : ZMod (q ^ 2 - 1)))
  ·
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_range]
    have hdvd : (q + 1) ∣ x.val := (zmodTransform_fixed_iff q hq x).mp hx.2
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1), ← hfac]
    exact ZMod.val_lt x
  ·
    intro k hk
    rw [Finset.mem_coe, Finset.mem_range] at hk
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [zmodTransform_fixed_iff q hq, ZMod.val_natCast_of_lt (hlt_k k hk)]
    exact dvd_mul_right (q + 1) k
  ·
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    have hdvd : (q + 1) ∣ x.val := (zmodTransform_fixed_iff q hq x).mp hx.2
    change (((q + 1) * (x.val / (q + 1)) : ℕ) : ZMod (q ^ 2 - 1)) = x
    rw [Nat.mul_div_cancel' hdvd]
    exact ZMod.natCast_zmod_val x
  ·
    intro k hk
    rw [Finset.mem_coe, Finset.mem_range] at hk
    change ((((q + 1) * k : ℕ) : ZMod (q ^ 2 - 1)).val) / (q + 1) = k
    rw [ZMod.val_natCast_of_lt (hlt_k k hk)]
    exact Nat.mul_div_cancel_left k (by omega)

/-- An element belongs to the first auxiliary finite set exactly when it is not fixed. -/
lemma mem_auxiliaryZModFinsetA_iff [NeZero (q ^ 2 - 1)] (x : ZMod (q ^ 2 - 1)) :
    x ∈ auxiliaryZModFinsetA q ↔ zmodTransform q x ≠ x := by
  simp only [auxiliaryZModFinsetA, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The first auxiliary finite set has cardinality `q * (q - 1)`. -/
theorem card_auxiliaryZModFinsetA [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) : (auxiliaryZModFinsetA q).card = q * (q - 1) := by
  classical
  set F := Finset.univ.filter (fun x : ZMod (q ^ 2 - 1) => zmodTransform q x = x) with hF
  have hdisj : Disjoint (auxiliaryZModFinsetA q) F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [mem_auxiliaryZModFinsetA_iff] at ha
    rw [hF, Finset.mem_filter] at haF
    exact ha haF.2
  have hunion : auxiliaryZModFinsetA q ∪ F = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    rw [Finset.mem_union, mem_auxiliaryZModFinsetA_iff, hF, Finset.mem_filter]
    by_cases h : zmodTransform q a = a
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
    · exact Or.inl h
  have hcard : (auxiliaryZModFinsetA q).card + F.card = q ^ 2 - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, ZMod.card]
  have hFcard : F.card = q - 1 := by rw [hF]; exact card_zmodTransform_fixedPoints q hq
  have halg : q ^ 2 - 1 - (q - 1) = q * (q - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
    have h2 : (m + 1) * m = m * m + m := by ring
    rw [h1, h2]; omega
  omega

/-- Applying the transformation twice is the identity when `q ≥ 2`. -/
lemma zmodTransform_involutive (hq : 2 ≤ q) (x : ZMod (q ^ 2 - 1)) : zmodTransform q (zmodTransform q x) = x := by
  haveI : NeZero (q ^ 2 - 1) := ⟨by have := four_le q hq; omega⟩
  have hsq : (q : ZMod (q ^ 2 - 1)) ^ 2 = 1 := by
    have e1 : ((q ^ 2 : ℕ) : ZMod (q ^ 2 - 1)) = (q : ZMod (q ^ 2 - 1)) ^ 2 := by push_cast; ring
    have e2 : (q ^ 2 : ℕ) = (q ^ 2 - 1) + 1 := by have := four_le q hq; omega
    rw [← e1, e2, Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, zero_add]
  simp only [zmodTransform]
  rw [← mul_assoc, ← pow_two, hsq, one_mul]

/-- The second auxiliary finite set and its transformed image are disjoint, have equal cardinality, and have union equal to the first auxiliary finite set. -/
theorem auxiliaryZModFinsets_partition [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    Disjoint (auxiliaryZModFinsetB q) ((auxiliaryZModFinsetB q).image (zmodTransform q))
      ∧ (auxiliaryZModFinsetB q) ∪ (auxiliaryZModFinsetB q).image (zmodTransform q) = auxiliaryZModFinsetA q
      ∧ ((auxiliaryZModFinsetB q).image (zmodTransform q)).card = (auxiliaryZModFinsetB q).card := by
  classical
  have hinv : Function.Involutive (zmodTransform q) := zmodTransform_involutive q hq
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    simp only [auxiliaryZModFinsetB, Finset.mem_filter] at ha hx
    obtain ⟨_, ha2⟩ := ha
    obtain ⟨_, hx2⟩ := hx
    rw [zmodTransform_involutive q hq] at ha2
    omega
  ·
    apply Finset.Subset.antisymm
    · intro a ha
      rw [Finset.mem_union] at ha
      rcases ha with ha | ha
      · simp only [auxiliaryZModFinsetB, Finset.mem_filter] at ha; exact ha.1
      · rw [Finset.mem_image] at ha
        obtain ⟨x, hx, rfl⟩ := ha
        simp only [auxiliaryZModFinsetB, Finset.mem_filter] at hx
        have hxne : zmodTransform q x ≠ x := (mem_auxiliaryZModFinsetA_iff q x).mp hx.1
        have hne2 : zmodTransform q (zmodTransform q x) ≠ zmodTransform q x := by
          rw [zmodTransform_involutive q hq]; exact Ne.symm hxne
        exact (mem_auxiliaryZModFinsetA_iff q (zmodTransform q x)).mpr hne2
    · intro a ha
      rw [Finset.mem_union]
      by_cases hlt : a.val < (zmodTransform q a).val
      · left; simp only [auxiliaryZModFinsetB, Finset.mem_filter]; exact ⟨ha, hlt⟩
      · right
        rw [Finset.mem_image]
        refine ⟨zmodTransform q a, ?_, zmodTransform_involutive q hq a⟩
        simp only [auxiliaryZModFinsetB, Finset.mem_filter]
        have hane : zmodTransform q a ≠ a := (mem_auxiliaryZModFinsetA_iff q a).mp ha
        have hmem : zmodTransform q a ∈ auxiliaryZModFinsetA q := by
          have hne2 : zmodTransform q (zmodTransform q a) ≠ zmodTransform q a := by
            rw [zmodTransform_involutive q hq]; exact Ne.symm hane
          exact (mem_auxiliaryZModFinsetA_iff q (zmodTransform q a)).mpr hne2
        refine ⟨hmem, ?_⟩
        rw [zmodTransform_involutive q hq]
        have hvalne : (zmodTransform q a).val ≠ a.val := fun h => hane (ZMod.val_injective _ h)
        omega
  ·
    exact Finset.card_image_of_injective _ hinv.injective

/-- The second auxiliary finite set has cardinality `q * (q - 1) / 2`. -/
theorem card_auxiliaryZModFinsetB [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    (auxiliaryZModFinsetB q).card = q * (q - 1) / 2 := by
  obtain ⟨hdisj, hunion, hcard⟩ := auxiliaryZModFinsets_partition q hq
  have h2 : (auxiliaryZModFinsetA q).card = (auxiliaryZModFinsetB q).card + (auxiliaryZModFinsetB q).card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hcard]
  have hmc : (auxiliaryZModFinsetA q).card = q * (q - 1) := card_auxiliaryZModFinsetA q hq
  omega

end RepresentationTheory.ZModInvolution

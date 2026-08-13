/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.FDRep.Character
import RepresentationTheory.Alignment.Attribute

/-!
# An irreducibility criterion for finite-group characters
-/

namespace RepresentationTheory.FiniteGroup.Character.Irreducibility

open scoped Classical in
/-- An integral linear combination of pairwise nonisomorphic simple characters with self-inner
product one and positive degree has exactly one coefficient equal to one. -/
@[source_ref "Chapter5/Discussion_before_Lemma5.7.2" (role := supporting),
  source_ref "Chapter5/Lemma5.7.2" (role := primary)]
theorem exists_singleton_of_character_selfInner_eq_one
    {G : Type} [Group G] [Fintype G] [Invertible (Fintype.card G : ℂ)]
    {ι : Type*} [Fintype ι]
    (W : ι → FDRep ℂ G) [∀ i, CategoryTheory.Simple (W i)]
    (hdistinct : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (n : ι → ℤ)
    (hnorm : ⅟(Fintype.card G : ℂ) •
        ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
                 (∑ j, (n j : ℂ) * (W j).character g⁻¹) = 1)
    (hpos : 0 < ∑ i, n i * (Module.finrank ℂ (W i) : ℤ)) :
    ∃ i₀, n i₀ = 1 ∧ ∀ i, i ≠ i₀ → n i = 0 := by
  have hdpos : ∀ i, 0 < Module.finrank ℂ (W i) := by
    intro i
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (W i)) with hfr0 | hposi
    · exfalso
      haveI : Subsingleton (W i) := Module.finrank_zero_iff.mp hfr0
      have hzero : ∀ g : G, (W i).character g = 0 := fun g => by
        rw [FDRep.character, Subsingleton.elim ((W i).ρ g) 0, map_zero]
      have h1 :=
        RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple
          (W i) (W i)
      rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at h1
      simp only [hzero, zero_mul, Finset.sum_const_zero, smul_zero] at h1
      exact one_ne_zero h1.symm
    · exact hposi
  have horth : ∀ i j, ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (W i).character g * (W j).character g⁻¹ =
        if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple
      (W i) (W j)]
    have hiff : Nonempty (W i ≅ W j) ↔ i = j :=
      ⟨hdistinct i j, fun h => ⟨h ▸ CategoryTheory.Iso.refl (W i)⟩⟩
    simp [hiff]
  have hexpand : ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
               (∑ j, (n j : ℂ) * (W j).character g⁻¹) = ∑ i, (n i : ℂ) ^ 2 := by
    have hAB : ∀ g : G,
        (∑ i, (n i : ℂ) * (W i).character g) *
          (∑ j, (n j : ℂ) * (W j).character g⁻¹) =
        ∑ i, ∑ j, (n i : ℂ) * (n j) *
            ((W i).character g * (W j).character g⁻¹) := by
      intro g
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    have reorder : ∀ (T : G → ι → ι → ℂ),
        (∑ g : G, ∑ i, ∑ j, T g i j) = ∑ i, ∑ j, ∑ g : G, T g i j := by
      intro T
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
    calc ⅟(Fintype.card G : ℂ) •
            ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
                     (∑ j, (n j : ℂ) * (W j).character g⁻¹)
        = ⅟(Fintype.card G : ℂ) • ∑ g : G, ∑ i, ∑ j,
            (n i : ℂ) * (n j) * ((W i).character g * (W j).character g⁻¹) := by
          rw [Finset.sum_congr rfl (fun g _ => hAB g)]
      _ = ⅟(Fintype.card G : ℂ) • ∑ i, ∑ j,
            (n i : ℂ) * (n j) * ∑ g : G, ((W i).character g * (W j).character g⁻¹) := by
          rw [reorder]
          refine congrArg _ (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
            (fun j _ => ?_)))
          rw [← Finset.mul_sum]
      _ = ∑ i, ∑ j, (n i : ℂ) * (n j) *
            (⅟(Fintype.card G : ℂ) •
              ∑ g : G, ((W i).character g * (W j).character g⁻¹)) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [smul_eq_mul, smul_eq_mul]; ring
      _ = ∑ i, ∑ j, (n i : ℂ) * (n j) * (if i = j then (1 : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [horth i j]
      _ = ∑ i, (n i : ℂ) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [mul_ite, mul_one, mul_zero]
          rw [Fintype.sum_ite_eq i (fun j => (n i : ℂ) * (n j))]
          ring
  have hcomplex : ∑ i, (n i : ℂ) ^ 2 = 1 := by rw [← hexpand]; exact hnorm
  have hZ : ∑ i, (n i) ^ 2 = 1 := by
    have hc : ((∑ i, (n i) ^ 2 : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; exact hcomplex
    exact_mod_cast hc
  have hne : ∃ i₀, (n i₀) ^ 2 ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : ∑ i, (n i) ^ 2 = 0 := Finset.sum_eq_zero (fun i _ => h i)
    rw [h0] at hZ; exact zero_ne_one hZ
  obtain ⟨i₀, hi0⟩ := hne
  have hi0pos : 0 < (n i₀) ^ 2 := (sq_nonneg _).lt_of_ne (Ne.symm hi0)
  have hsplit : (n i₀) ^ 2 + ∑ i ∈ Finset.univ.erase i₀, (n i) ^ 2 = 1 := by
    rw [Finset.add_sum_erase Finset.univ (fun i => (n i) ^ 2) (Finset.mem_univ i₀)]; exact hZ
  have hrest_nonneg : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, (n i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hni0sq : (n i₀) ^ 2 = 1 := by omega
  have hrest_zero : ∑ i ∈ Finset.univ.erase i₀, (n i) ^ 2 = 0 := by omega
  have hzero_rest : ∀ i ∈ Finset.univ.erase i₀, (n i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hrest_zero
  have hn_rest : ∀ i, i ≠ i₀ → n i = 0 := by
    intro i hi
    have hsq := hzero_rest i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    exact (pow_eq_zero_iff (two_ne_zero)).mp hsq
  have hpm : n i₀ = 1 ∨ n i₀ = -1 := by
    rw [sq] at hni0sq; exact mul_self_eq_one_iff.mp hni0sq
  have hdimsum : ∑ i, n i * (Module.finrank ℂ (W i) : ℤ) =
      n i₀ * (Module.finrank ℂ (W i₀) : ℤ) := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun i => n i * (Module.finrank ℂ (W i) : ℤ)) (Finset.mem_univ i₀)]
    have hz : ∑ i ∈ Finset.univ.erase i₀,
        n i * (Module.finrank ℂ (W i) : ℤ) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [hn_rest i (Finset.mem_erase.mp hi).1, zero_mul]
    rw [hz, add_zero]
  have hdpos₀ : 0 < (Module.finrank ℂ (W i₀) : ℤ) := by
    exact_mod_cast hdpos i₀
  have hprodpos : 0 < n i₀ * (Module.finrank ℂ (W i₀) : ℤ) := hdimsum ▸ hpos
  rcases hpm with h1 | hm1
  · exact ⟨i₀, h1, hn_rest⟩
  · exfalso
    rw [hm1] at hprodpos
    nlinarith [hprodpos, hdpos₀]

end RepresentationTheory.FiniteGroup.Character.Irreducibility

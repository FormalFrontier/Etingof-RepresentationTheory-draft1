/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Group.CharacterOperations
import RepresentationTheory.FiniteGroup.Character.Irreducibility
import RepresentationTheory.FDRep.CharacterDecomposition
import RepresentationTheory.FDRep.GroupAlgebraDecomposition

/-!
# Representations realizing character differences

This module realizes a normalized character difference of positive dimension as the character of a
simple finite-dimensional representation.
-/

open CategoryTheory Module
  RepresentationTheory.Group.CharacterOperations
  RepresentationTheory.FiniteGroup.Character.Irreducibility
  RepresentationTheory.FDRep.CharacterDecomposition
  RepresentationTheory.FDRep.GroupAlgebraDecomposition

namespace RepresentationTheory.FDRep.CharacterDifference

variable {G : Type} [Group G] [Fintype G]

/-- If the normalized squared norm of a character difference is one and the dimension difference is
positive, that difference is the character of a simple representation. -/
theorem exists_simple_character_eq_sub_of_norm_eq_one (A B : FDRep ℂ G)
    (hnorm : (Fintype.card G : ℂ)⁻¹ •
      ∑ g : G, (A.character g - B.character g) *
        (starRingEnd ℂ) (A.character g - B.character g) = 1)
    (hpos : finrank ℂ B < finrank ℂ A) :
    ∃ W : FDRep ℂ G, Simple W ∧
      ∀ g : G, W.character g = A.character g - B.character g := by
  classical
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'⟩
  obtain ⟨N, T, hT, hinj, hcomplete, -⟩ :=
    exists_completeSimpleFamily_sum_finrank_sq_eq_card ℂ G
  haveI : ∀ i, Simple (T i) := hT
  obtain ⟨a, ha⟩ := exists_character_eq_sum_smul T hcomplete A
  obtain ⟨b, hb⟩ := exists_character_eq_sum_smul T hcomplete B
  obtain ⟨m, hm⟩ : ∃ m : Fin N → ℤ, ∀ g : G,
      ∑ i, (m i : ℂ) * (T i).character g = A.character g - B.character g := by
    refine ⟨fun i => (a i : ℤ) - (b i : ℤ), fun g => ?_⟩
    rw [ha g, hb g, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      push_cast
      ring
  have hnorm' : ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (∑ i, (m i : ℂ) * (T i).character g) *
               (∑ j, (m j : ℂ) * (T j).character g⁻¹) = 1 := by
    rw [invOf_eq_inv]
    rw [← hnorm]
    refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
    rw [hm g, hm g⁻¹, map_sub, ← character_inv_eq_conj, ← character_inv_eq_conj]
  have hdim : ∑ i, m i * (finrank ℂ (T i) : ℤ) =
      (finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) := by
    have hC : ((∑ i, m i * (finrank ℂ (T i) : ℤ) : ℤ) : ℂ) =
        (((finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) : ℤ) : ℂ) := by
      have h1 := hm 1
      simp only [FDRep.char_one] at h1
      push_cast
      exact h1
    exact_mod_cast hC
  have hpos' : 0 < ∑ i, m i * (finrank ℂ (T i) : ℤ) := by
    rw [hdim]
    omega
  obtain ⟨i₀, hi₀, hrest⟩ :=
    exists_singleton_of_character_selfInner_eq_one T hinj m hnorm' hpos'
  refine ⟨T i₀, hT i₀, fun g => ?_⟩
  rw [← hm g, Finset.sum_eq_single i₀ (fun i _ hi => by rw [hrest i hi]; simp)
    (fun h => absurd (Finset.mem_univ i₀) h), hi₀]
  simp

section Choice

variable (A B : FDRep ℂ G)
  (hnorm : (Fintype.card G : ℂ)⁻¹ •
    ∑ g : G, (A.character g - B.character g) *
      (starRingEnd ℂ) (A.character g - B.character g) = 1)
  (hpos : finrank ℂ B < finrank ℂ A)

/-- A complex finite-dimensional representation selected from a normalized character difference
with positive dimension difference. -/
noncomputable def characterDifferenceRepresentation : FDRep ℂ G :=
  (exists_simple_character_eq_sub_of_norm_eq_one A B hnorm hpos).choose

/-- The representation selected from the character-difference hypotheses is simple. -/
instance simple_characterDifferenceRepresentation :
    Simple (characterDifferenceRepresentation A B hnorm hpos) :=
  (exists_simple_character_eq_sub_of_norm_eq_one A B hnorm hpos).choose_spec.1

/-- The character of the selected representation is the difference of the two given characters. -/
@[simp]
lemma character_characterDifferenceRepresentation (g : G) :
    (characterDifferenceRepresentation A B hnorm hpos).character g =
      A.character g - B.character g :=
  (exists_simple_character_eq_sub_of_norm_eq_one A B hnorm hpos).choose_spec.2 g

/-- The dimension of the selected character-difference representation is the difference of the two
original dimensions. -/
lemma finrank_characterDifferenceRepresentation :
    finrank ℂ (characterDifferenceRepresentation A B hnorm hpos) =
      finrank ℂ A - finrank ℂ B := by
  have h := character_characterDifferenceRepresentation A B hnorm hpos 1
  simp only [FDRep.char_one] at h
  have : ((finrank ℂ (characterDifferenceRepresentation A B hnorm hpos) : ℤ) : ℂ) =
      ((finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) : ℤ) := by
    push_cast
    exact h
  have hZ : (finrank ℂ (characterDifferenceRepresentation A B hnorm hpos) : ℤ) =
      (finrank ℂ A : ℤ) - (finrank ℂ B : ℤ) := by
    exact_mod_cast this
  omega

end Choice

end RepresentationTheory.FDRep.CharacterDifference

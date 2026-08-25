/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.VirtualRepresentations.Basic
import RepresentationTheory.FiniteGroup.Character.Irreducibility

open CategoryTheory

namespace RepresentationTheory.VirtualRepresentations.Basic.VirtualRepresentation

variable {G : Type} [Group G] [Fintype G]

/-- Two support indices are equal when their associated finite-dimensional representations are isomorphic. -/
theorem support_index_eq_of_iso (V : VirtualRepresentation G) :
    ∀ i j : (V.support : Finset (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)),
      Nonempty (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.representation
        (i : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G) ≅
        RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.representation
          (j : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)) → i = j :=
  fun _ _ h => Subtype.ext
    (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.representation_iso_iff_eq _ _ |>.mp h)

/-- A virtual character is the sum over all indexed simple representations of its coefficients times their characters. -/
theorem character_eq_sum_univ (V : VirtualRepresentation G) (g : G) :
    character V g =
      ∑ i : (V.support : Finset (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)),
        ((V (i : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G) : ℂ)) *
          (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.representation
            (i : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)).character g := by
  rw [character_apply, ← Finset.sum_coe_sort V.support]
  exact Finset.sum_congr rfl fun i _ => by
    rw [RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.character_representation]

/-- The virtual dimension is the sum over all indexed simple representations of coefficient times finite dimension. -/
theorem dim_eq_sum_univ (V : VirtualRepresentation G) :
    V.dim =
      ∑ i : (V.support : Finset (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)),
        V (i : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G) *
          (Module.finrank ℂ (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.representation
            (i : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)) : ℤ) := by
  rw [dim_eq_sum_support, ← Finset.sum_coe_sort V.support]
  exact Finset.sum_congr rfl fun i _ => by
    rw [RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.finrank_representation]

/-- A positive-dimensional virtual representation whose normalized character self-sum is one is one copy of a simple representation. -/
theorem eq_simpleMultiple_one_of_character_norm_one [Invertible (Fintype.card G : ℂ)]
    (V : VirtualRepresentation G)
    (hnorm : ⅟(Fintype.card G : ℂ) • ∑ g : G, character V g * character V g⁻¹ = 1)
    (hpos : 0 < V.dim) :
    ∃ (W : FDRep ℂ G) (hW : Simple W), V = simpleMultiple W hW 1 := by
  classical
  set ι := (V.support : Finset (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)) with hι
  set W : ι → FDRep ℂ G := fun i =>
    RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.representation
      (i : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G) with hW
  set n : ι → ℤ := fun i =>
    V (i : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G) with hn
  have hnorm' : ⅟(Fintype.card G : ℂ) •
      ∑ g : G, (∑ i, (n i : ℂ) * (W i).character g) *
               (∑ j, (n j : ℂ) * (W j).character g⁻¹) = 1 := by
    refine Eq.trans (congrArg _ (Finset.sum_congr rfl fun g _ => ?_)) hnorm
    rw [← character_eq_sum_univ V g, ← character_eq_sum_univ V g⁻¹]
  have hpos' : 0 < ∑ i, n i * (Module.finrank ℂ (W i) : ℤ) := by
    rw [← dim_eq_sum_univ V]; exact hpos
  obtain ⟨i₀, hi₀, hrest⟩ :=
    RepresentationTheory.FiniteGroup.Character.Irreducibility.exists_singleton_of_character_selfInner_eq_one
      (G := G) (ι := ι) W (support_index_eq_of_iso V) n hnorm' hpos'
  refine ⟨RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.representation
    (i₀ : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G),
    RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.simple_representation _, ?_⟩
  rw [simpleMultiple,
    RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.ofSimple_representation]
  ext c
  by_cases hc : c = (i₀ : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G)
  · subst hc; simpa using hi₀
  · rw [show (Finsupp.single
      (i₀ : RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter ℂ G) (1 : ℤ)) c = 0 from by
      simp [Ne.symm hc]]
    by_cases hmem : c ∈ V.support
    · exact hrest ⟨c, hmem⟩ (fun h => hc (congrArg Subtype.val h))
    · exact Finsupp.notMem_support_iff.mp hmem

/-- A positive-dimensional virtual representation whose normalized character self-sum is one has the character of a finite-dimensional representation. -/
theorem character_eq_simple_of_character_norm_one [Invertible (Fintype.card G : ℂ)]
    (V : VirtualRepresentation G)
    (hnorm : ⅟(Fintype.card G : ℂ) • ∑ g : G, character V g * character V g⁻¹ = 1)
    (hpos : 0 < V.dim) :
    ∃ (W : FDRep ℂ G) (_ : Simple W), character V = W.character := by
  obtain ⟨W, hW, hV⟩ := eq_simpleMultiple_one_of_character_norm_one V hnorm hpos
  exact ⟨W, hW, by rw [hV, character_simple]⟩

end RepresentationTheory.VirtualRepresentations.Basic.VirtualRepresentation

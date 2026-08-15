/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.GroupAlgebraDecomposition

open CategoryTheory

universe u v

namespace RepresentationTheory.representation_theory.finite_group.simple_exhaustion

/-- A finite pairwise nonisomorphic family of simple representations contains an isomorphic copy of every simple representation if the sum of its squared dimensions equals the group cardinality. -/
theorem exists_iso_of_sum_finrank_sq_eq_card
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)]
    {ι : Type v} [Fintype ι] (W : ι → FDRep k G)
    (hW : ∀ j, Simple (W j))
    (hinj : ∀ j j', Nonempty (W j ≅ W j') → j = j')
    (hsum : ∑ j, (Module.finrank k (W j)) ^ 2 = Fintype.card G)
    (X : FDRep k G) (hX : Simple X) :
    ∃ j, Nonempty (X ≅ W j) := by
  classical
  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  choose τ hτ using fun j => D.exists_iso_representation_of_simple (W j) (hW j)
  have hτ_inj : Function.Injective τ := by
    intro j j' h
    exact hinj j j' ⟨(hτ j).some ≪≫ (h ▸ (hτ j').some.symm)⟩
  have hfr : ∀ j, (Module.finrank k (W j)) ^ 2 = (D.dimension (τ j)) ^ 2 := by
    intro j
    rw [← D.finrank_representation (τ j),
      LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ j).some)]
  have hsum' : ∑ i ∈ Finset.univ.image τ, (D.dimension i) ^ 2 = ∑ i : Fin D.count, (D.dimension i) ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ h => hτ_inj h)]
    rw [← D.sum_dimension_sq_eq_card] at hsum
    rw [← hsum]
    exact Finset.sum_congr rfl (fun j _ => (hfr j).symm)
  have hτ_surj : Function.Surjective τ := by
    intro i
    by_contra hi
    have hi₀ : i ∉ Finset.univ.image τ := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun j => fun h => hi ⟨j, h⟩
    have hpos : 0 < (D.dimension i) ^ 2 := by
      have := (D.dimension_neZero i).out; positivity
    have hlt : ∑ i ∈ Finset.univ.image τ, (D.dimension i) ^ 2 < ∑ i : Fin D.count, (D.dimension i) ^ 2 :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ i) hi₀ hpos
        (fun k _ _ => Nat.zero_le _)
    exact absurd hsum' (ne_of_lt hlt)
  obtain ⟨i₀, hi₀⟩ := D.exists_iso_representation_of_simple X hX
  obtain ⟨j, hj⟩ := hτ_surj i₀
  subst hj
  exact ⟨j, ⟨hi₀.some ≪≫ (hτ j).some.symm⟩⟩

end RepresentationTheory.representation_theory.finite_group.simple_exhaustion

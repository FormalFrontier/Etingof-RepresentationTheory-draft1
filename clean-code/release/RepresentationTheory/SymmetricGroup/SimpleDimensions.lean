/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SimpleSymmetricGroupRepresentations
import RepresentationTheory.InvolutionRankSum
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.SymmetricGroup.SimpleDimensions

open _root_.CategoryTheory

private lemma fdRep_auxiliaryInvariant_eq_auxiliaryRepresentationScalar
    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    [Invertible (Fintype.card G : ℂ)] (W : FDRep ℂ G) :
    RepresentationTheory.FDRep.Auxiliary.auxiliaryInvariant W =
      RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar W.ρ := by
  unfold RepresentationTheory.FDRep.Auxiliary.auxiliaryInvariant
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar
  rw [invOf_eq_inv, smul_eq_mul]
  rfl

/-- For a finite, nonredundant, exhaustive family of simple finite-dimensional complex representations of the permutations of `Fin n`, the sum of their dimensions equals the number of permutations whose square is the identity. -/
@[source_ref "Chapter5/Problem5.12.5" (role := primary)]
theorem sum_finrank_simple_eq_card_involutions
    (n : ℕ)
    (ι : Type) [Fintype ι]
    (V : ι → FDRep ℂ (Equiv.Perm (Fin n)))
    (hsimple : ∀ i, Simple (V i))
    (hpairwise : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hcomplete : ∀ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∑ i, Module.finrank ℂ (V i) =
      Fintype.card {g : Equiv.Perm (Fin n) // g * g = 1} := by
  classical
  set G := Equiv.Perm (Fin n) with hG
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ G :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  have h_all_real : ∀ i,
      RepresentationTheory.FDRep.Auxiliary.auxiliaryInvariant (D.representation i) = 1 := by
    intro i
    rw [fdRep_auxiliaryInvariant_eq_auxiliaryRepresentationScalar]
    exact
      RepresentationTheory.SimpleSymmetricGroupRepresentations.simpleSymmetricGroupRepresentation_value_eq_one
        n (D.representation i).ρ (D.isSimpleModule_coordinateRepresentation i)
  have hcor :=
    RepresentationTheory.InvolutionRankSum.cast_card_sq_eq_one_eq_sum_finrank_of_auxiliary_values_eq_one
      D D.representation D.simple_representation D.representation_index_eq_of_iso h_all_real
  have hsumeq : ∑ i, Module.finrank ℂ (V i) =
      ∑ j, Module.finrank ℂ (D.representation j) := by
    choose τ hτ using fun i => D.exists_iso_representation_of_simple (V i) (hsimple i)
    have hτinj : Function.Injective τ := fun i j h =>
      hpairwise i j ⟨(hτ i).some ≪≫ (h ▸ (hτ j).some.symm)⟩
    have hτsurj : Function.Surjective τ := by
      intro j
      obtain ⟨i, hi⟩ := hcomplete (D.representation j) (D.simple_representation j)
      exact ⟨i, (D.representation_index_eq_of_iso j (τ i)
        ⟨hi.some ≪≫ (hτ i).some⟩).symm⟩
    let e := Equiv.ofBijective τ ⟨hτinj, hτsurj⟩
    calc ∑ i, Module.finrank ℂ (V i)
        = ∑ i, Module.finrank ℂ (D.representation (τ i)) :=
          Finset.sum_congr rfl fun i _ =>
            LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ i).some)
      _ = ∑ j, Module.finrank ℂ (D.representation j) :=
          Equiv.sum_comp e (fun j => Module.finrank ℂ (D.representation j))
  have hcast : ((∑ i, Module.finrank ℂ (V i) : ℕ) : ℂ)
      = ((∑ j, Module.finrank ℂ (D.representation j) : ℕ) : ℂ) := by rw [hsumeq]
  have key : ((∑ i, Module.finrank ℂ (V i) : ℕ) : ℂ)
      = (Fintype.card {g : G // g * g = 1} : ℂ) := by
    rw [hcast, Nat.cast_sum, ← hcor, Fintype.card_subtype]
  exact_mod_cast key

end RepresentationTheory.SymmetricGroup.SimpleDimensions

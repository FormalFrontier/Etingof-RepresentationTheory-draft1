/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.Auxiliary
import RepresentationTheory.Representation.Character.InversionAndInvariantForms
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Alignment.Attribute

open FDRep CategoryTheory

universe u

namespace RepresentationTheory.InvolutionRankSum

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- If the displayed auxiliary value is one for every indexed simple representation and the representations are pairwise nonisomorphic, the cast count of group elements squaring to one equals the sum of their finranks. -/
theorem cast_card_sq_eq_one_eq_sum_finrank_of_auxiliary_values_eq_one
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    [Invertible (Fintype.card G : k)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G)
    (V : Fin D.count → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (h_all_real : ∀ i, RepresentationTheory.FDRep.Auxiliary.auxiliaryInvariant (V i) = 1) :
    (Finset.univ.filter (fun g : G => g * g = 1)).card =
    ∑ i : Fin D.count, (Module.finrank k (V i) : k) := by
  rw [RepresentationTheory.FDRep.Auxiliary.card_sq_eq_one_eq_sum_finrank_mul_auxiliaryInvariant
    D V hV hinj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [h_all_real i, mul_one]

/-- For pairwise nonisomorphic indexed simple complex representations satisfying the displayed auxiliary condition, the cast count of group elements squaring to one equals the sum of their finranks. -/
@[source_ref "Chapter5/Corollary5.1.6" (role := supporting)]
theorem complex_cast_card_sq_eq_one_eq_sum_finrank_of_auxiliary_condition
    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ G)
    (V : Fin D.count → FDRep ℂ G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (h_all_real : ∀ i,
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo
        (V i).ρ) :
    ((Finset.univ.filter (fun g : G => g * g = 1)).card : ℂ) =
      ∑ i : Fin D.count, (Module.finrank ℂ (V i) : ℂ) := by
  exact_mod_cast cast_card_sq_eq_one_eq_sum_finrank_of_auxiliary_values_eq_one
    D V hV hinj (fun i => by
      rw [← RepresentationTheory.FDRep.Auxiliary.representationInvariant_eq_auxiliaryInvariant]
      letI := hV i
      exact
        RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_eq_one_of_auxiliary_property
          (V i).ρ (RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep (V i))
          (h_all_real i))

end RepresentationTheory.InvolutionRankSum

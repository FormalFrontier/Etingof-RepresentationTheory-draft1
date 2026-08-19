/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroupRepresentations.Auxiliary
import RepresentationTheory.OddOrder.CharacterSums
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.OddOrderAuxiliary

section

variable (G : Type*) [Group G] [Fintype G] [Nontrivial G]

/-- Establishes the existence of a simple complex representation of a nontrivial finite odd-order group with nontrivial action and an auxiliary condition. -/
theorem oddCardinality_exists_auxiliarySimpleRepresentation
    (hodd : Odd (Fintype.card G)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V)
      (ρ : Representation ℂ G V),
      IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule ∧
      (∃ g, ρ g ≠ 1) ∧
      ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  let D := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
    (k := ℂ) (G := G)
  obtain ⟨j, g₀, hj⟩ : ∃ (j : Fin D.count) (g : G), (D.coordinateRepresentation j) g ≠ 1 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
    have hmat : ∀ j : Fin D.count, D.matrixBlockHom j (MonoidAlgebra.of ℂ G g₀) = 1 := by
      intro j
      have hdef : (D.coordinateRepresentation j) g₀ =
          Matrix.mulVecLin (D.matrixBlockHom j (MonoidAlgebra.of ℂ G g₀)) := rfl
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_one, ← hdef, h j g₀]
      rfl
    have hprod : D.groupAlgebraEquivMatrix (MonoidAlgebra.of ℂ G g₀) = 1 := by
      funext i
      rw [Pi.one_apply]
      have := hmat i
      simpa [RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.matrixBlockHom,
        Pi.evalRingHom] using this
    have hof : MonoidAlgebra.of ℂ G g₀ = 1 := by
      apply D.groupAlgebraEquivMatrix.injective
      rw [hprod, map_one]
    exact hg₀ (MonoidAlgebra.of_injective
      (hof.trans (map_one (MonoidAlgebra.of ℂ G)).symm))
  haveI : NeZero (D.dimension j) := D.dimension_neZero j
  refine ⟨Fin (D.dimension j) → ℂ, inferInstance, inferInstance, inferInstance,
    D.coordinateRepresentation j, D.isSimpleModule_coordinateRepresentation j, ⟨g₀, hj⟩, ?_⟩
  exact RepresentationTheory.OddOrder.CharacterSums.auxiliary_not_of_odd_card_of_simple_of_nontrivial
    hodd (D.coordinateRepresentation j) (D.isSimpleModule_coordinateRepresentation j) ⟨g₀, hj⟩

end

end RepresentationTheory.OddOrderAuxiliary

/--
A nontrivial finite group of odd cardinality has a simple complex representation with nontrivial
action that does not satisfy the displayed auxiliary property.
-/
alias _root_.RepresentationTheory.OddOrderAuxiliary.oddCardinality_exists_simpleRepresentation_not_auxiliaryProperty := _root_.RepresentationTheory.OddOrderAuxiliary.oddCardinality_exists_auxiliarySimpleRepresentation

attribute [source_ref "Chapter5/Exercise5.1.7" (role := primary)] _root_.RepresentationTheory.OddOrderAuxiliary.oddCardinality_exists_simpleRepresentation_not_auxiliaryProperty

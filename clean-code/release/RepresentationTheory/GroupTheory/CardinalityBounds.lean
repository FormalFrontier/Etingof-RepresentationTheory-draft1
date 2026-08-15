/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GroupTheory.ConjugacyClassCardinalityBounds
import RepresentationTheory.ConjugacyClassCardinalityBounds
import RepresentationTheory.Alignment.Attribute

open RepresentationTheory.AuxiliaryDecompositionData
  RepresentationTheory.ConjugacyClassCardinalityBounds

namespace RepresentationTheory.GroupTheory.CardinalityBounds

universe u v

/-- For an algebraically closed field in which the finite group's order maps to zero, the auxiliary type has smaller cardinality than its conjugacy-class type. -/
@[source_ref "Chapter4/Exercise4.2.3" (role := supporting)]
theorem auxiliaryCard_lt_conjClasses_of_card_cast_eq_zero_algClosed
    (K : Type u) (G : Type v) [Field K] [IsAlgClosed K] [Group G] [Fintype G]
    (hcard : (Fintype.card G : K) = 0) :
    Nat.card (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter K G) <
      Nat.card (ConjClasses G) := by
  classical
  obtain ⟨D, hD⟩ :=
    _root_.RepresentationTheory.AuxiliaryDecompositionData.exists_auxiliaryDecompositionData_card_eq_count
      K G
  rw [_root_.RepresentationTheory.SimpleRepresentationModules.natCard_auxiliaryTypes_eq K G,
    hD]
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra K G) (D.indexedType i) :=
    fun i => D.isSimpleModule_module i
  have hlt :=
    _root_.RepresentationTheory.ConjugacyClassCardinalityBounds.card_lt_card_conjClasses_of_linearIndependent_of_card_eq_zero
      (S := fun i => D.indexedType i) hcard
      (_root_.RepresentationTheory.GroupTheory.ConjugacyClassCardinalityBounds.auxiliaryFamily_linearIndependent
        D)
  simpa using hlt

/-- If the finite group's order maps to zero in the field, the auxiliary type has smaller cardinality than its conjugacy-class type. -/
@[source_ref "Chapter4/Exercise4.2.3" (role := primary)]
theorem auxiliaryCard_lt_conjClasses_of_card_cast_eq_zero
    (k G : Type u) [Field k] [Group G] [Fintype G]
    (h : (Fintype.card G : k) = 0) :
    Nat.card (RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter k G) <
      Nat.card (ConjClasses G) := by
  have hK : (Fintype.card G : AlgebraicClosure k) = 0 := by
    rw [← map_natCast (algebraMap k (AlgebraicClosure k)) (Fintype.card G), h, map_zero]
  exact lt_of_le_of_lt
    (_root_.RepresentationTheory.GroupTheory.ConjugacyClassCardinalityBounds.auxiliaryCard_le_auxiliaryCard_of_algebra
      k (AlgebraicClosure k) G)
    (auxiliaryCard_lt_conjClasses_of_card_cast_eq_zero_algClosed
      (AlgebraicClosure k) G hK)

end RepresentationTheory.GroupTheory.CardinalityBounds

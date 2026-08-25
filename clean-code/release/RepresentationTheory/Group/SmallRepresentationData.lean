/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorSquareSpectralDecomposition
import RepresentationTheory.Group.OuterAutomorphismTwist
import RepresentationTheory.QuotientPermutationRepresentation
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Group.SmallRepresentationData

open _root_.RepresentationTheory.PermutationActionRepresentations

/-- The quaternion group with parameter two has five conjugacy classes. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem card_conjClasses_quaternionGroup_two :
    Fintype.card (ConjClasses (QuaternionGroup 2)) = 5 := by
  decide

/-- The quaternion group with parameter two has cardinality eight. -/
theorem card_quaternionGroup_two :
    Fintype.card (QuaternionGroup 2) = 8 := by
  rw [QuaternionGroup.card]

/-- A family of five finite-dimensional complex representations of the quaternion group with
parameter two. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
noncomputable def quaternionGroupRepFamily :
    Fin 5 → FDRep ℂ (QuaternionGroup 2) :=
  _root_.RepresentationTheory.QuaternionGroupTwo.irreducibleRepresentations

/-- Every representation in the quaternion-group family is simple. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem simple_quaternionGroupRepFamily (i : Fin 5) :
    CategoryTheory.Simple (quaternionGroupRepFamily i) :=
  _root_.RepresentationTheory.QuaternionGroupTwo.irreducibleRepresentations_simple i

/-- The character of an indexed quaternion-group representation at an indexed group element
equals the displayed value. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem character_quaternionGroupRepFamily_apply (i j : Fin 5) :
    (quaternionGroupRepFamily i).character
        (_root_.RepresentationTheory.QuaternionGroupTwo.selectedQuaternionGroupElements j) =
      _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex
        (_root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryCharacterTable i j) :=
  _root_.RepresentationTheory.QuaternionGroupTwo.irreducibleRepresentations_character i j

/-- Representations at distinct indices in the quaternion-group family are not isomorphic. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem quaternionGroupRepFamily_not_iso_of_ne (i j : Fin 5) (hij : i ≠ j) :
    ¬ Nonempty (quaternionGroupRepFamily i ≅ quaternionGroupRepFamily j) :=
  _root_.RepresentationTheory.QuaternionGroupTwo.irreducibleRepresentations_pairwise_nonisomorphic
    i j hij

set_option maxRecDepth 4000 in
/-- The permutation group on four letters has five conjugacy classes. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem card_conjClasses_perm_fin4 :
    Fintype.card (ConjClasses (Equiv.Perm (Fin 4))) = 5 := by
  decide

/-- The permutation group on four letters has cardinality twenty-four. -/
theorem card_perm_fin4 :
    Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Fintype.card_perm, Fintype.card_fin]; decide

/-- A family of five finite-dimensional complex representations of the permutation group on four
letters. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
noncomputable def permFin4RepFamily :
    Fin 5 → FDRep ℂ (Equiv.Perm (Fin 4)) :=
  _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations

/-- Every representation in the four-letter permutation-group family is simple. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem simple_permFin4RepFamily (i : Fin 5) :
    CategoryTheory.Simple (permFin4RepFamily i) :=
  _root_.RepresentationTheory.PermutationActionRepresentations.irreducibleRepresentations_simple i

/-- The character of an indexed four-letter permutation-group representation at an indexed group
element equals the displayed value. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem character_permFin4RepFamily_apply (i j : Fin 5) :
    (permFin4RepFamily i).character
        (_root_.RepresentationTheory.PermutationActionRepresentations.auxiliaryElementFamily j) =
      _root_.RepresentationTheory.QuaternionGroupTwo.auxiliaryTypeToComplex
        (auxiliaryCharacterTable i j) :=
  irreducibleRepresentations_character_aux i j

/-- Representations at distinct indices in the four-letter permutation-group family are not
isomorphic. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem permFin4RepFamily_not_iso_of_ne (i j : Fin 5) (hij : i ≠ j) :
    ¬ Nonempty (permFin4RepFamily i ≅ permFin4RepFamily j) :=
  irreducibleRepresentations_pairwise_nonisomorphic i j hij

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The alternating group on five letters has five conjugacy classes. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem card_conjClasses_alternatingGroup_fin5 :
    Fintype.card (ConjClasses (alternatingGroup (Fin 5))) = 5 := by
  decide

/-- The alternating group on five letters has cardinality sixty. -/
theorem card_alternatingGroup_fin5 :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide

/-- A family of five finite-dimensional complex representations of the alternating group on five
letters. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
noncomputable def alternatingGroupFin5RepFamily :
    Fin 5 → FDRep ℂ (alternatingGroup (Fin 5)) :=
  _root_.RepresentationTheory.TensorSquareSpectralDecomposition.indexedSimpleRepresentations

end RepresentationTheory.Group.SmallRepresentationData

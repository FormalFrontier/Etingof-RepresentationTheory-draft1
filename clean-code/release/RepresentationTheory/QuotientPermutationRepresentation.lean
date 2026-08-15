/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.PermutationDegreeThree
import RepresentationTheory.PermutationDegreeFour
import RepresentationTheory.PermutationActionRepresentations
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.Alignment.Attribute

/-! # Quotient Permutation Representation -/


namespace RepresentationTheory.QuotientPermutationRepresentation

open Equiv Function

noncomputable section

/-- A three-entry family of elements in the source group. -/
def sourceGroupElementFamily : Fin 3 → _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in

/-- A distinguished subgroup of the source group. -/
def distinguishedSubgroup : Subgroup _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType where
  carrier := {g | g = 1 ∨ ∃ i, g = sourceGroupElementFamily i}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide
  inv_mem' := by
    intro a ha
    revert a
    decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in

/-- The kernel of the selected monoid homomorphism is the displayed subgroup. -/
theorem selectedMonoidHom_ker : _root_.RepresentationTheory.PermutationDegreeFour.inducedPermutationHom.ker = distinguishedSubgroup := by
  ext g
  change _root_.RepresentationTheory.PermutationDegreeFour.inducedPermutationHom g = 1 ↔ (g = 1 ∨ ∃ i, g = sourceGroupElementFamily i)
  revert g
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in

/-- The selected monoid homomorphism is onto. -/
theorem selectedMonoidHom_surjective : Surjective _root_.RepresentationTheory.PermutationDegreeFour.inducedPermutationHom := by
  intro g
  revert g
  decide

/-- The distinguished subgroup is normal. -/
instance distinguishedSubgroup_normal : distinguishedSubgroup.Normal := by
  rw [← selectedMonoidHom_ker]
  infer_instance

/-- The quotient by the distinguished subgroup is multiplicatively equivalent to permutations of three points. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
noncomputable def quotientEquivPermFinThree : _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType ⧸ distinguishedSubgroup ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq selectedMonoidHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _root_.RepresentationTheory.PermutationDegreeFour.inducedPermutationHom selectedMonoidHom_surjective)

/-- A finite-dimensional complex representation of the source group. -/
def sourceRepresentation : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType :=
  (Action.res (FGModuleCat ℂ) _root_.RepresentationTheory.PermutationDegreeFour.inducedPermutationHom).obj _root_.RepresentationTheory.PermutationDegreeThree.reducedCoordinateRepresentation

/-- Its character equals the target representation's character after the selected monoid homomorphism. -/
@[simp]
theorem sourceRepresentation_character (g : _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) :
    sourceRepresentation.character g = _root_.RepresentationTheory.PermutationDegreeThree.reducedCoordinateRepresentation.character (_root_.RepresentationTheory.PermutationDegreeFour.inducedPermutationHom g) :=
  rfl

/-- Composing the first displayed function with the selected monoid homomorphism gives the second displayed function. -/
theorem auxiliaryFunction_comp_selectedMonoidHom (g : _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) :
    _root_.RepresentationTheory.PermutationDegreeThree.fixedPointCount (_root_.RepresentationTheory.PermutationDegreeFour.inducedPermutationHom g) = _root_.RepresentationTheory.PermutationDegreeFour.inducedFixedPointCount g :=
  rfl

/-- The source representation and a comparison representation have identical characters. -/
theorem sourceRepresentation_character_eq_comparison :
    sourceRepresentation.character = _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation.character := by
  funext g
  rw [sourceRepresentation_character, _root_.RepresentationTheory.PermutationDegreeThree.character_reducedCoordinateRepresentation,
    _root_.RepresentationTheory.PermutationDegreeFour.character_inducedReducedCoordinateRepresentation, auxiliaryFunction_comp_selectedMonoidHom]

/-- The source representation is isomorphic to a comparison representation. -/
theorem sourceRepresentation_iso_comparison :
    Nonempty (sourceRepresentation ≅ _root_.RepresentationTheory.PermutationDegreeFour.inducedReducedCoordinateRepresentation) :=
  _root_.RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _ sourceRepresentation_character_eq_comparison

end

end RepresentationTheory.QuotientPermutationRepresentation

namespace RepresentationTheory.QuotientPermutationRepresentation

open Equiv

noncomputable section

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in

/-- The two displayed functions into Fin 3 agree pointwise. -/
theorem finThreeFunctions_eq (g : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) (i : Fin 3) :
    _root_.RepresentationTheory.PermutationActionRepresentations.actOnFinThree g i = _root_.RepresentationTheory.PermutationDegreeFour.inducedIndexMap g i := by
  revert g i
  decide

/-- The two displayed functions agree pointwise. -/
theorem auxiliaryFunctions_eq (g : _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) :
    _root_.RepresentationTheory.PermutationActionRepresentations.fixedPointCount (G := _root_.RepresentationTheory.PermutationActionRepresentations.AuxiliaryType) (α := Fin 3) g = _root_.RepresentationTheory.PermutationDegreeFour.inducedFixedPointCount g := by
  unfold _root_.RepresentationTheory.PermutationActionRepresentations.fixedPointCount _root_.RepresentationTheory.PermutationDegreeFour.inducedFixedPointCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change _root_.RepresentationTheory.PermutationActionRepresentations.actOnFinThree g i = i ↔ _root_.RepresentationTheory.PermutationDegreeFour.inducedIndexMap g i = i
  rw [finThreeFunctions_eq]

/-- A comparison representation has the same character as the source representation. -/
theorem comparisonRepresentation_character_eq_source :
    _root_.RepresentationTheory.PermutationActionRepresentations.selectedRepresentationTwo.character = _root_.RepresentationTheory.QuotientPermutationRepresentation.sourceRepresentation.character := by
  funext g
  rw [_root_.RepresentationTheory.PermutationActionRepresentations.selectedRepresentationTwo, _root_.RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general,
    _root_.RepresentationTheory.QuotientPermutationRepresentation.sourceRepresentation_character,
    _root_.RepresentationTheory.PermutationDegreeThree.character_reducedCoordinateRepresentation, auxiliaryFunctions_eq,
    _root_.RepresentationTheory.QuotientPermutationRepresentation.auxiliaryFunction_comp_selectedMonoidHom]

/-- A comparison representation is isomorphic to the source representation. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem comparisonRepresentation_iso_source :
    Nonempty (_root_.RepresentationTheory.PermutationActionRepresentations.selectedRepresentationTwo ≅ _root_.RepresentationTheory.QuotientPermutationRepresentation.sourceRepresentation) :=
  _root_.RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _ comparisonRepresentation_character_eq_source

end

end RepresentationTheory.QuotientPermutationRepresentation

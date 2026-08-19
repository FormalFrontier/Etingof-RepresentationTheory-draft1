/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorSquareSpectralDecomposition
import RepresentationTheory.FiniteGroups.CharacterRigidity
import RepresentationTheory.Alignment.Attribute

/-!
# Outer automorphism twists of permutation-subgroup representations

This module constructs the automorphism induced by conjugating a permutation subgroup on five
letters by a selected transposition. It records the induced action on conjugacy-class indices and
the resulting exchange of two finite-dimensional complex representations.
-/

open Equiv

open RepresentationTheory.Group.PermutationSubgroupData
  (conjugacyClassIndex conjugacyClassRepresentative exists_conj_classRepresentative indexedTable
    permutationSubgroupFin5)
open RepresentationTheory.TensorSquareSpectralDecomposition
  (auxiliaryRepresentationOne auxiliaryRepresentationTwo character_auxiliaryRepresentationOne
    character_auxiliaryRepresentationTwo)

namespace RepresentationTheory.Group.OuterAutomorphismTwist

noncomputable section

/-- A selected permutation of five letters. -/
def conjugatingPermutation : Equiv.Perm (Fin 5) := Equiv.swap 0 1

/-- A multiplicative automorphism of the displayed permutation subgroup induced by conjugation
with a selected permutation. -/
def conjugationMulAut : MulAut permutationSubgroupFin5 :=
  MulAut.conjNormal conjugatingPermutation

/-- The underlying permutation of the automorphism applied to a group element is its conjugate by
the selected permutation. -/
@[simp]
theorem coe_conjugationMulAut_apply (g : permutationSubgroupFin5) :
    (conjugationMulAut g : Equiv.Perm (Fin 5)) =
      conjugatingPermutation * (g : Equiv.Perm (Fin 5)) * conjugatingPermutation⁻¹ :=
  rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- Exhaustively checking the explicit 60-element classifier exceeds the default limit.
/-- Applying the automorphism changes the displayed five-valued index according to the permutation
fixing zero, one, and two and swapping three with four. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem index_conjugationMulAut (g : permutationSubgroupFin5) :
    conjugacyClassIndex (conjugationMulAut g) =
      ![0, 1, 2, 4, 3] (conjugacyClassIndex g) := by
  revert g
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- Exhaustively checking all possible inner conjugators exceeds the default limit.
/-- The displayed multiplicative automorphism is not conjugation by any element of the subgroup. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
theorem conjugationMulAut_not_inner :
    ¬ ∃ a : permutationSubgroupFin5, conjugationMulAut = MulAut.conj a := by
  rintro ⟨a, ha⟩
  have h := congrArg
    (fun f : MulAut permutationSubgroupFin5 =>
      conjugacyClassIndex (f (conjugacyClassRepresentative 3))) ha
  have hinner :
      conjugacyClassIndex (MulAut.conj a (conjugacyClassRepresentative 3)) = 3 := by
    revert a
    decide
  have hrep : conjugacyClassIndex (conjugacyClassRepresentative 3) = 3 := by
    decide
  rw [index_conjugationMulAut, hrep, hinner] at h
  exact (by decide : (![(0 : Fin 5), 1, 2, 4, 3] (3 : Fin 5)) ≠ 3) h

/-- A finite-dimensional complex representation of the displayed permutation subgroup. -/
def twistedRepresentation : FDRep ℂ permutationSubgroupFin5 :=
  FDRep.of (auxiliaryRepresentationTwo.ρ.comp conjugationMulAut.toMonoidHom)

/-- The character of the displayed representation at a group element equals the character of the
comparison representation at the image of that element under the automorphism. -/
@[simp]
theorem character_twistedRepresentation_apply (g : permutationSubgroupFin5) :
    twistedRepresentation.character g =
      auxiliaryRepresentationTwo.character (conjugationMulAut g) :=
  rfl

private theorem chiA5_outer_swap (j : Fin 5) :
    indexedTable 1 (![0, 1, 2, 4, 3] j) = indexedTable 2 j := by
  fin_cases j <;> rfl

private theorem character_eq_classRep
    (V : FDRep ℂ permutationSubgroupFin5) (g : permutationSubgroupFin5) :
    V.character g = V.character (conjugacyClassRepresentative (conjugacyClassIndex g)) := by
  obtain ⟨c, hc⟩ := exists_conj_classRepresentative g
  calc
    V.character g =
        V.character (c * conjugacyClassRepresentative (conjugacyClassIndex g) * c⁻¹) :=
      congrArg V.character hc.symm
    _ = V.character (conjugacyClassRepresentative (conjugacyClassIndex g)) :=
      FDRep.char_conj V _ _

/-- The displayed representation and comparison representation have equal characters. -/
theorem character_twistedRepresentation_eq :
    twistedRepresentation.character = auxiliaryRepresentationOne.character := by
  funext g
  rw [character_twistedRepresentation_apply, character_eq_classRep,
    character_auxiliaryRepresentationTwo, index_conjugationMulAut, chiA5_outer_swap,
    ← character_auxiliaryRepresentationOne,
    ← character_eq_classRep auxiliaryRepresentationOne]

/-- The displayed representation is isomorphic to the comparison representation. -/
@[source_ref "Chapter4/Example4.8.1" (role := primary)]
theorem twistedRepresentation_iso :
    Nonempty (twistedRepresentation ≅ auxiliaryRepresentationOne) :=
  RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq _ _
    character_twistedRepresentation_eq

end

end RepresentationTheory.Group.OuterAutomorphismTwist

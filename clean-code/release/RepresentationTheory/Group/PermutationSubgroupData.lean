/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.PermutationActionRepresentations

namespace RepresentationTheory.Group.PermutationSubgroupData

open RepresentationTheory.QuaternionGroupTwo.AuxiliaryType

/-- A family of five rational values. -/
def rationalWeights : Fin 5 → ℚ := ![1, 20, 15, 12, 12]

/-- A five-by-five family of values in the displayed auxiliary type. -/
def indexedTable : Fin 5 → Fin 5 → RepresentationTheory.QuaternionGroupTwo.AuxiliaryType :=
  ![![1,  1,  1,  1,           1          ],
    ![3,  0, -1, ⟨1/2, 1/2⟩,  ⟨1/2, -1/2⟩ ],
    ![3,  0, -1, ⟨1/2, -1/2⟩, ⟨1/2, 1/2⟩  ],
    ![4,  1,  0, -1,          -1          ],
    ![5, -1,  1,  0,           0          ]]

/-- The displayed indexed expression is one when its indices agree and zero otherwise. -/
theorem indexedExpression_eq_ite (i j : Fin 5) :
    RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.auxiliaryCombination 60 rationalWeights
      (indexedTable i) (indexedTable j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    (first | rw [if_pos rfl] | rw [if_neg (by decide)]) <;>
    apply RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ext <;>
    norm_num [RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.auxiliaryCombination,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.sum_fin_five, rationalWeights,
      indexedTable, RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mk_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.add_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mul_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.mul_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.neg_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.zero_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.one_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofNat_im,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofRat_re,
      RepresentationTheory.QuaternionGroupTwo.AuxiliaryType.ofRat_im, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]

open Equiv CategoryTheory

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- A subgroup of the permutation group on five letters. -/
abbrev permutationSubgroupFin5 := alternatingGroup (Fin 5)

/-- The displayed subgroup of the permutation group on five letters has cardinality sixty. -/
lemma card_permutationSubgroupFin5 : Nat.card permutationSubgroupFin5 = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

/-- Selects an element of the displayed permutation subgroup for each of five indices. -/
def conjugacyClassRepresentative : Fin 5 → permutationSubgroupFin5 :=
  ![1,
    ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨(Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1) ^ 2,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩]

/-- Assigns one of five indices to each element of the displayed permutation subgroup. -/
def conjugacyClassIndex (g : permutationSubgroupFin5) : Fin 5 :=
  if RepresentationTheory.PermutationActionRepresentations.fixedPointCount
      (G := permutationSubgroupFin5) (α := Fin 5) g = 5 then 0
  else if RepresentationTheory.PermutationActionRepresentations.fixedPointCount
      (G := permutationSubgroupFin5) (α := Fin 5) g = 2 then 1
  else if RepresentationTheory.PermutationActionRepresentations.fixedPointCount
      (G := permutationSubgroupFin5) (α := Fin 5) g = 1 then 2
  else if ∃ c : permutationSubgroupFin5,
      c * conjugacyClassRepresentative 3 * c⁻¹ = g then 3
  else 4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Every element is conjugate to the representative selected by its conjugacy-class index. -/
lemma exists_conj_classRepresentative (g : permutationSubgroupFin5) :
    ∃ c : permutationSubgroupFin5,
      c * conjugacyClassRepresentative (conjugacyClassIndex g) * c⁻¹ = g := by
  revert g; decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The five fibers of the conjugacy-class index have cardinalities one, twenty, fifteen, twelve, and twelve. -/
lemma card_fiber_conjugacyClassIndex (j : Fin 5) :
    (Finset.univ.filter fun g => conjugacyClassIndex g = j).card =
      ![1, 20, 15, 12, 12] j := by
  revert j; decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Each selected representative is conjugate to its inverse. -/
lemma classRepresentative_isConj_inv (j : Fin 5) :
    ∃ c : permutationSubgroupFin5,
      c * conjugacyClassRepresentative j * c⁻¹ = (conjugacyClassRepresentative j)⁻¹ := by
  revert j; decide

end

end RepresentationTheory.Group.PermutationSubgroupData

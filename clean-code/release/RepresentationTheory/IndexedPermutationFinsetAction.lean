/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Group.PermutationSubgroupData
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.IndexedPermutationFinsetAction

open RepresentationTheory.QuaternionGroupTwo.AuxiliaryType

open Equiv CategoryTheory

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- Summing a function of the displayed natural-number statistic over the group equals the weighted sum over five indexed elements. -/
lemma sum_auxiliaryStatistic_eq_weightedIndexedSum
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [MulAction RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 α]
    (f : ℕ → ℤ) :
    ∑ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5,
        f (RepresentationTheory.PermutationActionRepresentations.fixedPointCount
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := α) g) =
      ∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℤ) *
        f (RepresentationTheory.PermutationActionRepresentations.fixedPointCount
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := α)
          (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)) := by
  rw [← Finset.sum_fiberwise Finset.univ
    (fun g => RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g)
    (fun g => f (RepresentationTheory.PermutationActionRepresentations.fixedPointCount
      (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
      (α := α) g))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∀ g ∈ Finset.univ.filter
      (fun g => RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g = j),
      f (RepresentationTheory.PermutationActionRepresentations.fixedPointCount
        (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
        (α := α) g) =
        f (RepresentationTheory.PermutationActionRepresentations.fixedPointCount
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := α)
          (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j)) := by
    intro g hg
    have hj : RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassIndex g = j :=
      (Finset.mem_filter.mp hg).2
    obtain ⟨c, hc⟩ :=
      RepresentationTheory.Group.PermutationSubgroupData.exists_conj_classRepresentative g
    conv_lhs => rw [← hc]
    rw [RepresentationTheory.PermutationActionRepresentations.fixedPointCount_conj, hj]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const,
    RepresentationTheory.Group.PermutationSubgroupData.card_fiber_conjugacyClassIndex j,
    nsmul_eq_mul]

/-- A finite-dimensional complex representation with constant character one. -/
def trivialRepresentation :
    FDRep ℂ RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 :=
  FDRep.of (RepresentationTheory.PermutationActionRepresentations.representationOfUnitsCharacter
    (1 : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 →* ℂˣ))

/-- The character of the trivial representation is one on every group element. -/
lemma character_trivialRepresentation
    (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    trivialRepresentation.character g = 1 := by
  rw [trivialRepresentation,
    RepresentationTheory.PermutationActionRepresentations.representationOfUnitsCharacter_character]; simp

/-- The trivial representation is simple. -/
lemma simple_trivialRepresentation : Simple trivialRepresentation :=
  RepresentationTheory.PermutationActionRepresentations.representationOfUnitsCharacter_simple _

/-- An auxiliary finite-dimensional complex representation. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
def auxiliaryRepresentationOne :
    FDRep ℂ RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 :=
  RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation
    (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 5)

/-- The first auxiliary representation's character is the displayed natural-number statistic minus one. -/
lemma character_auxiliaryRepresentationOne
    (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    auxiliaryRepresentationOne.character g =
      (RepresentationTheory.PermutationActionRepresentations.fixedPointCount
        (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
        (α := Fin 5) g : ℂ) - 1 := by
  rw [auxiliaryRepresentationOne,
    RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The first auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationOne : Simple auxiliaryRepresentationOne := by
  rw [auxiliaryRepresentationOne, FDRep.simple_iff_char_is_norm_one]
  have hterm :
      ∀ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5,
      (RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := Fin 5)).character g *
        (RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := Fin 5)).character g⁻¹ =
      ((((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
        (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
        (α := Fin 5) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general,
      RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general,
      RepresentationTheory.PermutationActionRepresentations.fixedPointCount_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum :
      ∑ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5,
        (((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := Fin 5) g : ℤ) - 1) ^ 2) = 60 :=
    calc
      ∑ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5,
          (((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
            (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
            (α := Fin 5) g : ℤ) - 1) ^ 2) =
        ∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℤ) *
          (((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
            (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
            (α := Fin 5)
            (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) : ℤ) -
            1) ^ 2) :=
        sum_auxiliaryStatistic_eq_weightedIndexedSum (α := Fin 5)
          (fun n => ((n : ℤ) - 1) ^ 2)
      _ = 60 := by decide
  rw [hsum, RepresentationTheory.Group.PermutationSubgroupData.card_permutationSubgroupFin5]; norm_num

/-- An auxiliary permutation of five elements indexed by three five-valued arguments. -/
def auxiliaryTriplePermutation (a b c : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 c * Equiv.swap 0 b * Equiv.swap 0 a * Equiv.swap 0 1

/-- An auxiliary family of six permutations of five elements. -/
def auxiliaryIndexedPermutations : Fin 6 → Equiv.Perm (Fin 5) :=
  ![auxiliaryTriplePermutation 2 3 4, auxiliaryTriplePermutation 2 4 3,
    auxiliaryTriplePermutation 3 2 4, auxiliaryTriplePermutation 3 4 2,
    auxiliaryTriplePermutation 4 2 3, auxiliaryTriplePermutation 4 3 2]

/-- A family of six finite sets of permutations of five elements. -/
def indexedPermutationFinsets (i : Fin 6) : Finset (Equiv.Perm (Fin 5)) :=
  {auxiliaryIndexedPermutations i, (auxiliaryIndexedPermutations i) ^ 2,
    (auxiliaryIndexedPermutations i) ^ 3, (auxiliaryIndexedPermutations i) ^ 4}

/-- The action of a group element on permutations of five elements. -/
def permutationActionMap
    (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
    (x : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 5) :=
  (g : Equiv.Perm (Fin 5)) * x * (g : Equiv.Perm (Fin 5))⁻¹

/-- The identity group element induces the identity map on permutations. -/
lemma permutationActionMap_one : permutationActionMap 1 = id := by
  funext x; simp [permutationActionMap]

/-- Successive permutation action maps agree with the action map of the product. -/
lemma permutationActionMap_mul
    (g h : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
    (x : Equiv.Perm (Fin 5)) :
    permutationActionMap g (permutationActionMap h x) = permutationActionMap (g * h) x := by
  simp only [permutationActionMap, Subgroup.coe_mul]; group

/-- The action of a group element on the six indices of the permutation-finset family. -/
def permutationFinsetIndexAction
    (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
    (i : Fin 6) : Fin 6 :=
  if indexedPermutationFinsets 0 = (indexedPermutationFinsets i).image (permutationActionMap g) then 0
  else if indexedPermutationFinsets 1 =
      (indexedPermutationFinsets i).image (permutationActionMap g) then 1
  else if indexedPermutationFinsets 2 =
      (indexedPermutationFinsets i).image (permutationActionMap g) then 2
  else if indexedPermutationFinsets 3 =
      (indexedPermutationFinsets i).image (permutationActionMap g) then 3
  else if indexedPermutationFinsets 4 =
      (indexedPermutationFinsets i).image (permutationActionMap g) then 4 else 5

/-- Distinct indices determine distinct finite sets in the indexed permutation family. -/
lemma indexedPermutationFinsets_injective : Function.Injective indexedPermutationFinsets := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Acting on an index corresponds to taking the image of its permutation finset under the permutation action map. -/
lemma indexedPermutationFinsets_action
    (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
    (i : Fin 6) :
    indexedPermutationFinsets (permutationFinsetIndexAction g i) =
      (indexedPermutationFinsets i).image (permutationActionMap g) := by
  revert g i; decide

/-- The multiplicative action on six indices induced by the permutation-finset action. -/
instance permutationFinsetIndexMulAction :
    MulAction RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 (Fin 6) where
  smul := permutationFinsetIndexAction
  one_smul i := indexedPermutationFinsets_injective (by
    change indexedPermutationFinsets (permutationFinsetIndexAction 1 i) = indexedPermutationFinsets i
    rw [indexedPermutationFinsets_action, permutationActionMap_one, Finset.image_id])
  mul_smul g h i := indexedPermutationFinsets_injective (by
    have hcomp : permutationActionMap g ∘ permutationActionMap h =
        permutationActionMap (g * h) := by
      funext x; exact permutationActionMap_mul g h x
    change indexedPermutationFinsets (permutationFinsetIndexAction (g * h) i) =
      indexedPermutationFinsets (permutationFinsetIndexAction g (permutationFinsetIndexAction h i))
    rw [indexedPermutationFinsets_action, indexedPermutationFinsets_action,
      indexedPermutationFinsets_action, Finset.image_image, hcomp])

/-- An auxiliary finite-dimensional complex representation. -/
@[source_ref "Chapter4/Example4.8.1" (role := supporting)]
def auxiliaryRepresentationTwo :
    FDRep ℂ RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5 :=
  RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation
    (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) (α := Fin 6)

/-- The second auxiliary representation's character is the displayed natural-number statistic minus one. -/
lemma character_auxiliaryRepresentationTwo
    (g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5) :
    auxiliaryRepresentationTwo.character g =
      (RepresentationTheory.PermutationActionRepresentations.fixedPointCount
        (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
        (α := Fin 6) g : ℂ) - 1 := by
  rw [auxiliaryRepresentationTwo,
    RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The second auxiliary representation is simple. -/
lemma simple_auxiliaryRepresentationTwo : Simple auxiliaryRepresentationTwo := by
  rw [auxiliaryRepresentationTwo, FDRep.simple_iff_char_is_norm_one]
  have hterm :
      ∀ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5,
      (RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := Fin 6)).character g *
        (RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := Fin 6)).character g⁻¹ =
      ((((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
        (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
        (α := Fin 6) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general,
      RepresentationTheory.PermutationActionRepresentations.reducedPermutationRepresentation_character_general,
      RepresentationTheory.PermutationActionRepresentations.fixedPointCount_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum :
      ∑ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5,
        (((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
          (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
          (α := Fin 6) g : ℤ) - 1) ^ 2) = 60 :=
    calc
      ∑ g : RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5,
          (((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
            (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
            (α := Fin 6) g : ℤ) - 1) ^ 2) =
        ∑ j : Fin 5, ((![1, 20, 15, 12, 12] j : ℕ) : ℤ) *
          (((RepresentationTheory.PermutationActionRepresentations.fixedPointCount
            (G := RepresentationTheory.Group.PermutationSubgroupData.permutationSubgroupFin5)
            (α := Fin 6)
            (RepresentationTheory.Group.PermutationSubgroupData.conjugacyClassRepresentative j) : ℤ) -
            1) ^ 2) :=
        sum_auxiliaryStatistic_eq_weightedIndexedSum (α := Fin 6)
          (fun n => ((n : ℤ) - 1) ^ 2)
      _ = 60 := by decide
  rw [hsum, RepresentationTheory.Group.PermutationSubgroupData.card_permutationSubgroupFin5]; norm_num

end

end RepresentationTheory.IndexedPermutationFinsetAction

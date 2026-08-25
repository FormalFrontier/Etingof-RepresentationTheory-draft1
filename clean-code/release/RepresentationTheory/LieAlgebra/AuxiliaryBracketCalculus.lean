/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.ExplicitConstructions
import Mathlib.Tactic.FieldSimp
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary Bracket Calculus -/

namespace RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus

open RepresentationTheory.LieAlgebra.ExplicitConstructions

variable (k : Type*) [CommRing k]

/-- The natural-number iterate of the displayed bracket operator on the auxiliary Lie algebra. -/
noncomputable def iterateBracket (j : ℕ) (u : AuxiliaryType k 4) : AuxiliaryType k 4 := (fun v => ⁅distinguishedElement_aux8 k 4, v⁆)^[j] u

/-- The zeroth iterate is the identity. -/
@[simp] theorem iterateBracket_zero (u : AuxiliaryType k 4) : iterateBracket k 0 u = u := rfl

/-- The first iterate is bracket with the displayed distinguished element. -/
theorem iterateBracket_one (u : AuxiliaryType k 4) : iterateBracket k 1 u = ⁅distinguishedElement_aux8 k 4, u⁆ := rfl

/-- The second iterate is the displayed double bracket. -/
theorem iterateBracket_two (u : AuxiliaryType k 4) : iterateBracket k 2 u = ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, u⁆⁆ := rfl

/-- The third iterate is the displayed threefold nested bracket. -/
theorem iterateBracket_three (u : AuxiliaryType k 4) : iterateBracket k 3 u = ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, u⁆⁆⁆ := rfl

/-- The fourth iterate is the displayed fourfold nested bracket. -/
theorem iterateBracket_four (u : AuxiliaryType k 4) :
    iterateBracket k 4 u = ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, u⁆⁆⁆⁆ := rfl

/-- The fifth iterate is the displayed fivefold nested bracket. -/
theorem iterateBracket_five (u : AuxiliaryType k 4) :
    iterateBracket k 5 u = ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement_aux8 k 4, u⁆⁆⁆⁆⁆ := rfl

/-- The successor iterate is bracket with the distinguished element after the preceding iterate. -/
theorem iterateBracket_succ (j : ℕ) (u : AuxiliaryType k 4) : iterateBracket k (j + 1) u = ⁅distinguishedElement_aux8 k 4, iterateBracket k j u⁆ :=
  Function.iterate_succ_apply' _ _ _

/-- The successor iterate is the preceding iterate applied after one bracket with the distinguished element. -/
theorem iterateBracket_succ_apply (j : ℕ) (u : AuxiliaryType k 4) : iterateBracket k (j + 1) u = iterateBracket k j ⁅distinguishedElement_aux8 k 4, u⁆ := rfl

/-- Iteration by `i + j` equals iteration by `i` after iteration by `j`. -/
theorem iterateBracket_add (i j : ℕ) (u : AuxiliaryType k 4) : iterateBracket k (i + j) u = iterateBracket k i (iterateBracket k j u) :=
  Function.iterate_add_apply _ i j u

/-- One iteration after `j` iterations equals the successor iterate. -/
theorem iterateBracket_one_apply (j : ℕ) (u : AuxiliaryType k 4) : iterateBracket k 1 (iterateBracket k j u) = iterateBracket k (j + 1) u := by
  rw [iterateBracket_one, iterateBracket_succ]

/-- Applying an iterate after one step equals the successor iterate. -/
theorem iterateBracket_apply_one (j : ℕ) (u : AuxiliaryType k 4) : iterateBracket k j (iterateBracket k 1 u) = iterateBracket k (j + 1) u := by
  rw [iterateBracket_one, iterateBracket_succ_apply]

/-- The iterated bracket operator preserves addition. -/
@[simp] theorem iterateBracket_add_apply (j : ℕ) (u v : AuxiliaryType k 4) : iterateBracket k j (u + v) = iterateBracket k j u + iterateBracket k j v := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iterateBracket_succ, iterateBracket_succ, iterateBracket_succ, ih, lie_add]

/-- Every iterate sends zero to zero. -/
@[simp] theorem iterateBracket_zero_apply (j : ℕ) : iterateBracket k j (0 : AuxiliaryType k 4) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iterateBracket_succ, ih, lie_zero]

/-- The iterated bracket operator commutes with negation. -/
@[simp] theorem iterateBracket_neg (j : ℕ) (u : AuxiliaryType k 4) : iterateBracket k j (-u) = -iterateBracket k j u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iterateBracket_succ, iterateBracket_succ, ih, lie_neg]

/-- The iterated bracket operator preserves subtraction. -/
@[simp] theorem iterateBracket_sub (j : ℕ) (u v : AuxiliaryType k 4) : iterateBracket k j (u - v) = iterateBracket k j u - iterateBracket k j v := by
  rw [sub_eq_add_neg, iterateBracket_add_apply, iterateBracket_neg, sub_eq_add_neg]

/-- The iterated bracket operator commutes with scalar multiplication. -/
@[simp] theorem iterateBracket_smul (j : ℕ) (a : k) (u : AuxiliaryType k 4) : iterateBracket k j (a • u) = a • iterateBracket k j u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iterateBracket_succ, iterateBracket_succ, ih, lie_smul]

/-- Iterating the displayed initial element produces the corresponding indexed family element. -/
theorem iterateBracket_initialElement (j : ℕ) : iterateBracket k j (distinguishedElement_aux7 k 4) = distinguishedElement k 4 j := rfl

/-- The displayed nested bracket satisfies the stated difference identity with the next indexed element. -/
theorem bracket_bracket_degree01 (i : ℕ) (u : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 i, ⁅distinguishedElement_aux8 k 4, u⁆⁆ = ⁅distinguishedElement_aux8 k 4, ⁅distinguishedElement k 4 i, u⁆⁆ - ⁅distinguishedElement k 4 (i + 1), u⁆ := by
  have h := leibniz_lie (distinguishedElement_aux8 k 4) (distinguishedElement k 4 i) u
  rw [← bracket_eq] at h
  rw [h]; abel

/-- The bracket with a first iterate equals the first iterate of the bracket minus the shifted bracket. -/
theorem bracket_iterateBracket_one (i : ℕ) (u : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 i, iterateBracket k 1 u⁆ = iterateBracket k 1 ⁅distinguishedElement k 4 i, u⁆ - ⁅distinguishedElement k 4 (i + 1), u⁆ := by
  simp only [iterateBracket_one]; exact bracket_bracket_degree01 k i u

/-- The bracket with a second iterate expands as the displayed alternating binomial combination of shifted brackets. -/
theorem bracket_iterateBracket_two (i : ℕ) (u : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 i, iterateBracket k 2 u⁆
      = iterateBracket k 2 ⁅distinguishedElement k 4 i, u⁆ - (2 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 (i + 1), u⁆
        + ⁅distinguishedElement k 4 (i + 2), u⁆ := by
  simp only [iterateBracket_two, iterateBracket_one, bracket_bracket_degree01, lie_sub, Nat.add_assoc, Nat.reduceAdd]
  module

/-- The bracket with a third iterate expands as the displayed alternating binomial combination of shifted brackets. -/
theorem bracket_iterateBracket_three (i : ℕ) (u : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 i, iterateBracket k 3 u⁆
      = iterateBracket k 3 ⁅distinguishedElement k 4 i, u⁆ - (3 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 (i + 1), u⁆
        + (3 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 (i + 2), u⁆ - ⁅distinguishedElement k 4 (i + 3), u⁆ := by
  simp only [iterateBracket_three, iterateBracket_two, iterateBracket_one, bracket_bracket_degree01, lie_sub, Nat.add_assoc,
    Nat.reduceAdd]
  module

/-- The bracket with a fourth iterate expands as the displayed alternating binomial combination of shifted brackets. -/
theorem bracket_iterateBracket_four (i : ℕ) (u : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 i, iterateBracket k 4 u⁆
      = iterateBracket k 4 ⁅distinguishedElement k 4 i, u⁆ - (4 : k) • iterateBracket k 3 ⁅distinguishedElement k 4 (i + 1), u⁆
        + (6 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 (i + 2), u⁆
        - (4 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 (i + 3), u⁆ + ⁅distinguishedElement k 4 (i + 4), u⁆ := by
  simp only [iterateBracket_four, iterateBracket_three, iterateBracket_two, iterateBracket_one, bracket_bracket_degree01, lie_sub,
    Nat.add_assoc, Nat.reduceAdd]
  module

/-- The bracket with a fifth iterate expands as the displayed alternating binomial combination of shifted brackets. -/
theorem bracket_iterateBracket_five (i : ℕ) (u : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 i, iterateBracket k 5 u⁆
      = iterateBracket k 5 ⁅distinguishedElement k 4 i, u⁆ - (5 : k) • iterateBracket k 4 ⁅distinguishedElement k 4 (i + 1), u⁆
        + (10 : k) • iterateBracket k 3 ⁅distinguishedElement k 4 (i + 2), u⁆
        - (10 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 (i + 3), u⁆
        + (5 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 (i + 4), u⁆ - ⁅distinguishedElement k 4 (i + 5), u⁆ := by
  simp only [iterateBracket_five, iterateBracket_four, iterateBracket_three, iterateBracket_two, iterateBracket_one, bracket_bracket_degree01,
    lie_sub, Nat.add_assoc, Nat.reduceAdd]
  module

/-- The fifth indexed element has zero bracket with every element. -/
@[simp] theorem bracket_generatorFive_eq_zero (u : AuxiliaryType k 4) : ⁅distinguishedElement k 4 5, u⁆ = 0 := by
  rw [displayed_eq, zero_lie]

/-- The displayed bracket with a fifth iterate expands as the stated alternating binomial combination. -/
theorem bracket_generatorZero_iterateBracket_five (u : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 0, iterateBracket k 5 u⁆
      = iterateBracket k 5 ⁅distinguishedElement k 4 0, u⁆ - (5 : k) • iterateBracket k 4 ⁅distinguishedElement k 4 1, u⁆
        + (10 : k) • iterateBracket k 3 ⁅distinguishedElement k 4 2, u⁆
        - (10 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 3, u⁆
        + (5 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 4, u⁆ := by
  have h := bracket_iterateBracket_five k 0 u
  simp only [Nat.zero_add, bracket_generatorFive_eq_zero, sub_zero] at h
  exact h

/-- If two elements have zero bracket, their bracket operators commute on every element. -/
theorem bracket_bracket_comm_of_bracket_eq_zero {u v : AuxiliaryType k 4} (h : ⁅u, v⁆ = 0) (w : AuxiliaryType k 4) :
    ⁅u, ⁅v, w⁆⁆ = ⁅v, ⁅u, w⁆⁆ := by
  rw [leibniz_lie, h, zero_lie, zero_add]

/-- The bracket operators determined by the first and zeroth indexed elements commute on every element. -/
theorem bracket_generatorOne_generatorZero_comm (w : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 1, ⁅distinguishedElement k 4 0, w⁆⁆ = ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 1, w⁆⁆ :=
  bracket_bracket_comm_of_bracket_eq_zero k (by rw [← lie_skew, bracket_eq_aux19, neg_zero]) w

/-- The bracket operators determined by the second and zeroth indexed elements commute on every element. -/
theorem bracket_generatorTwo_generatorZero_comm (w : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 2, ⁅distinguishedElement k 4 0, w⁆⁆ = ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 2, w⁆⁆ :=
  bracket_bracket_comm_of_bracket_eq_zero k (by rw [← lie_skew, bracket_eq_aux20, neg_zero]) w

/-- The displayed repeated bracket with a first iterate satisfies the stated double-commutator identity. -/
theorem bracket_generatorZero_iterateBracket_one_twice (w : AuxiliaryType k 4) :
    ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 0, iterateBracket k 1 w⁆⁆
      = (2 : k) • ⁅distinguishedElement k 4 0, iterateBracket k 1 ⁅distinguishedElement k 4 0, w⁆⁆
        - iterateBracket k 1 ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 0, w⁆⁆ := by
  have h1 := bracket_bracket_degree01 k 0 w
  have h2 := bracket_bracket_degree01 k 0 ⁅distinguishedElement k 4 0, w⁆
  simp only [iterateBracket_one]
  rw [h1, lie_sub, h2, bracket_generatorOne_generatorZero_comm]
  module

/-- An inductively generated relation between two elements of the displayed Lie algebra. -/
structure AuxiliaryPairCondition (b c : AuxiliaryType k 4) : Prop where
  
  /-- The owner's relation implies that the zeroth indexed element has zero bracket with its first element. -/
  pairAuxiliaryBracketIdentityEleven : ⁅distinguishedElement k 4 0, b⁆ = 0
  
  /-- The owner's relation implies that the first indexed element has zero bracket with its first element. -/
  pairAuxiliaryBracketIdentityFour : ⁅distinguishedElement k 4 1, b⁆ = 0
  
  /-- The owner's relation implies that the second indexed element has zero bracket with its first element. -/
  pairAuxiliaryBracketIdentityEight : ⁅distinguishedElement k 4 2, b⁆ = 0
  
  /-- The owner's relation identifies the bracket of the third indexed element with its first element as its second element. -/
  pairAuxiliaryBracketIdentitySix : ⁅distinguishedElement k 4 3, b⁆ = c
  
  /-- The owner's relation implies that the displayed bracket with its first element is twice the first iterate of its second element. -/
  pairAuxiliaryBracketIdentityTwo : ⁅distinguishedElement k 4 4, b⁆ = (2 : k) • iterateBracket k 1 c
  
  /-- The owner's relation implies that the displayed fifth iterate of the first element is zero. -/
  pairAuxiliaryIterate_eq_zero_two : iterateBracket k 5 b = 0

/-- An inductively generated condition on elements of the displayed Lie algebra. -/
structure AuxiliaryCondition (c : AuxiliaryType k 4) : Prop where
  
  /-- The owner's condition implies that the zeroth indexed element has zero bracket with the given element. -/
  auxiliaryBracketIdentityNine : ⁅distinguishedElement k 4 0, c⁆ = 0
  
  /-- The owner's condition implies that the displayed third iterate is zero. -/
  auxiliaryIterate_eq_zero_three : iterateBracket k 3 c = 0
  
  /-- The owner's condition implies the displayed scalar-weighted bracket identity. -/
  auxiliaryBracketIdentitySeven : (2 : k) • ⁅distinguishedElement k 4 2, c⁆ = (3 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 1, c⁆

/-- Twice the first iterate of the displayed bracket equals the bracket of the zeroth and fourth indexed elements. -/
theorem two_smul_iterateBracket_one_bracket :
    (2 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ = ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆ := by
  have h : iterateBracket k 1 ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆
      = ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ + ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆ := by
    rw [iterateBracket_one]; exact bracket_eq_aux44 k 4 0 3
  have h2 : (2 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ = -⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆ := by
    rw [eq_neg_iff_add_eq_zero]; exact bracket_eq_aux24 k
  rw [h, smul_add, h2]
  module

/-- The displayed initial target element and negated bracket satisfy the auxiliary pair condition. -/
theorem auxiliaryPairCondition_initialElements : AuxiliaryPairCondition k (distinguishedElement_aux7 k 4) (-⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆) where
  pairAuxiliaryBracketIdentityEleven := lie_self _
  pairAuxiliaryBracketIdentityFour := by
    change ⁅distinguishedElement k 4 1, distinguishedElement k 4 0⁆ = 0
    rw [← lie_skew, bracket_eq_aux19, neg_zero]
  pairAuxiliaryBracketIdentityEight := by
    change ⁅distinguishedElement k 4 2, distinguishedElement k 4 0⁆ = 0
    rw [← lie_skew, bracket_eq_aux20, neg_zero]
  pairAuxiliaryBracketIdentitySix := by
    change ⁅distinguishedElement k 4 3, distinguishedElement k 4 0⁆ = _
    rw [← lie_skew]
  pairAuxiliaryBracketIdentityTwo := by
    change ⁅distinguishedElement k 4 4, distinguishedElement k 4 0⁆ = _
    rw [← lie_skew, iterateBracket_neg, smul_neg, two_smul_iterateBracket_one_bracket]
  pairAuxiliaryIterate_eq_zero_two := by rw [iterateBracket_initialElement, displayed_eq]

section Step

variable {k}

/-- The owner's relation implies that the zeroth indexed element has zero bracket with the first iterate of its first element. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityTwelve {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 1 b⁆ = 0 := by
  rw [bracket_iterateBracket_one, h.pairAuxiliaryBracketIdentityEleven, h.pairAuxiliaryBracketIdentityFour]; simp

/-- The owner's relation implies that the first indexed element has zero bracket with the first iterate of its first element. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityFive {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 1, iterateBracket k 1 b⁆ = 0 := by
  rw [bracket_iterateBracket_one, h.pairAuxiliaryBracketIdentityFour, h.pairAuxiliaryBracketIdentityEight]; simp

/-- The owner's relation identifies the displayed bracket with the negation of its second element. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityNine {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 2, iterateBracket k 1 b⁆ = -c := by
  rw [bracket_iterateBracket_one, h.pairAuxiliaryBracketIdentityEight, h.pairAuxiliaryBracketIdentitySix]; simp

/-- The owner's relation gives the displayed negated first-iterate bracket identity. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentitySeven {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 3, iterateBracket k 1 b⁆ = -iterateBracket k 1 c := by
  rw [bracket_iterateBracket_one, h.pairAuxiliaryBracketIdentitySix, h.pairAuxiliaryBracketIdentityTwo]; module

/-- The owner's relation implies the displayed bracket identity involving first and second iterates. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityThree {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 4, iterateBracket k 1 b⁆ = (2 : k) • iterateBracket k 2 c := by
  rw [bracket_iterateBracket_one, h.pairAuxiliaryBracketIdentityTwo, bracket_generatorFive_eq_zero, sub_zero, iterateBracket_smul, iterateBracket_one_apply]

/-- The owner's relation implies that the displayed fifth iterate of the first iterate is zero. -/
theorem AuxiliaryPairCondition.pairAuxiliaryIterate_eq_zero_one {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    iterateBracket k 5 (iterateBracket k 1 b) = 0 := by
  rw [iterateBracket_apply_one, iterateBracket_succ, h.pairAuxiliaryIterate_eq_zero_two, _root_.lie_zero]

/-- The owner's relation implies that the displayed bracket with the second iterate is zero. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityFourteen {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 2 b⁆ = 0 := by
  rw [bracket_iterateBracket_two, h.pairAuxiliaryBracketIdentityEleven, h.pairAuxiliaryBracketIdentityFour, h.pairAuxiliaryBracketIdentityEight]; simp

/-- The owner's relation identifies the displayed bracket with the negation of its second element. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityThirteen {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 3 b⁆ = -c := by
  rw [bracket_iterateBracket_three, h.pairAuxiliaryBracketIdentityEleven, h.pairAuxiliaryBracketIdentityFour, h.pairAuxiliaryBracketIdentityEight, h.pairAuxiliaryBracketIdentitySix]; simp

/-- The owner's relation implies that the zeroth indexed element has zero bracket with its second element. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityFifteen {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 0, c⁆ = 0 := by
  have hs := bracket_generatorZero_iterateBracket_one_twice k (iterateBracket k 2 b)
  rw [iterateBracket_one_apply, h.pairAuxiliaryBracketIdentityFourteen, h.pairAuxiliaryBracketIdentityThirteen] at hs
  simp only [lie_neg, _root_.lie_zero, iterateBracket_zero_apply, smul_zero, sub_zero, neg_eq_zero] at hs
  exact hs

/-- The owner's relation gives the displayed bracket identity involving third and second iterates. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityTen {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    ⁅distinguishedElement k 4 2, iterateBracket k 3 b⁆ = (3 : k) • iterateBracket k 2 c := by
  rw [bracket_iterateBracket_three, h.pairAuxiliaryBracketIdentityEight, h.pairAuxiliaryBracketIdentitySix, h.pairAuxiliaryBracketIdentityTwo, bracket_generatorFive_eq_zero]
  simp only [iterateBracket_zero_apply, iterateBracket_smul, iterateBracket_one_apply]
  module

/-- The owner's relation implies that ten times the displayed third iterate of its second element is zero. -/
theorem AuxiliaryPairCondition.ten_smul_pairAuxiliaryIterate_eq_zero {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    (10 : k) • iterateBracket k 3 c = 0 := by
  have hs := bracket_generatorZero_iterateBracket_five k (iterateBracket k 1 b)
  rw [h.pairAuxiliaryIterate_eq_zero_one, h.pairAuxiliaryBracketIdentityTwelve, h.pairAuxiliaryBracketIdentityFive, h.pairAuxiliaryBracketIdentityNine,
    h.pairAuxiliaryBracketIdentitySeven, h.pairAuxiliaryBracketIdentityThree] at hs
  simp only [_root_.lie_zero, iterateBracket_zero_apply, smul_zero, sub_zero, iterateBracket_neg, iterateBracket_smul,
    iterateBracket_one_apply, iterateBracket_apply_one, Nat.reduceAdd] at hs
  rw [hs]
  module

/-- The owner's relation implies the displayed scalar-weighted bracket identity for its second element. -/
theorem AuxiliaryPairCondition.pairAuxiliaryBracketIdentityOne {b c : AuxiliaryType k 4} (h : AuxiliaryPairCondition k b c) :
    (4 : k) • ⁅distinguishedElement k 4 2, c⁆ = (6 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 1, c⁆ := by
  have hc : c = -⁅distinguishedElement k 4 0, iterateBracket k 3 b⁆ := by rw [h.pairAuxiliaryBracketIdentityThirteen, neg_neg]
  have key : ⁅distinguishedElement k 4 2, c⁆ = -((3 : k) • ⁅distinguishedElement k 4 0, iterateBracket k 2 c⁆) := by
    conv_lhs => rw [hc]
    rw [lie_neg, bracket_generatorTwo_generatorZero_comm, h.pairAuxiliaryBracketIdentityTen, lie_smul]
  have hexp : ⁅distinguishedElement k 4 0, iterateBracket k 2 c⁆
      = iterateBracket k 2 ⁅distinguishedElement k 4 0, c⁆ - (2 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 1, c⁆ + ⁅distinguishedElement k 4 2, c⁆ :=
    bracket_iterateBracket_two k 0 c
  rw [h.pairAuxiliaryBracketIdentityFifteen, iterateBracket_zero_apply, zero_sub] at hexp
  rw [hexp] at key
  rw [← sub_eq_zero] at key ⊢
  rw [← key]
  module

/-- The auxiliary endomorphism given by the negation of bracket with the first indexed element. -/
noncomputable def negBracketWithGeneratorOne (c : AuxiliaryType k 4) : AuxiliaryType k 4 := -⁅distinguishedElement k 4 1, c⁆

/-- The auxiliary endomorphism given by bracket with the third indexed element. -/
noncomputable def bracketWithGeneratorThree (b : AuxiliaryType k 4) : AuxiliaryType k 4 := ⁅distinguishedElement k 4 3, b⁆

/-- Bracket with the first indexed element is the negation of the displayed auxiliary transform. -/
theorem bracket_generatorOne_eq_neg_auxiliaryTransform (c : AuxiliaryType k 4) : ⁅distinguishedElement k 4 1, c⁆ = -negBracketWithGeneratorOne c := by
  rw [negBracketWithGeneratorOne, neg_neg]

/-- The auxiliary endomorphism is the negation of bracket with the first indexed element. -/
theorem negBracketWithGeneratorOne_apply (c : AuxiliaryType k 4) : negBracketWithGeneratorOne c = -⁅distinguishedElement k 4 1, c⁆ := rfl

/-- The auxiliary endomorphism is bracket with the third indexed element. -/
theorem bracketWithGeneratorThree_apply (b : AuxiliaryType k 4) : bracketWithGeneratorThree b = ⁅distinguishedElement k 4 3, b⁆ := rfl

end Step

section Field

variable {k : Type*} [Field k]

/-- Under the stated nonvanishing hypotheses, the displayed auxiliary pair condition implies the owner's condition for its second element. -/
theorem AuxiliaryCondition.of_auxiliaryPairCondition (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) {b c : AuxiliaryType k 4}
    (h : AuxiliaryPairCondition k b c) : AuxiliaryCondition k c where
  auxiliaryBracketIdentityNine := h.pairAuxiliaryBracketIdentityFifteen
  auxiliaryIterate_eq_zero_three := by
    have h10 : (10 : k) ≠ 0 := by
      have : (10 : k) = 2 * 5 := by norm_num
      rw [this]; exact mul_ne_zero h2 h5
    have := congrArg (fun v : AuxiliaryType k 4 => (10 : k)⁻¹ • v) h.ten_smul_pairAuxiliaryIterate_eq_zero
    simpa [smul_smul, inv_mul_cancel₀ h10] using this
  auxiliaryBracketIdentitySeven := by
    have hkey := h.pairAuxiliaryBracketIdentityOne
    have := congrArg (fun v : AuxiliaryType k 4 => (2 : k)⁻¹ • v) hkey
    simp only [smul_smul] at this
    rw [show (2 : k)⁻¹ * 4 = 2 by field_simp; ring,
      show (2 : k)⁻¹ * 6 = 3 by field_simp; ring] at this
    exact this

/-- Under the stated nonvanishing hypotheses, the negated displayed bracket satisfies the auxiliary condition. -/
theorem auxiliaryCondition_neg_bracket (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    AuxiliaryCondition k (-⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆) :=
  AuxiliaryCondition.of_auxiliaryPairCondition h2 h5 (auxiliaryPairCondition_initialElements k)

/-- Under the stated nonvanishing hypotheses, the third iterate of the displayed bracket is zero. -/
theorem iterateBracket_three_bracket_eq_zero (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    iterateBracket k 3 ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ = 0 := by
  have h := (auxiliaryCondition_neg_bracket h2 h5).auxiliaryIterate_eq_zero_three
  rw [iterateBracket_neg, neg_eq_zero] at h
  exact h

/-- Under the stated nonvanishing hypotheses, the displayed repeated bracket with the zeroth indexed element is zero. -/
theorem bracket_generatorZero_selfBracket_eq_zero (h2 : (2 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆⁆ = 0 := by
  have h := (auxiliaryCondition_neg_bracket h2 h5).auxiliaryBracketIdentityNine
  rw [lie_neg, neg_eq_zero] at h
  exact h

end Field

section EvenToOdd

variable {k : Type*} [Field k] {c : AuxiliaryType k 4}

private theorem smul_cancel₀ {a : k} (ha : a ≠ 0) {v w : AuxiliaryType k 4} (hvw : a • v = a • w) : v = w := by
  have h' := congrArg (fun z : AuxiliaryType k 4 => a⁻¹ • z) hvw
  simpa [smul_smul, inv_mul_cancel₀ ha] using h'

private theorem eq_zero_of_smul₀ {a : k} (ha : a ≠ 0) {v : AuxiliaryType k 4} (hv : a • v = 0) : v = 0 :=
  smul_cancel₀ ha (by rw [hv, smul_zero])

/-- The bracket of the fourth and zeroth indexed elements is twice the bracket of the first and third indexed elements. -/
theorem bracket_generatorFour_generatorZero : ⁅distinguishedElement k 4 4, distinguishedElement k 4 0⁆ = (2 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ := by
  have h := bracket_eq_aux24 k
  rw [(lie_skew (distinguishedElement k 4 4) (distinguishedElement k 4 0)).symm]
  linear_combination (norm := module) -h

namespace AuxiliaryCondition

/-- The owner's condition implies the displayed scalar-weighted bracket identity involving the third indexed element. -/
theorem auxiliaryBracketIdentityTwenty (h : AuxiliaryCondition k c) :
    (2 : k) • ⁅distinguishedElement k 4 3, c⁆ = (3 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 1, c⁆ := by
  have e := bracket_iterateBracket_three k 0 c
  rw [h.auxiliaryIterate_eq_zero_three, h.auxiliaryBracketIdentityNine] at e
  simp only [Nat.zero_add, _root_.lie_zero, iterateBracket_zero_apply] at e
  have hD : (2 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 2, c⁆ = (3 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 1, c⁆ := by
    rw [← iterateBracket_smul, h.auxiliaryBracketIdentitySeven, iterateBracket_smul, iterateBracket_one_apply]
  linear_combination (norm := module) (2 : k) • e + (3 : k) • hD

/-- Under the owner's condition and the stated nonvanishing hypothesis, the displayed bracket with the fourth indexed element equals the third iterate of a bracket. -/
theorem auxiliaryBracketIdentityThree (h2 : (2 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 4, c⁆ = iterateBracket k 3 ⁅distinguishedElement k 4 1, c⁆ := by
  have e := bracket_iterateBracket_three k 1 c
  rw [h.auxiliaryIterate_eq_zero_three] at e
  simp only [Nat.reduceAdd, _root_.lie_zero] at e
  have hD2 : (2 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 2, c⁆ = (3 : k) • iterateBracket k 3 ⁅distinguishedElement k 4 1, c⁆ := by
    rw [← iterateBracket_smul, h.auxiliaryBracketIdentitySeven, iterateBracket_smul, iterateBracket_apply_one]
  have hD3 : (2 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 3, c⁆ = (3 : k) • iterateBracket k 3 ⁅distinguishedElement k 4 1, c⁆ := by
    rw [← iterateBracket_smul, h.auxiliaryBracketIdentityTwenty, iterateBracket_smul, iterateBracket_one_apply]
  refine smul_cancel₀ h2 ?_
  linear_combination (norm := module) (2 : k) • e - (3 : k) • hD2 + (3 : k) • hD3

/-- The owner's condition implies that the zeroth indexed element has zero bracket with the transformed element. -/
theorem auxiliaryBracketIdentityEighteen (h : AuxiliaryCondition k c) : ⁅distinguishedElement k 4 0, negBracketWithGeneratorOne c⁆ = 0 := by
  rw [negBracketWithGeneratorOne_apply, lie_neg, ← bracket_generatorOne_generatorZero_comm, h.auxiliaryBracketIdentityNine, _root_.lie_zero, neg_zero]

/-- The owner's condition implies that the displayed bracket with a first iterate equals the auxiliary transformed element. -/
theorem auxiliaryBracketIdentityEleven (h : AuxiliaryCondition k c) : ⁅distinguishedElement k 4 0, iterateBracket k 1 c⁆ = negBracketWithGeneratorOne c := by
  rw [bracket_iterateBracket_one, h.auxiliaryBracketIdentityNine, iterateBracket_zero_apply, zero_sub, negBracketWithGeneratorOne_apply]

/-- The owner's condition implies the displayed doubled bracket identity involving the second iterate. -/
theorem auxiliaryBracketIdentityTwentyThree (h : AuxiliaryCondition k c) :
    (2 : k) • ⁅distinguishedElement k 4 0, iterateBracket k 2 c⁆ = iterateBracket k 1 (negBracketWithGeneratorOne c) := by
  have e := bracket_iterateBracket_two k 0 c
  rw [h.auxiliaryBracketIdentityNine] at e
  simp only [Nat.zero_add, iterateBracket_zero_apply, zero_sub] at e
  have hb : iterateBracket k 1 (negBracketWithGeneratorOne c) = -iterateBracket k 1 ⁅distinguishedElement k 4 1, c⁆ := by
    rw [negBracketWithGeneratorOne_apply, iterateBracket_neg]
  linear_combination (norm := module) (2 : k) • e - hb + h.auxiliaryBracketIdentitySeven

/-- The owner's condition implies the displayed bracket identity involving the auxiliary transform. -/
theorem auxiliaryBracketIdentityThirteen (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 1 (negBracketWithGeneratorOne c)⁆ = -⁅distinguishedElement k 4 1, negBracketWithGeneratorOne c⁆ := by
  rw [bracket_iterateBracket_one, h.auxiliaryBracketIdentityEighteen, iterateBracket_zero_apply, zero_sub]

/-- Under the owner's condition and the stated nonvanishing hypothesis, the first indexed element has zero bracket with the transformed element. -/
theorem auxiliaryBracketIdentitySix (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 1, negBracketWithGeneratorOne c⁆ = 0 := by
  have hs := bracket_generatorZero_iterateBracket_one_twice k (iterateBracket k 1 c)
  rw [iterateBracket_one_apply, h.auxiliaryBracketIdentityEleven, h.auxiliaryBracketIdentityEighteen, h.auxiliaryBracketIdentityThirteen] at hs
  simp only [iterateBracket_zero_apply, sub_zero, smul_neg] at hs
  have hL : (2 : k) • ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 0, iterateBracket k 2 c⁆⁆ = -⁅distinguishedElement k 4 1, negBracketWithGeneratorOne c⁆ := by
    rw [← lie_smul, h.auxiliaryBracketIdentityTwentyThree, h.auxiliaryBracketIdentityThirteen]
  refine eq_zero_of_smul₀ h3 ?_
  linear_combination (norm := module) (2 : k) • hs - hL

/-- Under the owner's condition and the stated nonvanishing hypothesis, the displayed bracket with a second iterate equals the comparison bracket. -/
theorem auxiliaryBracketIdentityFifteen (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 2 (negBracketWithGeneratorOne c)⁆ = ⁅distinguishedElement k 4 2, negBracketWithGeneratorOne c⁆ := by
  have e := bracket_iterateBracket_two k 0 (negBracketWithGeneratorOne c)
  rw [h.auxiliaryBracketIdentityEighteen, h.auxiliaryBracketIdentitySix h3] at e
  simpa using e

/-- Under the owner's condition and the stated nonvanishing hypotheses, the second indexed element has zero bracket with the transformed element. -/
theorem auxiliaryBracketIdentityEight (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 2, negBracketWithGeneratorOne c⁆ = 0 := by
  have hs := bracket_generatorZero_iterateBracket_one_twice k (iterateBracket k 2 c)
  rw [iterateBracket_one_apply, h.auxiliaryIterate_eq_zero_three] at hs
  simp only [_root_.lie_zero] at hs
  have hP : (2 : k) • ⁅distinguishedElement k 4 0, iterateBracket k 1 ⁅distinguishedElement k 4 0, iterateBracket k 2 c⁆⁆
      = ⁅distinguishedElement k 4 2, negBracketWithGeneratorOne c⁆ := by
    rw [← lie_smul, ← iterateBracket_smul, h.auxiliaryBracketIdentityTwentyThree, iterateBracket_one_apply,
      h.auxiliaryBracketIdentityFifteen h3]
  have hQ : (2 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 0, iterateBracket k 2 c⁆⁆ = 0 := by
    rw [← iterateBracket_smul, ← lie_smul, h.auxiliaryBracketIdentityTwentyThree, h.auxiliaryBracketIdentityThirteen,
      h.auxiliaryBracketIdentitySix h3, neg_zero, iterateBracket_zero_apply]
  refine eq_zero_of_smul₀ h2 ?_
  linear_combination (norm := module) (-2 : k) • hs - (2 : k) • hP + hQ

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed fifth iterate is zero. -/
theorem auxiliaryIterate_eq_zero_one (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    iterateBracket k 5 (negBracketWithGeneratorOne c) = 0 := by
  have hsix : iterateBracket k 6 c = 0 := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, iterateBracket_add, h.auxiliaryIterate_eq_zero_three, iterateBracket_zero_apply]
  have hs := bracket_generatorZero_iterateBracket_five k (iterateBracket k 1 c)
  rw [iterateBracket_apply_one, hsix] at hs
  simp only [_root_.lie_zero] at hs
  have e0 : iterateBracket k 5 ⁅distinguishedElement k 4 0, iterateBracket k 1 c⁆ = iterateBracket k 5 (negBracketWithGeneratorOne c) := by
    rw [h.auxiliaryBracketIdentityEleven]
  have e1 : (2 : k) • iterateBracket k 4 ⁅distinguishedElement k 4 1, iterateBracket k 1 c⁆ = iterateBracket k 5 (negBracketWithGeneratorOne c) := by
    have h1 : (2 : k) • ⁅distinguishedElement k 4 1, iterateBracket k 1 c⁆ = iterateBracket k 1 (negBracketWithGeneratorOne c) := by
      have e := bracket_iterateBracket_one k 1 c
      have hb : iterateBracket k 1 (negBracketWithGeneratorOne c) = -iterateBracket k 1 ⁅distinguishedElement k 4 1, c⁆ := by rw [negBracketWithGeneratorOne_apply, iterateBracket_neg]
      linear_combination (norm := module) (2 : k) • e - hb - h.auxiliaryBracketIdentitySeven
    rw [← iterateBracket_smul, h1, iterateBracket_apply_one]
  have e2 : iterateBracket k 3 ⁅distinguishedElement k 4 2, iterateBracket k 1 c⁆ = 0 := by
    have h2' : (2 : k) • ⁅distinguishedElement k 4 2, iterateBracket k 1 c⁆ = 0 := by
      have e := bracket_iterateBracket_one k 2 c
      have hD : iterateBracket k 1 ((2 : k) • ⁅distinguishedElement k 4 2, c⁆) = (3 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 1, c⁆ := by
        rw [h.auxiliaryBracketIdentitySeven, iterateBracket_smul, iterateBracket_one_apply]
      rw [iterateBracket_smul] at hD
      linear_combination (norm := module) (2 : k) • e + hD - h.auxiliaryBracketIdentityTwenty
    rw [eq_zero_of_smul₀ h2 h2', iterateBracket_zero_apply]
  have e3 : (2 : k) • iterateBracket k 2 ⁅distinguishedElement k 4 3, iterateBracket k 1 c⁆ = -iterateBracket k 5 (negBracketWithGeneratorOne c) := by
    have h3' : (2 : k) • ⁅distinguishedElement k 4 3, iterateBracket k 1 c⁆ = -iterateBracket k 3 (negBracketWithGeneratorOne c) := by
      have e := bracket_iterateBracket_one k 3 c
      have hD : iterateBracket k 1 ((2 : k) • ⁅distinguishedElement k 4 3, c⁆) = (3 : k) • iterateBracket k 3 ⁅distinguishedElement k 4 1, c⁆ := by
        rw [h.auxiliaryBracketIdentityTwenty, iterateBracket_smul, iterateBracket_one_apply]
      rw [iterateBracket_smul] at hD
      have hb : iterateBracket k 3 (negBracketWithGeneratorOne c) = -iterateBracket k 3 ⁅distinguishedElement k 4 1, c⁆ := by rw [negBracketWithGeneratorOne_apply, iterateBracket_neg]
      simp only [Nat.reduceAdd] at e
      linear_combination (norm := module) (2 : k) • e + hD - (2 : k) • h.auxiliaryBracketIdentityThree h2 + hb
    rw [← iterateBracket_smul, h3', iterateBracket_neg, show (5 : ℕ) = 2 + 3 from rfl, iterateBracket_add]
  have e4 : iterateBracket k 1 ⁅distinguishedElement k 4 4, iterateBracket k 1 c⁆ = -iterateBracket k 5 (negBracketWithGeneratorOne c) := by
    have h4 : ⁅distinguishedElement k 4 4, iterateBracket k 1 c⁆ = -iterateBracket k 4 (negBracketWithGeneratorOne c) := by
      have e := bracket_iterateBracket_one k 4 c
      have hb : iterateBracket k 4 (negBracketWithGeneratorOne c) = -iterateBracket k 4 ⁅distinguishedElement k 4 1, c⁆ := by rw [negBracketWithGeneratorOne_apply, iterateBracket_neg]
      have hD : iterateBracket k 1 ⁅distinguishedElement k 4 4, c⁆ = iterateBracket k 4 ⁅distinguishedElement k 4 1, c⁆ := by
        rw [h.auxiliaryBracketIdentityThree h2, iterateBracket_one_apply]
      simp only [Nat.reduceAdd, bracket_generatorFive_eq_zero] at e
      linear_combination (norm := module) e + hD + hb
    rw [h4, iterateBracket_neg, iterateBracket_one_apply]
  refine eq_zero_of_smul₀ h3 ?_
  linear_combination (norm := module) (2 : k) • hs + (2 : k) • e0 - (5 : k) • e1
    + (20 : k) • e2 - (10 : k) • e3 + (10 : k) • e4

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed bracket with a third iterate is the negation of the auxiliary image. -/
theorem auxiliaryBracketIdentityFourteen (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 3 (negBracketWithGeneratorOne c)⁆ = -bracketWithGeneratorThree (negBracketWithGeneratorOne c) := by
  have e := bracket_iterateBracket_three k 0 (negBracketWithGeneratorOne c)
  rw [h.auxiliaryBracketIdentityEighteen, h.auxiliaryBracketIdentitySix h3, h.auxiliaryBracketIdentityEight h2 h3] at e
  simpa [bracketWithGeneratorThree_apply] using e

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed bracket with a fourth iterate expands as the stated sum. -/
theorem auxiliaryBracketIdentityTen (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 4 (negBracketWithGeneratorOne c)⁆
      = -((4 : k) • iterateBracket k 1 (bracketWithGeneratorThree (negBracketWithGeneratorOne c))) + ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆ := by
  have e := bracket_iterateBracket_four k 0 (negBracketWithGeneratorOne c)
  rw [h.auxiliaryBracketIdentityEighteen, h.auxiliaryBracketIdentitySix h3, h.auxiliaryBracketIdentityEight h2 h3] at e
  simpa [bracketWithGeneratorThree_apply] using e

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed bracket with the auxiliary image is zero. -/
theorem auxiliaryBracketIdentitySixteen (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 0, bracketWithGeneratorThree (negBracketWithGeneratorOne c)⁆ = 0 := by
  have hs := bracket_generatorZero_iterateBracket_one_twice k (iterateBracket k 2 (negBracketWithGeneratorOne c))
  rw [iterateBracket_one_apply, h.auxiliaryBracketIdentityFifteen h3, h.auxiliaryBracketIdentityEight h2 h3,
    h.auxiliaryBracketIdentityFourteen h2 h3] at hs
  simp only [iterateBracket_zero_apply, _root_.lie_zero, smul_zero, sub_zero, lie_neg, neg_eq_zero] at hs
  exact hs

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed bracket with an iterated transformed element equals the stated negated bracket. -/
theorem auxiliaryBracketIdentityTwelve (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 0, iterateBracket k 1 (bracketWithGeneratorThree (negBracketWithGeneratorOne c))⁆ = -⁅distinguishedElement k 4 1, bracketWithGeneratorThree (negBracketWithGeneratorOne c)⁆ := by
  rw [bracket_iterateBracket_one, h.auxiliaryBracketIdentitySixteen h2 h3, iterateBracket_zero_apply, zero_sub]

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed iterated-bracket identity with coefficients two holds. -/
theorem auxiliaryBracketIdentityOne (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : AuxiliaryCondition k c) :
    iterateBracket k 1 ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆ = (2 : k) • iterateBracket k 2 (bracketWithGeneratorThree (negBracketWithGeneratorOne c)) := by
  have hs := bracket_generatorZero_iterateBracket_five k (negBracketWithGeneratorOne c)
  rw [h.auxiliaryIterate_eq_zero_one h2 h3, h.auxiliaryBracketIdentityEighteen, h.auxiliaryBracketIdentitySix h3,
    h.auxiliaryBracketIdentityEight h2 h3] at hs
  simp only [_root_.lie_zero, iterateBracket_zero_apply, smul_zero, sub_zero, zero_sub, add_zero] at hs
  rw [← bracketWithGeneratorThree_apply] at hs
  refine smul_cancel₀ h5 ?_
  linear_combination (norm := module) -hs

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed double bracket equals negative twice the comparison bracket. -/
theorem auxiliaryBracketIdentitySeventeen (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆⁆ = -((2 : k) • ⁅distinguishedElement k 4 1, bracketWithGeneratorThree (negBracketWithGeneratorOne c)⁆) := by
  have hs := bracket_generatorZero_iterateBracket_one_twice k (iterateBracket k 3 (negBracketWithGeneratorOne c))
  rw [iterateBracket_one_apply, h.auxiliaryBracketIdentityFourteen h2 h3, h.auxiliaryBracketIdentityTen h2 h3] at hs
  simp only [lie_neg, h.auxiliaryBracketIdentitySixteen h2 h3, neg_zero, iterateBracket_zero_apply, sub_zero, lie_add,
    lie_neg, lie_smul, smul_neg, iterateBracket_neg] at hs
  rw [h.auxiliaryBracketIdentityTwelve h2 h3] at hs
  linear_combination (norm := module) hs

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed second- and third-iterate bracket identity holds. -/
theorem auxiliaryBracketIdentityTwo (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : AuxiliaryCondition k c) :
    iterateBracket k 2 ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆ = (2 : k) • iterateBracket k 3 (bracketWithGeneratorThree (negBracketWithGeneratorOne c)) := by
  have e := congrArg (fun v : AuxiliaryType k 4 => iterateBracket k 1 v) (h.auxiliaryBracketIdentityOne h2 h3 h5)
  simpa [iterateBracket_one_apply] using e

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed third iterate of the transformed element is zero. -/
theorem auxiliaryIterate_eq_zero_two (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : AuxiliaryCondition k c) : iterateBracket k 3 (bracketWithGeneratorThree (negBracketWithGeneratorOne c)) = 0 := by
  have h10 : (10 : k) ≠ 0 := by
    have h' : (10 : k) = 2 * 5 := by norm_num
    rw [h']; exact mul_ne_zero h2 h5
  have hs := bracket_generatorZero_iterateBracket_five k (iterateBracket k 1 (negBracketWithGeneratorOne c))
  rw [iterateBracket_apply_one, ← iterateBracket_one_apply, h.auxiliaryIterate_eq_zero_one h2 h3] at hs
  simp only [iterateBracket_zero_apply, _root_.lie_zero] at hs
  have g0 : ⁅distinguishedElement k 4 0, iterateBracket k 1 (negBracketWithGeneratorOne c)⁆ = 0 := by
    have e := bracket_iterateBracket_one k 0 (negBracketWithGeneratorOne c)
    simp only [Nat.zero_add] at e
    rw [e, h.auxiliaryBracketIdentityEighteen, h.auxiliaryBracketIdentitySix h3]; simp
  have g1 : ⁅distinguishedElement k 4 1, iterateBracket k 1 (negBracketWithGeneratorOne c)⁆ = 0 := by
    have e := bracket_iterateBracket_one k 1 (negBracketWithGeneratorOne c)
    simp only [Nat.reduceAdd] at e
    rw [e, h.auxiliaryBracketIdentitySix h3, h.auxiliaryBracketIdentityEight h2 h3]; simp
  have g2 : ⁅distinguishedElement k 4 2, iterateBracket k 1 (negBracketWithGeneratorOne c)⁆ = -bracketWithGeneratorThree (negBracketWithGeneratorOne c) := by
    have e := bracket_iterateBracket_one k 2 (negBracketWithGeneratorOne c)
    simp only [Nat.reduceAdd] at e
    rw [e, h.auxiliaryBracketIdentityEight h2 h3, ← bracketWithGeneratorThree_apply]; simp
  have g3 : ⁅distinguishedElement k 4 3, iterateBracket k 1 (negBracketWithGeneratorOne c)⁆
      = iterateBracket k 1 (bracketWithGeneratorThree (negBracketWithGeneratorOne c)) - ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆ := by
    have e := bracket_iterateBracket_one k 3 (negBracketWithGeneratorOne c)
    simp only [Nat.reduceAdd] at e
    rw [e, ← bracketWithGeneratorThree_apply]
  have g4 : ⁅distinguishedElement k 4 4, iterateBracket k 1 (negBracketWithGeneratorOne c)⁆ = iterateBracket k 1 ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆ := by
    have e := bracket_iterateBracket_one k 4 (negBracketWithGeneratorOne c)
    simp only [Nat.reduceAdd, bracket_generatorFive_eq_zero, sub_zero] at e
    exact e
  rw [g0, g1, g2, g3, g4] at hs
  simp only [iterateBracket_zero_apply, smul_zero, iterateBracket_neg, iterateBracket_sub, iterateBracket_apply_one] at hs
  refine eq_zero_of_smul₀ h10 ?_
  linear_combination (norm := module) -hs - (15 : k) • h.auxiliaryBracketIdentityTwo h2 h3 h5

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed scalar-weighted bracket identity for the auxiliary image holds. -/
theorem auxiliaryBracketIdentityTwentyTwo (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : AuxiliaryCondition k c) :
    (2 : k) • ⁅distinguishedElement k 4 2, bracketWithGeneratorThree (negBracketWithGeneratorOne c)⁆
      = (3 : k) • iterateBracket k 1 ⁅distinguishedElement k 4 1, bracketWithGeneratorThree (negBracketWithGeneratorOne c)⁆ := by
  have hs := bracket_generatorZero_iterateBracket_one_twice k (iterateBracket k 4 (negBracketWithGeneratorOne c))
  rw [iterateBracket_one_apply, h.auxiliaryIterate_eq_zero_one h2 h3, h.auxiliaryBracketIdentityTen h2 h3] at hs
  simp only [_root_.lie_zero] at hs
  have hP : ⁅distinguishedElement k 4 0, -((4 : k) • iterateBracket k 1 (bracketWithGeneratorThree (negBracketWithGeneratorOne c))) + ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆⁆
      = (2 : k) • ⁅distinguishedElement k 4 1, bracketWithGeneratorThree (negBracketWithGeneratorOne c)⁆ := by
    rw [lie_add, lie_neg, lie_smul, h.auxiliaryBracketIdentityTwelve h2 h3,
      h.auxiliaryBracketIdentitySeventeen h2 h3]
    module
  have hQ : iterateBracket k 1 (-((4 : k) • iterateBracket k 1 (bracketWithGeneratorThree (negBracketWithGeneratorOne c))) + ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆)
      = -((2 : k) • iterateBracket k 2 (bracketWithGeneratorThree (negBracketWithGeneratorOne c))) := by
    rw [iterateBracket_add_apply, iterateBracket_neg, iterateBracket_smul, iterateBracket_one_apply, h.auxiliaryBracketIdentityOne h2 h3 h5]
    module
  rw [hP, hQ] at hs
  have hexp := bracket_iterateBracket_two k 0 (bracketWithGeneratorThree (negBracketWithGeneratorOne c))
  rw [h.auxiliaryBracketIdentitySixteen h2 h3] at hexp
  simp only [Nat.zero_add, iterateBracket_zero_apply, zero_sub] at hexp
  rw [lie_neg, lie_smul, iterateBracket_smul] at hs
  refine smul_cancel₀ h2 ?_
  linear_combination (norm := module) hs - (4 : k) • hexp

/-- Under the stated nonvanishing hypotheses, the owner's condition is preserved by the displayed composite auxiliary map. -/
theorem auxiliaryCondition_auxiliaryImage (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    AuxiliaryCondition k (bracketWithGeneratorThree (negBracketWithGeneratorOne c)) where
  auxiliaryBracketIdentityNine := h.auxiliaryBracketIdentitySixteen h2 h3
  auxiliaryIterate_eq_zero_three := h.auxiliaryIterate_eq_zero_two h2 h3 h5
  auxiliaryBracketIdentitySeven := h.auxiliaryBracketIdentityTwentyTwo h2 h3 h5

/-- The auxiliary endomorphism of the displayed Lie algebra used by the owner's condition. -/
noncomputable def auxiliaryTransform (c : AuxiliaryType k 4) : AuxiliaryType k 4 :=
  ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆ - (2 : k) • iterateBracket k 1 (bracketWithGeneratorThree (negBracketWithGeneratorOne c))

/-- Under the owner's condition and the stated nonvanishing hypotheses, every element has zero bracket with the auxiliary transform. -/
theorem bracket_auxiliaryTransform_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : AuxiliaryCondition k c) (v : AuxiliaryType k 4) : ⁅v, auxiliaryTransform c⁆ = 0 := by
  have hx : ⁅distinguishedElement_aux7 k 4, auxiliaryTransform c⁆ = 0 := by
    rw [auxiliaryTransform, ← displayed_eq_aux2 k 4, lie_sub, lie_smul, h.auxiliaryBracketIdentitySeventeen h2 h3,
      h.auxiliaryBracketIdentityTwelve h2 h3]
    module
  have hy : ⁅distinguishedElement_aux8 k 4, auxiliaryTransform c⁆ = 0 := by
    rw [auxiliaryTransform, ← iterateBracket_one, iterateBracket_sub, iterateBracket_smul, iterateBracket_one_apply,
      h.auxiliaryBracketIdentityOne h2 h3 h5]
    module
  let M : Submodule k (AuxiliaryType k 4) :=
    { carrier := {u | ⁅u, auxiliaryTransform c⁆ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [add_lie, ha, hb, add_zero]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_lie]
      smul_mem' := fun a u hu => by
        simp only [Set.mem_setOf_eq] at hu ⊢; rw [smul_lie, hu, smul_zero] }
  have hM : M = ⊤ := by
    refine displayed_eq_aux3 k 4 M hx hy ?_ ?_
    · intro m hm
      have hm' : ⁅m, auxiliaryTransform c⁆ = 0 := hm
      change ⁅⁅distinguishedElement_aux7 k 4, m⁆, auxiliaryTransform c⁆ = 0
      rw [lie_lie, hm', hx]; simp
    · intro m hm
      have hm' : ⁅m, auxiliaryTransform c⁆ = 0 := hm
      change ⁅⁅distinguishedElement_aux8 k 4, m⁆, auxiliaryTransform c⁆ = 0
      rw [lie_lie, hm', hy]; simp
  have : v ∈ M := by rw [hM]; trivial
  exact this

/-- Under the owner's condition and the stated nonvanishing hypothesis, the displayed doubled bracket equals the negated third iterate. -/
theorem auxiliaryBracketIdentityTwentyOne (h2 : (2 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    (2 : k) • ⁅distinguishedElement k 4 3, iterateBracket k 1 c⁆ = -iterateBracket k 3 (negBracketWithGeneratorOne c) := by
  have e := bracket_iterateBracket_one k 3 c
  simp only [Nat.reduceAdd] at e
  have hD : iterateBracket k 1 ((2 : k) • ⁅distinguishedElement k 4 3, c⁆) = (3 : k) • iterateBracket k 3 ⁅distinguishedElement k 4 1, c⁆ := by
    rw [h.auxiliaryBracketIdentityTwenty, iterateBracket_smul, iterateBracket_one_apply]
  rw [iterateBracket_smul] at hD
  have hb : iterateBracket k 3 (negBracketWithGeneratorOne c) = -iterateBracket k 3 ⁅distinguishedElement k 4 1, c⁆ := by rw [negBracketWithGeneratorOne_apply, iterateBracket_neg]
  linear_combination (norm := module) (2 : k) • e + hD - (2 : k) • h.auxiliaryBracketIdentityThree h2 + hb

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed nested bracket is zero. -/
theorem auxiliaryBracketIdentityFive (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, c⁆ = 0 := by
  have hjac : ⁅⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, c⁆
      = ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 3, c⁆⁆ - ⁅distinguishedElement k 4 3, ⁅distinguishedElement k 4 0, c⁆⁆ := lie_lie _ _ _
  rw [h.auxiliaryBracketIdentityNine, _root_.lie_zero, sub_zero] at hjac
  refine eq_zero_of_smul₀ h2 ?_
  rw [hjac, ← lie_smul, h.auxiliaryBracketIdentityTwenty, lie_smul, bracket_generatorOne_eq_neg_auxiliaryTransform, iterateBracket_neg,
    lie_neg, h.auxiliaryBracketIdentityFifteen h3, h.auxiliaryBracketIdentityEight h2 h3]
  module

/-- Under the owner's condition and the stated nonvanishing hypotheses, the displayed doubled nested bracket equals the negated auxiliary image. -/
theorem auxiliaryBracketIdentityNineteen (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    (2 : k) • ⁅⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆, iterateBracket k 1 c⁆ = -bracketWithGeneratorThree (negBracketWithGeneratorOne c) := by
  have hjac : ⁅distinguishedElement k 4 3, negBracketWithGeneratorOne c⁆
      = ⁅⁅distinguishedElement k 4 3, distinguishedElement k 4 0⁆, iterateBracket k 1 c⁆
        + ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 3, iterateBracket k 1 c⁆⁆ := by
    rw [← h.auxiliaryBracketIdentityEleven]; exact leibniz_lie _ _ _
  have ha30 : ⁅distinguishedElement k 4 3, distinguishedElement k 4 0⁆ = -⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ :=
    (lie_skew (distinguishedElement k 4 3) (distinguishedElement k 4 0)).symm
  have h2s : (2 : k) • ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 3, iterateBracket k 1 c⁆⁆ = bracketWithGeneratorThree (negBracketWithGeneratorOne c) := by
    rw [← lie_smul, h.auxiliaryBracketIdentityTwentyOne h2, lie_neg,
      h.auxiliaryBracketIdentityFourteen h2 h3, neg_neg]
  rw [ha30, neg_lie, ← bracketWithGeneratorThree_apply] at hjac
  linear_combination (norm := module) (2 : k) • hjac + h2s

/-- Under the owner's condition and the stated nonvanishing hypothesis, the displayed bracket is the negation of the fourth iterate of the transformed element. -/
theorem auxiliaryBracketIdentityFour (h2 : (2 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    ⁅distinguishedElement k 4 4, iterateBracket k 1 c⁆ = -iterateBracket k 4 (negBracketWithGeneratorOne c) := by
  have e := bracket_iterateBracket_one k 4 c
  simp only [Nat.reduceAdd, bracket_generatorFive_eq_zero, sub_zero] at e
  rw [e, h.auxiliaryBracketIdentityThree h2, iterateBracket_one_apply, bracket_generatorOne_eq_neg_auxiliaryTransform, iterateBracket_neg]

/-- Under the owner's condition and the stated nonvanishing hypotheses, the auxiliary transform equals the displayed nested bracket. -/
theorem auxiliaryTransform_eq_iteratedBracket (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h : AuxiliaryCondition k c) :
    auxiliaryTransform c = ⁅⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆, iterateBracket k 1 c⁆ := by
  have hjac : ⁅distinguishedElement k 4 4, negBracketWithGeneratorOne c⁆
      = ⁅⁅distinguishedElement k 4 4, distinguishedElement k 4 0⁆, iterateBracket k 1 c⁆
        + ⁅distinguishedElement k 4 0, ⁅distinguishedElement k 4 4, iterateBracket k 1 c⁆⁆ := by
    rw [← h.auxiliaryBracketIdentityEleven]; exact leibniz_lie _ _ _
  rw [bracket_generatorFour_generatorZero, smul_lie, h.auxiliaryBracketIdentityFour h2, lie_neg,
    h.auxiliaryBracketIdentityTen h2 h3] at hjac
  rw [auxiliaryTransform]
  refine smul_cancel₀ h2 ?_
  linear_combination (norm := module) hjac

end AuxiliaryCondition

/-- Under the stated nonvanishing hypotheses, the auxiliary condition and vanishing of its transform imply the owner's pair relation for the displayed images. -/
theorem AuxiliaryPairCondition.of_auxiliaryCondition_and_transform_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h : AuxiliaryCondition k c) (hgap : AuxiliaryCondition.auxiliaryTransform c = 0) :
    AuxiliaryPairCondition k (negBracketWithGeneratorOne c) (bracketWithGeneratorThree (negBracketWithGeneratorOne c)) where
  pairAuxiliaryBracketIdentityEleven := h.auxiliaryBracketIdentityEighteen
  pairAuxiliaryBracketIdentityFour := h.auxiliaryBracketIdentitySix h3
  pairAuxiliaryBracketIdentityEight := h.auxiliaryBracketIdentityEight h2 h3
  pairAuxiliaryBracketIdentitySix := rfl
  pairAuxiliaryBracketIdentityTwo := by rwa [AuxiliaryCondition.auxiliaryTransform, sub_eq_zero] at hgap
  pairAuxiliaryIterate_eq_zero_two := h.auxiliaryIterate_eq_zero_one h2 h3

/-- Under the stated nonvanishing and trivial-center hypotheses, the auxiliary condition implies the owner's pair relation for the displayed images. -/
theorem AuxiliaryPairCondition.of_auxiliaryCondition_and_trivial_center (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (h : AuxiliaryCondition k c) (hZ : ∀ w : AuxiliaryType k 4, (∀ v : AuxiliaryType k 4, ⁅v, w⁆ = 0) → w = 0) :
    AuxiliaryPairCondition k (negBracketWithGeneratorOne c) (bracketWithGeneratorThree (negBracketWithGeneratorOne c)) :=
  AuxiliaryPairCondition.of_auxiliaryCondition_and_transform_eq_zero h2 h3 h (hZ _ (h.bracket_auxiliaryTransform_eq_zero h2 h3 h5))

/-- A natural-number-indexed family in the displayed auxiliary Lie algebra. -/
noncomputable def auxiliarySequence (K : Type*) [CommRing K] : ℕ → AuxiliaryType K 4
  | 0 => -⁅distinguishedElement K 4 0, distinguishedElement K 4 3⁆
  | m + 1 => bracketWithGeneratorThree (negBracketWithGeneratorOne (auxiliarySequence K m))

/-- The zeroth auxiliary sequence element is the negation of the displayed bracket. -/
@[simp] theorem auxiliarySequence_zero (K : Type*) [CommRing K] :
    auxiliarySequence K 0 = -⁅distinguishedElement K 4 0, distinguishedElement K 4 3⁆ := rfl

/-- The successor auxiliary sequence element is obtained by the displayed composite of bracket endomorphisms. -/
@[simp] theorem auxiliarySequence_succ (K : Type*) [CommRing K] (m : ℕ) :
    auxiliarySequence K (m + 1) = bracketWithGeneratorThree (negBracketWithGeneratorOne (auxiliarySequence K m)) := rfl

/-- Under the stated nonvanishing hypotheses, every element of the auxiliary sequence satisfies the auxiliary condition. -/
theorem auxiliaryCondition_auxiliarySequence (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    AuxiliaryCondition k (auxiliarySequence k m) := by
  induction m with
  | zero => exact auxiliaryCondition_neg_bracket h2 h5
  | succ m ih => exact ih.auxiliaryCondition_auxiliaryImage h2 h3 h5

/-- Under the stated nonvanishing hypotheses, the displayed composite auxiliary element satisfies the auxiliary condition. -/
theorem auxiliaryCondition_compositeElement (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    AuxiliaryCondition k (bracketWithGeneratorThree (negBracketWithGeneratorOne (-⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆))) :=
  auxiliaryCondition_auxiliarySequence h2 h3 h5 1

/-- Under the stated nonvanishing hypotheses, twice the displayed bracket with a first iterate is the successor auxiliary sequence element. -/
theorem two_smul_bracket_sequence_zero_iterateBracket_one (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ) :
    (2 : k) • ⁅auxiliarySequence k 0, iterateBracket k 1 (auxiliarySequence k m)⁆ = auxiliarySequence k (m + 1) := by
  have h := (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityNineteen h2 h3
  rw [auxiliarySequence_zero, auxiliarySequence_succ, neg_lie, smul_neg, h, neg_neg]

/-- Under the stated nonvanishing hypotheses, the zeroth auxiliary sequence element has zero bracket with every sequence element. -/
theorem bracket_auxiliarySequence_zero_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅auxiliarySequence k 0, auxiliarySequence k m⁆ = 0 := by
  rw [auxiliarySequence_zero, neg_lie,
    (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityFive h2 h3, neg_zero]

/-- The first iterate of the zeroth auxiliary sequence element is the displayed bracket of indexed elements. -/
theorem iterateBracket_one_auxiliarySequence_zero : iterateBracket k 1 (auxiliarySequence k 0) = ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ := by
  have h := bracket_eq_aux24 k
  rw [auxiliarySequence_zero, iterateBracket_neg, iterateBracket_one, bracket_eq_aux44]
  linear_combination (norm := module) -h

/-- Under the stated nonvanishing hypotheses, the auxiliary transform of the zeroth sequence element is zero. -/
theorem auxiliaryTransform_auxiliarySequence_zero_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    AuxiliaryCondition.auxiliaryTransform (auxiliarySequence k 0) = 0 := by
  rw [(auxiliaryCondition_auxiliarySequence h2 h3 h5 0).auxiliaryTransform_eq_iteratedBracket h2 h3, iterateBracket_one_auxiliarySequence_zero, lie_self]

/-- Under the stated nonvanishing hypotheses, the displayed transforms of the zeroth auxiliary sequence element satisfy the auxiliary pair condition. -/
theorem auxiliaryPairCondition_sequence_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    AuxiliaryPairCondition k (negBracketWithGeneratorOne (auxiliarySequence k 0)) (bracketWithGeneratorThree (negBracketWithGeneratorOne (auxiliarySequence k 0))) :=
  AuxiliaryPairCondition.of_auxiliaryCondition_and_transform_eq_zero h2 h3 (auxiliaryCondition_auxiliarySequence h2 h3 h5 0)
    (auxiliaryTransform_auxiliarySequence_zero_eq_zero h2 h3 h5)

/-- Under the stated nonvanishing hypotheses, the displayed bracket vanishing implies the auxiliary pair condition for the corresponding sequence transforms. -/
theorem auxiliaryPairCondition_sequence_of_bracket_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) (hgap : ⁅⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆, iterateBracket k 1 (auxiliarySequence k m)⁆ = 0) :
    AuxiliaryPairCondition k (negBracketWithGeneratorOne (auxiliarySequence k m)) (bracketWithGeneratorThree (negBracketWithGeneratorOne (auxiliarySequence k m))) :=
  AuxiliaryPairCondition.of_auxiliaryCondition_and_transform_eq_zero h2 h3 (auxiliaryCondition_auxiliarySequence h2 h3 h5 m)
    (by rw [(auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryTransform_eq_iteratedBracket h2 h3, hgap])

end EvenToOdd

section Spanning

variable {k : Type*} [Field k]

/-- A natural-number-indexed auxiliary companion family in the displayed Lie algebra. -/
noncomputable def auxiliaryCompanionFamily (K : Type*) [CommRing K] : ℕ → AuxiliaryType K 4
  | 0 => distinguishedElement_aux7 K 4
  | m + 1 => negBracketWithGeneratorOne (auxiliarySequence K m)

/-- The zeroth companion-family element is the displayed initial target element. -/
@[simp] theorem auxiliaryCompanionFamily_zero (K : Type*) [CommRing K] : auxiliaryCompanionFamily K 0 = distinguishedElement_aux7 K 4 := rfl

/-- The successor companion-family element is the negated bracket transform of the corresponding sequence element. -/
@[simp] theorem auxiliaryCompanionFamily_succ (K : Type*) [CommRing K] (m : ℕ) :
    auxiliaryCompanionFamily K (m + 1) = negBracketWithGeneratorOne (auxiliarySequence K m) := rfl

/-- A natural-number-indexed auxiliary family in the displayed Lie algebra. -/
noncomputable def auxiliaryCentralFamily (K : Type*) [CommRing K] (m : ℕ) : AuxiliaryType K 4 :=
  ⁅distinguishedElement K 4 4, auxiliaryCompanionFamily K m⁆ - (2 : K) • iterateBracket K 1 (auxiliarySequence K m)

/-- The successor auxiliary central-family element is the auxiliary transform of the corresponding sequence element. -/
theorem auxiliaryCentralFamily_succ (m : ℕ) : auxiliaryCentralFamily k (m + 1) = AuxiliaryCondition.auxiliaryTransform (auxiliarySequence k m) := rfl

/-- The auxiliary central family vanishes at zero. -/
@[simp] theorem auxiliaryCentralFamily_zero : auxiliaryCentralFamily k 0 = 0 := by
  rw [auxiliaryCentralFamily, auxiliaryCompanionFamily_zero, ← displayed_eq_aux2 k 4, bracket_generatorFour_generatorZero, iterateBracket_one_auxiliarySequence_zero, sub_self]

/-- Under the stated nonvanishing hypotheses, the auxiliary central family vanishes at one. -/
theorem auxiliaryCentralFamily_one_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    auxiliaryCentralFamily k 1 = 0 :=
  auxiliaryTransform_auxiliarySequence_zero_eq_zero h2 h3 h5

/-- Under the stated nonvanishing hypotheses, every element has zero bracket with every member of the displayed auxiliary family. -/
theorem bracket_auxiliaryCentralFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ)
    (v : AuxiliaryType k 4) : ⁅v, auxiliaryCentralFamily k m⁆ = 0 := by
  cases m with
  | zero => rw [auxiliaryCentralFamily_zero, _root_.lie_zero]
  | succ m =>
      rw [auxiliaryCentralFamily_succ]
      exact (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).bracket_auxiliaryTransform_eq_zero h2 h3 h5 v

/-- If the auxiliary central family vanishes, each companion-family and sequence pair satisfies the auxiliary pair condition. -/
theorem auxiliaryPairCondition_companion_sequence (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (hgap : ∀ m : ℕ, auxiliaryCentralFamily k m = 0) (m : ℕ) : AuxiliaryPairCondition k (auxiliaryCompanionFamily k m) (auxiliarySequence k m) := by
  cases m with
  | zero => exact auxiliaryPairCondition_initialElements k
  | succ m =>
      exact AuxiliaryPairCondition.of_auxiliaryCondition_and_transform_eq_zero h2 h3 (auxiliaryCondition_auxiliarySequence h2 h3 h5 m) (hgap (m + 1))

/-- The displayed Lie algebra element associated with an auxiliary index. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
noncomputable def indexedFamily (K : Type*) [CommRing K] : AuxiliaryIndex → AuxiliaryType K 4
  | .base => distinguishedElement_aux8 K 4
  | .odd m i => iterateBracket K i (auxiliaryCompanionFamily K m)
  | .even m i => iterateBracket K i (auxiliarySequence K m)

/-- The indexed family at the displayed base index equals the displayed initial element. -/
@[simp] theorem indexedFamily_base (K : Type*) [CommRing K] : indexedFamily K .base = distinguishedElement_aux8 K 4 := rfl

/-- On the displayed five-index family, the indexed element is the corresponding iterate of the auxiliary companion-family element. -/
@[simp] theorem indexedFamily_family5 (K : Type*) [CommRing K] (m : ℕ) (i : Fin 5) :
    indexedFamily K (.odd m i) = iterateBracket K i (auxiliaryCompanionFamily K m) := rfl

/-- On the displayed three-index family, the indexed element is the corresponding iterate of the auxiliary sequence element. -/
@[simp] theorem indexedFamily_family3 (K : Type*) [CommRing K] (m : ℕ) (i : Fin 3) :
    indexedFamily K (.even m i) = iterateBracket K i (auxiliarySequence K m) := rfl

/-- An auxiliary set of elements in the displayed Lie algebra. -/
noncomputable def auxiliarySpanningSet (K : Type*) [CommRing K] : Set (AuxiliaryType K 4) :=
  Set.range (indexedFamily K) ∪ Set.range (auxiliaryCentralFamily K)

/-- Every indexed-family element belongs to the displayed auxiliary set. -/
theorem indexedFamily_mem_auxiliarySet (I : AuxiliaryIndex) : indexedFamily k I ∈ auxiliarySpanningSet k := Or.inl ⟨I, rfl⟩

/-- Every member of the auxiliary central family belongs to the auxiliary spanning set. -/
theorem auxiliaryCentralFamily_mem_auxiliarySpanningSet (m : ℕ) : auxiliaryCentralFamily k m ∈ auxiliarySpanningSet k := Or.inr ⟨m, rfl⟩

/-- Every element of the auxiliary set is either an indexed-family element or a member of the auxiliary central family. -/
theorem eq_indexedFamily_or_eq_auxiliaryCentralFamily_of_mem {v : AuxiliaryType k 4} (h : v ∈ auxiliarySpanningSet k) :
    (∃ I, indexedFamily k I = v) ∨ ∃ m, auxiliaryCentralFamily k m = v := h

/-- Under the stated nonvanishing hypotheses, the fifth iterate of every displayed auxiliary family element is zero. -/
theorem iterateBracket_five_auxiliaryFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    iterateBracket k 5 (auxiliaryCompanionFamily k m) = 0 := by
  cases m with
  | zero => rw [auxiliaryCompanionFamily_zero, iterateBracket_initialElement, displayed_eq]
  | succ m => exact (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryIterate_eq_zero_one h2 h3

/-- Under the stated nonvanishing hypotheses, the third iterate of every auxiliary sequence element is zero. -/
theorem iterateBracket_three_auxiliarySequence_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    iterateBracket k 3 (auxiliarySequence k m) = 0 :=
  (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryIterate_eq_zero_three

/-- Under the stated nonvanishing hypotheses, the zeroth indexed element has zero bracket with every auxiliary companion-family element. -/
theorem bracket_generatorZero_auxiliaryCompanionFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅distinguishedElement k 4 0, auxiliaryCompanionFamily k m⁆ = 0 := by
  cases m with
  | zero => rw [auxiliaryCompanionFamily_zero, ← displayed_eq_aux2 k 4, lie_self]
  | succ m => exact (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityEighteen

/-- Under the stated nonvanishing hypotheses, the displayed bracket with the first iterate of the companion family is zero. -/
theorem auxiliaryRecurrenceIdentityThree (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅distinguishedElement k 4 0, iterateBracket k 1 (auxiliaryCompanionFamily k m)⁆ = 0 := by
  cases m with
  | zero => rw [auxiliaryCompanionFamily_zero, iterateBracket_initialElement, bracket_eq_aux19]
  | succ m =>
      have h := auxiliaryCondition_auxiliarySequence h2 h3 h5 m
      rw [auxiliaryCompanionFamily_succ, h.auxiliaryBracketIdentityThirteen, h.auxiliaryBracketIdentitySix h3, neg_zero]

/-- Under the stated nonvanishing hypotheses, the displayed bracket with the second iterate of the companion family is zero. -/
theorem auxiliaryRecurrenceIdentityFive (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅distinguishedElement k 4 0, iterateBracket k 2 (auxiliaryCompanionFamily k m)⁆ = 0 := by
  cases m with
  | zero => rw [auxiliaryCompanionFamily_zero, iterateBracket_initialElement, bracket_eq_aux20]
  | succ m =>
      have h := auxiliaryCondition_auxiliarySequence h2 h3 h5 m
      rw [auxiliaryCompanionFamily_succ, h.auxiliaryBracketIdentityFifteen h3, h.auxiliaryBracketIdentityEight h2 h3]

/-- Under the stated nonvanishing hypotheses, the displayed bracket with the third iterate of the companion family is the negated auxiliary sequence element. -/
theorem auxiliaryRecurrenceIdentityFour (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅distinguishedElement k 4 0, iterateBracket k 3 (auxiliaryCompanionFamily k m)⁆ = -auxiliarySequence k m := by
  cases m with
  | zero => rw [auxiliaryCompanionFamily_zero, iterateBracket_initialElement, auxiliarySequence_zero, neg_neg]
  | succ m => exact (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityFourteen h2 h3

/-- Under the stated nonvanishing hypotheses, the displayed bracket with a fourth iterate satisfies the auxiliary recurrence identity. -/
theorem auxiliaryRecurrenceIdentityOne (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅distinguishedElement k 4 0, iterateBracket k 4 (auxiliaryCompanionFamily k m)⁆
      = -((2 : k) • iterateBracket k 1 (auxiliarySequence k m)) + auxiliaryCentralFamily k m := by
  have key : ⁅distinguishedElement k 4 0, iterateBracket k 4 (auxiliaryCompanionFamily k m)⁆
      = -((4 : k) • iterateBracket k 1 (auxiliarySequence k m)) + ⁅distinguishedElement k 4 4, auxiliaryCompanionFamily k m⁆ := by
    cases m with
    | zero =>
        have hd : iterateBracket k 1 (auxiliarySequence k 0) = ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆ := iterateBracket_one_auxiliarySequence_zero
        have h04 : ⁅distinguishedElement k 4 0, distinguishedElement k 4 4⁆ = -((2 : k) • ⁅distinguishedElement k 4 1, distinguishedElement k 4 3⁆) := by
          rw [← two_smul_iterateBracket_one_bracket]
          have hneg : iterateBracket k 1 ⁅distinguishedElement k 4 0, distinguishedElement k 4 3⁆ = -iterateBracket k 1 (auxiliarySequence k 0) := by
            rw [auxiliarySequence_zero, iterateBracket_neg, neg_neg]
          rw [hneg, hd, smul_neg]
        rw [auxiliaryCompanionFamily_zero, iterateBracket_initialElement, ← displayed_eq_aux2 k 4, bracket_generatorFour_generatorZero, hd, h04]
        module
    | succ m => exact (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityTen h2 h3
  rw [key, auxiliaryCentralFamily]
  module

/-- Under the stated nonvanishing hypotheses, the zeroth indexed element has zero bracket with every auxiliary sequence element. -/
theorem bracket_generatorZero_auxiliarySequence_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    ⁅distinguishedElement k 4 0, auxiliarySequence k m⁆ = 0 :=
  (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityNine

/-- Under the stated nonvanishing hypotheses, the displayed bracket with a first iterate advances the auxiliary companion family. -/
theorem auxiliaryRecurrenceIdentityTwo (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : ⁅distinguishedElement k 4 0, iterateBracket k 1 (auxiliarySequence k m)⁆ = auxiliaryCompanionFamily k (m + 1) :=
  (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityEleven

/-- Under the stated nonvanishing hypotheses, twice the displayed bracket with a second iterate equals the first iterate of the successor companion-family element. -/
theorem two_smul_bracket_generatorZero_iterateBracket_two (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) : (2 : k) • ⁅distinguishedElement k 4 0, iterateBracket k 2 (auxiliarySequence k m)⁆ = iterateBracket k 1 (auxiliaryCompanionFamily k (m + 1)) :=
  (auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryBracketIdentityTwentyThree

/-- Under the stated nonvanishing hypotheses, the auxiliary set spans the entire displayed Lie algebra. -/
theorem span_auxiliarySpanningSet_eq_top (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    Submodule.span k (auxiliarySpanningSet k) = ⊤ := by
  have hF : ∀ I : AuxiliaryIndex, indexedFamily k I ∈ Submodule.span k (auxiliarySpanningSet k) := fun I =>
    Submodule.subset_span (indexedFamily_mem_auxiliarySet I)
  have hW : ∀ m : ℕ, auxiliaryCentralFamily k m ∈ Submodule.span k (auxiliarySpanningSet k) := fun m =>
    Submodule.subset_span (auxiliaryCentralFamily_mem_auxiliarySpanningSet m)
  refine submodule_eq_aux2 k 4 (auxiliarySpanningSet k)
    (indexedFamily_mem_auxiliarySet (AuxiliaryIndex.odd 0 0)) (indexedFamily_mem_auxiliarySet AuxiliaryIndex.base) ?_ ?_
  · rintro s hs
    rcases eq_indexedFamily_or_eq_auxiliaryCentralFamily_of_mem hs with ⟨I, rfl⟩ | ⟨m, rfl⟩
    · cases I with
      | base =>
          change ⁅distinguishedElement k 4 0, distinguishedElement_aux8 k 4⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
          have hb : ⁅distinguishedElement k 4 0, distinguishedElement_aux8 k 4⁆ = -iterateBracket k 1 (auxiliaryCompanionFamily k 0) := by
            rw [auxiliaryCompanionFamily_zero, iterateBracket_one, displayed_eq_aux2, ← lie_skew]
          rw [hb]
          exact neg_mem (hF (AuxiliaryIndex.odd 0 1))
      | odd m i =>
          fin_cases i
          · change ⁅distinguishedElement k 4 0, auxiliaryCompanionFamily k m⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [bracket_generatorZero_auxiliaryCompanionFamily_eq_zero h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅distinguishedElement k 4 0, iterateBracket k 1 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [auxiliaryRecurrenceIdentityThree h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅distinguishedElement k 4 0, iterateBracket k 2 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [auxiliaryRecurrenceIdentityFive h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅distinguishedElement k 4 0, iterateBracket k 3 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [auxiliaryRecurrenceIdentityFour h2 h3 h5 m]
            exact neg_mem (hF (AuxiliaryIndex.even m 0))
          · change ⁅distinguishedElement k 4 0, iterateBracket k 4 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [auxiliaryRecurrenceIdentityOne h2 h3 h5 m]
            exact add_mem (neg_mem (Submodule.smul_mem _ _ (hF (AuxiliaryIndex.even m 1)))) (hW m)
      | even m i =>
          fin_cases i
          · change ⁅distinguishedElement k 4 0, auxiliarySequence k m⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [bracket_generatorZero_auxiliarySequence_eq_zero h2 h3 h5 m]
            exact Submodule.zero_mem _
          · change ⁅distinguishedElement k 4 0, iterateBracket k 1 (auxiliarySequence k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [auxiliaryRecurrenceIdentityTwo h2 h3 h5 m]
            exact hF (AuxiliaryIndex.odd (m + 1) 0)
          · change ⁅distinguishedElement k 4 0, iterateBracket k 2 (auxiliarySequence k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            have hhalf : ⁅distinguishedElement k 4 0, iterateBracket k 2 (auxiliarySequence k m)⁆
                = (2 : k)⁻¹ • iterateBracket k 1 (auxiliaryCompanionFamily k (m + 1)) := by
              rw [← two_smul_bracket_generatorZero_iterateBracket_two h2 h3 h5 m, smul_smul,
                inv_mul_cancel₀ h2, one_smul]
            rw [hhalf]
            exact Submodule.smul_mem _ _ (hF (AuxiliaryIndex.odd (m + 1) 1))
    · change ⁅distinguishedElement_aux7 k 4, auxiliaryCentralFamily k m⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
      rw [bracket_auxiliaryCentralFamily_eq_zero h2 h3 h5 m]
      exact Submodule.zero_mem _
  · rintro s hs
    rcases eq_indexedFamily_or_eq_auxiliaryCentralFamily_of_mem hs with ⟨I, rfl⟩ | ⟨m, rfl⟩
    · cases I with
      | base =>
          change ⁅distinguishedElement_aux8 k 4, distinguishedElement_aux8 k 4⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
          rw [lie_self]
          exact Submodule.zero_mem _
      | odd m i =>
          fin_cases i
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 0 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            exact hF (AuxiliaryIndex.odd m 1)
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 1 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            exact hF (AuxiliaryIndex.odd m 2)
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 2 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            exact hF (AuxiliaryIndex.odd m 3)
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 3 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            exact hF (AuxiliaryIndex.odd m 4)
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 4 (auxiliaryCompanionFamily k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            rw [show iterateBracket k (4 + 1) (auxiliaryCompanionFamily k m) = iterateBracket k 5 (auxiliaryCompanionFamily k m) from rfl,
              iterateBracket_five_auxiliaryFamily_eq_zero h2 h3 h5 m]
            exact Submodule.zero_mem _
      | even m i =>
          fin_cases i
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 0 (auxiliarySequence k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            exact hF (AuxiliaryIndex.even m 1)
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 1 (auxiliarySequence k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            exact hF (AuxiliaryIndex.even m 2)
          · change ⁅distinguishedElement_aux8 k 4, iterateBracket k 2 (auxiliarySequence k m)⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
            rw [← iterateBracket_succ]
            rw [show iterateBracket k (2 + 1) (auxiliarySequence k m) = iterateBracket k 3 (auxiliarySequence k m) from rfl,
              iterateBracket_three_auxiliarySequence_eq_zero h2 h3 h5 m]
            exact Submodule.zero_mem _
    · change ⁅distinguishedElement_aux8 k 4, auxiliaryCentralFamily k m⁆ ∈ Submodule.span k (auxiliarySpanningSet k)
      rw [bracket_auxiliaryCentralFamily_eq_zero h2 h3 h5 m]
      exact Submodule.zero_mem _

/-- If the auxiliary central family vanishes, the indexed family spans the entire displayed Lie algebra. -/
theorem span_range_indexedFamily_eq_top_of_auxiliaryCentralFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (hgap : ∀ m : ℕ, auxiliaryCentralFamily k m = 0) :
    Submodule.span k (Set.range (indexedFamily k)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_auxiliarySpanningSet_eq_top h2 h3 h5, Submodule.span_le]
  intro v hv
  rcases eq_indexedFamily_or_eq_auxiliaryCentralFamily_of_mem hv with ⟨I, rfl⟩ | ⟨m, rfl⟩
  · exact Submodule.subset_span ⟨I, rfl⟩
  · rw [hgap m]
    exact Submodule.zero_mem _

/-- Under the stated nonvanishing and trivial-center hypotheses, the indexed family spans the entire displayed Lie algebra. -/
theorem span_range_indexedFamily_eq_top_of_trivial_center (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (hZ : ∀ w : AuxiliaryType k 4, (∀ v : AuxiliaryType k 4, ⁅v, w⁆ = 0) → w = 0) :
    Submodule.span k (Set.range (indexedFamily k)) = ⊤ :=
  span_range_indexedFamily_eq_top_of_auxiliaryCentralFamily_eq_zero h2 h3 h5 fun m => hZ _ (bracket_auxiliaryCentralFamily_eq_zero h2 h3 h5 m)

/-- There is exactly one displayed index of degree zero. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
theorem card_degree_zero : Nat.card {I : AuxiliaryIndex // I.toNat = 0} = 1 := by
  have hbij : Function.Bijective
      (fun _ : Unit => (⟨AuxiliaryIndex.base, rfl⟩ : {I : AuxiliaryIndex // I.toNat = 0})) := by
    refine ⟨fun a b _ => Subsingleton.elim a b, ?_⟩
    rintro ⟨I, hI⟩
    cases I with
    | base => exact ⟨(), rfl⟩
    | odd m i => rw [AuxiliaryIndex.toNat] at hI; omega
    | even m i => rw [AuxiliaryIndex.toNat] at hI; omega
  simpa using (Nat.card_eq_of_bijective _ hbij).symm

/-- There are exactly five displayed indices of degree `2 * m + 1`. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
theorem card_degree_two_mul_add_one (m : ℕ) : Nat.card {I : AuxiliaryIndex // I.toNat = 2 * m + 1} = 5 := by
  have hbij : Function.Bijective
      (fun i : Fin 5 => (⟨AuxiliaryIndex.odd m i, rfl⟩ : {I : AuxiliaryIndex // I.toNat = 2 * m + 1})) := by
    refine ⟨fun i j hij => by simpa using hij, ?_⟩
    rintro ⟨I, hI⟩
    cases I with
    | base => rw [AuxiliaryIndex.toNat] at hI; omega
    | odd m' i =>
        have hm : m' = m := by rw [AuxiliaryIndex.toNat] at hI; omega
        subst hm
        exact ⟨i, rfl⟩
    | even m' i => rw [AuxiliaryIndex.toNat] at hI; omega
  simpa using (Nat.card_eq_of_bijective _ hbij).symm

/-- There are exactly three displayed indices of degree `2 * m + 2`. -/
@[source_ref "Chapter2/Problem2.16.3" (role := supporting)]
theorem card_degree_two_mul_add_two (m : ℕ) : Nat.card {I : AuxiliaryIndex // I.toNat = 2 * m + 2} = 3 := by
  have hbij : Function.Bijective
      (fun i : Fin 3 => (⟨AuxiliaryIndex.even m i, rfl⟩ : {I : AuxiliaryIndex // I.toNat = 2 * m + 2})) := by
    refine ⟨fun i j hij => by simpa using hij, ?_⟩
    rintro ⟨I, hI⟩
    cases I with
    | base => rw [AuxiliaryIndex.toNat] at hI; omega
    | odd m' i => rw [AuxiliaryIndex.toNat] at hI; omega
    | even m' i =>
        have hm : m' = m := by rw [AuxiliaryIndex.toNat] at hI; omega
        subst hm
        exact ⟨i, rfl⟩
  simpa using (Nat.card_eq_of_bijective _ hbij).symm

end Spanning

end RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus

attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.negBracketWithGeneratorOne
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracketWithGeneratorThree
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryCondition.auxiliaryTransform
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily
  RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySpanningSet

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.BigradedComponents
import RepresentationTheory.Alignment.Attribute

/-! # Bracket Relations -/

namespace RepresentationTheory.GradedLieAlgebra.BracketRelations

section Leibniz

variable (k : Type*) [CommRing k]

/-- The first component map preserves the Lie bracket. -/
theorem componentOne_bracket (u v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 ⁅u, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 u, v⁆ + ⁅u, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 v⁆ := by
  simp only [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one]
  exact leibniz_lie _ _ _

/-- Expands the second component of a bracket using first and second components. -/
theorem componentTwo_bracket (u v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 ⁅u, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 u, v⁆ + (2 : k) • ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 u, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 v⁆ + ⁅u, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 v⁆ := by
  have e : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 ⁅u, v⁆) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 ⁅u, v⁆ := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 1 _
  have eu : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 u) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 u := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 1 _
  have ev : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 v) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 v := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 1 _
  rw [← e, componentOne_bracket, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_add_apply, componentOne_bracket, componentOne_bracket, eu, ev]
  module

/-- Expands the third component of a bracket using the lower components. -/
theorem componentThree_bracket (u v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 3 ⁅u, v⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 3 u, v⁆ + (3 : k) • ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 u, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 v⁆
      + (3 : k) • ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 u, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 v⁆ + ⁅u, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 3 v⁆ := by
  have e : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 ⁅u, v⁆) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 3 ⁅u, v⁆ := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 2 _
  have eu : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 u) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 3 u := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 2 _
  have ev : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 v) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 3 v := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 2 _
  have eu1 : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 u) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 u := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 1 _
  have ev1 : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 v) = _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 v := _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply k 1 _
  rw [← e, componentTwo_bracket, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_add_apply, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_add_apply, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_smul, componentOne_bracket, componentOne_bracket, componentOne_bracket,
    eu, ev, eu1, ev1]
  module

end Leibniz

section Bot

variable {k : Type*} [Field k]

/-- An element in a component equal to bottom is zero. -/
theorem eq_zero_of_mem_bot_component {p : ℕ × ℕ} {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4} (h : _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p = ⊥)
    (hu : u ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p) : u = 0 := by
  rw [h] at hu
  simpa using hu

/-- The indicated even-indexed component is bottom outside its displayed range. -/
theorem componentAt_even_two_outside_range_eq_bot (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (M r : ℕ)
    (hr : r < 4 * M + 3 ∨ 4 * M + 5 < r) : _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (2 * M + 2, r) = ⊥ := by
  refine _root_.RepresentationTheory.LieAlgebra.BigradedComponents.component_eq_bot_of_unclassified_bidegree h2 h3 h5 _ ?_ ?_
  · rintro (_ | ⟨m, i⟩ | ⟨m, i⟩) h
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedComponents.base_bideg, Prod.mk.injEq] at h; omega
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedComponents.family5_bideg, Prod.mk.injEq] at h; omega
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedComponents.family3_bideg, Prod.mk.injEq] at h
      have := i.isLt
      omega
  · intro m h
    rw [Prod.mk.injEq] at h
    omega

/-- The indicated component is bottom outside its displayed interval. -/
theorem componentAt_even_one_outside_range_eq_bot (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (M r : ℕ)
    (hr : r < 4 * M ∨ 4 * M + 4 < r) : _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (2 * M + 1, r) = ⊥ := by
  refine _root_.RepresentationTheory.LieAlgebra.BigradedComponents.component_eq_bot_of_unclassified_bidegree h2 h3 h5 _ ?_ ?_
  · rintro (_ | ⟨m, i⟩ | ⟨m, i⟩) h
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedComponents.base_bideg, Prod.mk.injEq] at h; omega
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedComponents.family5_bideg, Prod.mk.injEq] at h
      have := i.isLt
      omega
    · rw [_root_.RepresentationTheory.LieAlgebra.BigradedComponents.family3_bideg, Prod.mk.injEq] at h; omega
  · intro m h
    rw [Prod.mk.injEq] at h
    omega

end Bot

section Table

variable {k : Type*} [Field k]

/-- Any two elements of the indexed base family commute. -/
theorem bracket_baseFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (i j : ℕ) : ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j⁆ = 0 := by
  have hmem := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.distinguished_mem_component k i) (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.distinguished_mem_component k j)
  rw [show ((2 * i + 2, 4 * i + 3) + (2 * j + 2, 4 * j + 3) : ℕ × ℕ)
      = (2 * (i + j + 1) + 2, 4 * i + 4 * j + 6) by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega] at hmem
  exact eq_zero_of_mem_bot_component (componentAt_even_two_outside_range_eq_bot h2 h3 h5 _ _ (Or.inl (by omega))) hmem

/-- Any two displayed second-component elements have zero bracket. -/
theorem bracket_componentTwo_componentTwo_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (i j : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)⁆ = 0 := by
  have hmem := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.shiftSecond_mem_component k 2 (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.distinguished_mem_component k i))
    (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.shiftSecond_mem_component k 2 (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.distinguished_mem_component k j))
  rw [show ((2 * i + 2, 4 * i + 3 + 2) + (2 * j + 2, 4 * j + 3 + 2) : ℕ × ℕ)
      = (2 * (i + j + 1) + 2, 4 * i + 4 * j + 10) by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega] at hmem
  exact eq_zero_of_mem_bot_component (componentAt_even_two_outside_range_eq_bot h2 h3 h5 _ _ (Or.inr (by omega))) hmem

/-- The bracket vanishes when the sum of component indices lies outside the stated range. -/
theorem bracket_components_eq_zero_outside_degree_range (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (p q a b : ℕ) (hab : a + b < 3 ∨ 5 < a + b) :
    ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k a (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k p), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k b (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k q)⁆ = 0 := by
  have hmem := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.shiftSecond_mem_component k a (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.secondaryElement_mem_component k p))
    (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.shiftSecond_mem_component k b (_root_.RepresentationTheory.LieAlgebra.BigradedComponents.secondaryElement_mem_component k q))
  rw [show ((2 * p + 1, 4 * p + a) + (2 * q + 1, 4 * q + b) : ℕ × ℕ)
      = (2 * (p + q) + 2, 4 * p + 4 * q + (a + b)) by
    simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega] at hmem
  refine eq_zero_of_mem_bot_component (componentAt_even_two_outside_range_eq_bot h2 h3 h5 _ _ ?_) hmem
  rcases hab with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end Table

section Imaginary

variable {k : Type*} [Field k]

/-- Swapping the indices gives equal brackets between the first and second components. -/
theorem bracket_componentOne_componentTwo_swap (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (i j : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)⁆
      = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i)⁆ := by
  have h := componentThree_bracket k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i) (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)
  rw [bracket_baseFamily_eq_zero h2 h3 h5 i j, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_zero_apply,
    (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCondition_auxiliarySequence h2 h3 h5 i).auxiliaryIterate_eq_zero_three, (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCondition_auxiliarySequence h2 h3 h5 j).auxiliaryIterate_eq_zero_three] at h
  simp only [zero_lie, _root_.lie_zero, zero_add, add_zero] at h
  have hskew : ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)⁆
      = -⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i)⁆ := by
    rw [← lie_skew]
  rw [hskew] at h
  have h3' : (3 : k) • (⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)⁆
      - ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i)⁆) = 0 := by
    linear_combination (norm := module) -h
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3').resolve_left h3)

/-- Relates twice a bracket of first components to a difference of brackets with second components. -/
theorem two_smul_bracket_componentOne_eq_sub (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (i j : ℕ) :
    (2 : k) • ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)⁆
      = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i)⁆ - ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)⁆ := by
  have h := componentTwo_bracket k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i) (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j)
  rw [bracket_baseFamily_eq_zero h2 h3 h5 i j, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_zero_apply] at h
  have hskew : ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j⁆
      = -⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k j, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k i)⁆ := by
    rw [← lie_skew]
  rw [hskew] at h
  linear_combination (norm := module) -h

/-- Expresses the successor auxiliary element as a bracket of first components. -/
theorem auxFamily_succ_eq_bracket (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k (m + 1) = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0), _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)⁆ := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily_succ, (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCondition_auxiliarySequence h2 h3 h5 m).auxiliaryTransform_eq_iteratedBracket h2 h3, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_auxiliarySequence_zero]

/-- Relates twice the successor auxiliary element to a difference of two brackets. -/
theorem two_smul_auxFamily_succ_eq_sub_brackets (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    (2 : k) • _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k (m + 1)
      = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0)⁆ - ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)⁆ := by
  rw [auxFamily_succ_eq_bracket h2 h3 h5 m, two_smul_bracket_componentOne_eq_sub h2 h3 h5 0 m]

/-- Relates the first component at a successor index to an auxiliary term and a bracket. -/
theorem componentOne_succ_eq_aux_add_bracket (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k (m + 1))
      = (2 : k) • _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k (m + 1) + (2 : k) • ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)⁆ := by
  have e := congrArg (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1) (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.two_smul_bracket_sequence_zero_iterateBracket_one h2 h3 h5 m)
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_smul, componentOne_bracket, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one_apply] at e
  rw [← e, auxFamily_succ_eq_bracket h2 h3 h5 m]
  module

/-- Rewrites the first component at a successor index as a sum of two brackets. -/
theorem componentOne_succ_eq_bracket_sum (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k (m + 1))
      = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0)⁆ + ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)⁆ := by
  have h := componentOne_succ_eq_aux_add_bracket h2 h3 h5 m
  have hd := two_smul_auxFamily_succ_eq_sub_brackets h2 h3 h5 m
  rw [h]
  linear_combination (norm := module) hd

/-- Characterizes vanishing of the successor auxiliary element by equality of two brackets. -/
theorem auxFamily_succ_eq_zero_iff_brackets_eq (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k (m + 1) = 0 ↔
      ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0)⁆ = ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)⁆ := by
  rw [← sub_eq_zero (a := ⁅_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 2 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k 0)⁆),
    ← two_smul_auxFamily_succ_eq_sub_brackets h2 h3 h5 m, smul_eq_zero]
  simp [h2]

end Imaginary

end RepresentationTheory.GradedLieAlgebra.BracketRelations


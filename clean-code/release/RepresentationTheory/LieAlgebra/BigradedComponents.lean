/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.FreeBigrading
import RepresentationTheory.LieAlgebra.GradedMatrixRealization

/-! # Bigraded Components -/

namespace RepresentationTheory.LieAlgebra.BigradedComponents

section Degrees

variable (k : Type*) [CommRing k]

/-- The unary indexed operation raises the second bidegree by one. -/
theorem shiftSecondOne_mem_component {a b : ℕ}
    {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (hu : u ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a, b)) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 u ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a, b + 1) := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one]
  have := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k
    (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.degree01TargetElement_mem_targetBidegree k 4) hu
  rwa [show ((0, 1) + (a, b) : ℕ × ℕ) = (a, b + 1) by simp [Nat.add_comm]] at this

/-- The indexed operation shifts the second component of bidegree by `j`. -/
theorem shiftSecond_mem_component {a b : ℕ} (j : ℕ)
    {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (hu : u ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a, b)) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k j u ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a, b + j) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_succ,
        ← Nat.add_assoc]
      have := shiftSecondOne_mem_component k ih
      rwa [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one] at this

/-- The displayed operation raises both bidegrees by one. -/
theorem diagonalShift_mem_component {a b : ℕ}
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (hc : c ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a, b)) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.negBracketWithGeneratorOne c ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a + 1, b + 1) := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.negBracketWithGeneratorOne]
  refine neg_mem ?_
  have := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k
    (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.auxiliaryElement_mem_targetBidegree k 4 1) hc
  rwa [show ((1, 1) + (a, b) : ℕ × ℕ) = (a + 1, b + 1) by
    simp [Nat.add_comm]] at this

/-- The specified operation raises the two bidegrees by one and three. -/
theorem shiftBoth_mem_component {a b : ℕ}
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (hc : c ∈ _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a, b)) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracketWithGeneratorThree c ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 (a + 1, b + 3) := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracketWithGeneratorThree]
  have := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k
    (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.auxiliaryElement_mem_targetBidegree k 4 3) hc
  rwa [show ((1, 3) + (a, b) : ℕ × ℕ) = (a + 1, b + 3) by
    simp [Nat.add_comm]] at this

/-- The distinguished element belongs to bidegree `(2m + 2, 4m + 3)`. -/
theorem distinguished_mem_component (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4
        (2 * m + 2, 4 * m + 3) := by
  induction m with
  | zero =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence_zero]
      refine neg_mem ?_
      have := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k
        (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.auxiliaryElement_mem_targetBidegree k 4 0)
        (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.auxiliaryElement_mem_targetBidegree k 4 3)
      rwa [show ((1, 0) + (1, 3) : ℕ × ℕ) = (2 * 0 + 2, 4 * 0 + 3) by norm_num] at this
  | succ m ih =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence_succ]
      have h := shiftBoth_mem_component k (diagonalShift_mem_component k ih)
      rwa [show (2 * m + 2 + 1 + 1, 4 * m + 3 + 1 + 3) =
          (2 * (m + 1) + 2, 4 * (m + 1) + 3) by
        simp [Prod.ext_iff]; omega] at h

/-- The secondary distinguished element belongs to bidegree `(2m + 1, 4m)`. -/
theorem secondaryElement_mem_component (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k m ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4
        (2 * m + 1, 4 * m) := by
  cases m with
  | zero =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily_zero]
      simpa using
        _root_.RepresentationTheory.LieAlgebra.FreeBigrading.degree10TargetElement_mem_targetBidegree k 4
  | succ m =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily_succ]
      have h := diagonalShift_mem_component k (distinguished_mem_component k m)
      rwa [show (2 * m + 2 + 1, 4 * m + 3 + 1) =
          (2 * (m + 1) + 1, 4 * (m + 1)) by
        simp [Prod.ext_iff]; omega] at h

/-- Assigns a pair of natural-number degrees to each index. -/
def _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex → ℕ × ℕ
  | .base => (0, 1)
  | .odd m i => (2 * m + 1, 4 * m + i)
  | .even m i => (2 * m + 2, 4 * m + 3 + i)

/-- The base index has bidegree `(0, 1)`. -/
@[simp] theorem base_bideg :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.base.bideg =
      (0, 1) := rfl

/-- The five-member family has bidegree `(2m + 1, 4m + i)`. -/
@[simp] theorem family5_bideg (m : ℕ) (i : Fin 5) :
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.odd m i).bideg =
      (2 * m + 1, 4 * m + i) := rfl

/-- The three-member family has bidegree `(2m + 2, 4m + 3 + i)`. -/
@[simp] theorem family3_bideg (m : ℕ) (i : Fin 3) :
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.even m i).bideg =
      (2 * m + 2, 4 * m + 3 + i) := rfl

/-- The member indexed by one has bidegree `(2m + 2, 4m + 4)`. -/
theorem family3_one_bideg (m : ℕ) :
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.even m
      (1 : Fin 3)).bideg = (2 * m + 2, 4 * m + 4) := by
  have h : ((1 : Fin 3) : ℕ) = 1 := rfl
  rw [family3_bideg, h, Prod.mk.injEq]
  omega

/-- The bidegree assignment is injective. -/
theorem _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg_injective :
    Function.Injective
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg := by
  rintro (_ | ⟨m, i⟩ | ⟨m, i⟩) (_ | ⟨m', i'⟩ | ⟨m', i'⟩) h <;>
    simp only [base_bideg, family5_bideg, family3_bideg, Prod.mk.injEq] at h
  · rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · obtain rfl : m = m' := by omega
    obtain rfl : i = i' := Fin.ext (by omega)
    rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · obtain rfl : m = m' := by omega
    obtain rfl : i = i' := Fin.ext (by omega)
    rfl

/-- Each indexed element belongs to the component specified by its bidegree. -/
theorem indexedElement_mem_component
    (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 I.bideg := by
  cases I with
  | base => simpa using
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.degree01TargetElement_mem_targetBidegree k 4
  | odd m i =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily_family5,
        family5_bideg]
      exact shiftSecond_mem_component k (i : ℕ) (secondaryElement_mem_component k m)
  | even m i =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily_family3,
        family3_bideg]
      exact shiftSecond_mem_component k (i : ℕ) (distinguished_mem_component k m)

/-- The relation element belongs to bidegree `(2m + 2, 4m + 4)`. -/
theorem relation_mem_component (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m ∈
      _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4
        (2 * m + 2, 4 * m + 4) := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily]
  refine sub_mem ?_ (Submodule.smul_mem _ _ ?_)
  · have h := _root_.RepresentationTheory.LieAlgebra.FreeBigrading.bracket_mem_targetBidegree_add k
      (_root_.RepresentationTheory.LieAlgebra.FreeBigrading.auxiliaryElement_mem_targetBidegree k 4 4)
      (secondaryElement_mem_component k m)
    rwa [show ((1, 4) + (2 * m + 1, 4 * m) : ℕ × ℕ) =
        (2 * m + 2, 4 * m + 4) by
      simp [Prod.ext_iff]; omega] at h
  · have h := shiftSecond_mem_component k 1 (distinguished_mem_component k m)
    rwa [show (2 * m + 2, 4 * m + 3 + 1) = (2 * m + 2, 4 * m + 4) by simp] at h

end Degrees

section Imaginary

variable {k : Type*} [Field k]

/-- A set spanning every matching indexed generator spans the whole bidegree component. -/
theorem component_le_span_of_generators (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (p : ℕ × ℕ)
    (T : Set (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4))
    (hfam : ∀ I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex,
      I.bideg = p →
        _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I ∈
          Submodule.span k T)
    (hdef : ∀ m : ℕ, (2 * m + 2, 4 * m + 4) = p →
      _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m ∈
        Submodule.span k T) :
    _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p ≤
      Submodule.span k T := by
  rw [_root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree_eq_span_image_of_span_eq_top
    k p
    (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.span_auxiliarySpanningSet_eq_top
      h2 h3 h5), Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  rcases
      _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.eq_indexedFamily_or_eq_auxiliaryCentralFamily_of_mem
        hv with ⟨I, rfl⟩ | ⟨m, rfl⟩
  · by_cases hI : I.bideg = p
    · rw [_root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegreeProjection_apply_eq_self
        k (hI ▸ indexedElement_mem_component k I)]
      exact hfam I hI
    · rw [_root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegreeProjection_eq_zero_of_mem
        k (indexedElement_mem_component k I) hI]
      exact Submodule.zero_mem _
  · by_cases hm : (2 * m + 2, 4 * m + 4) = p
    · rw [_root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegreeProjection_apply_eq_self
        k (hm ▸ relation_mem_component k m)]
      exact hdef m hm
    · rw [_root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegreeProjection_eq_zero_of_mem
        k (relation_mem_component k m) hm]
      exact Submodule.zero_mem _

/-- Under the stated characteristic assumptions, every unclassified bidegree component is zero. -/
theorem component_eq_bot_of_unclassified_bidegree (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (p : ℕ × ℕ)
    (hI : ∀ I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex,
      I.bideg ≠ p)
    (hm : ∀ m : ℕ, (2 * m + 2, 4 * m + 4) ≠ p) :
    _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 p = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h := component_le_span_of_generators h2 h3 h5 p
    (∅ : Set (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4))
    (fun I hIp => absurd hIp (hI I)) (fun m hmp => absurd hmp (hm m))
  simpa using h

/-- A nonexceptional indexed bidegree component is spanned by its distinguished generator. -/
theorem component_le_span_singleton (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex)
    (hI : ∀ m : ℕ, (2 * m + 2, 4 * m + 4) ≠ I.bideg) :
    _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4 I.bideg ≤
      Submodule.span k
        {_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I} := by
  refine component_le_span_of_generators h2 h3 h5 _ _ (fun J hJ => ?_)
    (fun m hm => absurd hm (hI m))
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg_injective hJ]
  exact Submodule.mem_span_singleton_self _

/-- The exceptional bidegree component is contained in the span of the displayed pair. -/
theorem component_le_span_pair (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4
        (2 * m + 2, 4 * m + 4) ≤
      Submodule.span k
        {_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1
            (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m),
          _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m} := by
  refine component_le_span_of_generators h2 h3 h5 _ _ (fun J hJ => ?_) (fun m' hm' => ?_)
  · obtain rfl : J =
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.even m 1 :=
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg_injective
        (by rw [hJ, family3_one_bideg])
    rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily_family3]
    exact Submodule.subset_span (by simp)
  · rw [Prod.mk.injEq] at hm'
    obtain rfl : m' = m := by omega
    exact Submodule.subset_span (by simp)

/-- If the displayed relation vanishes, the exceptional component is spanned by the shifted generator. -/
theorem component_le_span_of_relation_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ)
    (h : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m = 0) :
    _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4
        (2 * m + 2, 4 * m + 4) ≤
      Submodule.span k
        {_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1
          (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)} := by
  refine component_le_span_of_generators h2 h3 h5 _ _ (fun J hJ => ?_) (fun m' hm' => ?_)
  · obtain rfl : J =
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.even m 1 :=
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg_injective
        (by rw [hJ, family3_one_bideg])
    rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily_family3]
    exact Submodule.mem_span_singleton_self _
  · rw [Prod.mk.injEq] at hm'
    obtain rfl : m' = m := by omega
    rw [h]
    exact Submodule.zero_mem _

/-- Containment of the exceptional component in the indicated span forces the displayed relation to vanish. -/
theorem relation_eq_zero_of_component_le_span (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) (m : ℕ)
    (hdim : _root_.RepresentationTheory.LieAlgebra.FreeBigrading.targetBidegree k 4
        (2 * m + 2, 4 * m + 4) ≤
      Submodule.span k
        {_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1
          (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)}) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m = 0 := by
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.1 (hdim (relation_mem_component k m))
  have h0 : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 0,
      _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m⁆ = 0 :=
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracket_auxiliaryCentralFamily_eq_zero
      h2 h3 h5 m _
  rw [← hlam, lie_smul,
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryRecurrenceIdentityTwo
      h2 h3 h5 m] at h0
  rcases smul_eq_zero.1 h0 with hz | hz
  · rw [← hlam, hz, zero_smul]
  · exact absurd hz
      (_root_.RepresentationTheory.LieAlgebra.GradedMatrixRealization.auxiliaryCompanionFamily_ne_zero
        h2 h3 (m + 1))

end Imaginary

end RepresentationTheory.LieAlgebra.BigradedComponents

attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.bideg

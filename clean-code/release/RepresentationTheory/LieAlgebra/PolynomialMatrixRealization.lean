/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus

/-! # Polynomial matrix realization -/

namespace RepresentationTheory.LieAlgebra.PolynomialMatrixRealization

open Polynomial

attribute [local instance] LieRing.ofAssociativeRing

section Centralizer

variable {k : Type*} [CommRing k]

/-- The displayed polynomial matrix has entry `X` at index `(2, 0)` and zero at every other index. -/
theorem xAtTwoZeroMatrix_apply (i j : Fin 3) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux4 k i j =
      if 2 = i ∧ 0 = j then (X : Polynomial k) else 0 := rfl

/-- The displayed matrix entry is the indicator of `(0, 1)` minus the indicator of `(1, 2)`. -/
theorem upperChainDifferenceMatrix_apply (i j : Fin 3) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux6 k i j =
      (if 0 = i ∧ 1 = j then (1 : Polynomial k) else 0)
        - (if 1 = i ∧ 2 = j then (1 : Polynomial k) else 0) := rfl

/-- A polynomial matrix whose brackets with both displayed matrices vanish is the scalar matrix determined by its `(0, 0)` entry. -/
theorem matrix_eq_scalar_of_bracket_eq_zero (P : Matrix (Fin 3) (Fin 3) (Polynomial k))
    (hX : ⁅P, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux4 k⁆ = 0)
    (hY : ⁅P, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux6 k⁆ = 0) :
    P = Matrix.scalar (Fin 3) (P 0 0) := by
  have eX : ∀ i j : Fin 3,
      (P * _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux4 k -
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux4 k * P) i j = 0 := by
    intro i j
    have := congrFun (congrFun hX i) j
    simpa [LieRing.of_associative_ring_bracket] using this
  have eY : ∀ i j : Fin 3,
      (P * _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux6 k -
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux6 k * P) i j = 0 := by
    intro i j
    have := congrFun (congrFun hY i) j
    simpa [LieRing.of_associative_ring_bracket] using this
  have h02 : P 0 2 = 0 := by have := eX 0 0; simpa [Matrix.mul_apply, xAtTwoZeroMatrix_apply] using this
  have h12 : P 1 2 = 0 := by have := eX 1 0; simpa [Matrix.mul_apply, xAtTwoZeroMatrix_apply] using this
  have h01 : P 0 1 = 0 := by have := eX 2 1; simpa [Matrix.mul_apply, xAtTwoZeroMatrix_apply] using this
  have h22 : P 2 2 = P 0 0 := by
    have h : P 2 2 * X = X * P 0 0 := by
      have := eX 2 0
      simpa [Matrix.mul_apply, xAtTwoZeroMatrix_apply, sub_eq_zero] using this
    have h' : (P 2 2 - P 0 0) * X = 0 := by linear_combination h
    simpa [sub_eq_zero] using h'
  have h10 : P 1 0 = 0 := by have := eY 0 0; simpa [Matrix.mul_apply, upperChainDifferenceMatrix_apply] using this
  have h20 : P 2 0 = 0 := by have := eY 1 0; simpa [Matrix.mul_apply, upperChainDifferenceMatrix_apply] using this
  have h21 : P 2 1 = 0 := by have := eY 2 2; simpa [Matrix.mul_apply, upperChainDifferenceMatrix_apply] using this
  have h11 : P 0 0 = P 1 1 := by
    have := eY 0 1
    simpa [Matrix.mul_apply, upperChainDifferenceMatrix_apply, sub_eq_zero] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal, h02, h12, h01, h22, h10, h20, h21, h11]

end Centralizer

section CentreLoopPos

variable {k : Type*} [Field k]

/-- A matrix in the displayed set is zero if its brackets with both distinguished matrices vanish. -/
theorem eq_zero_of_mem_auxiliarySet_and_bracket_eq_zero (h3 : (3 : k) ≠ 0)
    {P : Matrix (Fin 3) (Fin 3) (Polynomial k)}
    (hP : P ∈ _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k)
    (hX : ⁅P, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux4 k⁆ = 0)
    (hY : ⁅P, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux6 k⁆ = 0) : P = 0 := by
  have hscal : P = Matrix.scalar (Fin 3) (P 0 0) :=
    matrix_eq_scalar_of_bracket_eq_zero P hX hY
  have htr : Matrix.trace P = 0 := hP.1
  rw [hscal] at htr
  have h : (3 : Polynomial k) = 0 ∨ P 0 0 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Matrix.scalar_apply] using htr
  have hzero : P 0 0 = 0 := by
    refine h.resolve_left fun hc => h3 ?_
    simpa using congrArg (fun p : Polynomial k => p.coeff 0) hc
  rw [hscal, hzero, map_zero]

end CentreLoopPos

section Gbar

variable {k : Type*} [Field k]

/-- On every free Lie algebra element, the displayed composite of auxiliary maps agrees with the displayed comparison map. -/
theorem auxiliaryMap_comp_apply (a : FreeLieAlgebra k (Fin 2)) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux5 k 4 a) =
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.lieHom_aux3 k a := rfl

/-- The displayed auxiliary map sends the displayed element to the polynomial matrix supported at `(2, 0)` with value `X`. -/
@[simp] theorem auxiliaryMap_apply_eq_xAtTwoZeroMatrix :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux7 k 4) =
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux4 k :=
  _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux14 k

/-- The displayed auxiliary map sends the displayed element to the matrix whose entries are the indicator of `(0, 1)` minus the indicator of `(1, 2)`. -/
@[simp] theorem auxiliaryMap_apply_eq_upperChainDifferenceMatrix :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux8 k 4) =
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux6 k :=
  _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux15 k

/-- The displayed auxiliary map sends a bracket to the bracket of the images. -/
theorem auxiliaryMap_bracket
    (u v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k ⁅u, v⁆ =
      ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k u,
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k v⁆ := by
  obtain ⟨a, rfl⟩ := _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_surjective k 4 u
  obtain ⟨b, rfl⟩ := _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_surjective k 4 v
  rw [← LieHom.map_lie, auxiliaryMap_comp_apply, auxiliaryMap_comp_apply,
    auxiliaryMap_comp_apply, LieHom.map_lie]

/-- The image of every element under the displayed auxiliary map belongs to the displayed set of matrices. -/
theorem auxiliaryMap_mem
    (u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k u ∈
      _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k := by
  obtain ⟨a, rfl⟩ := _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_surjective k 4 u
  exact _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.submodule_le k ⟨a, rfl⟩

/-- If every element has zero bracket with the given element, then its image under the displayed auxiliary map is zero. -/
theorem auxiliaryMap_eq_zero_of_forall_bracket_eq_zero (h3 : (3 : k) ≠ 0)
    {z : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (hz : ∀ v : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4,
      ⁅v, z⁆ = 0) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k z = 0 := by
  refine eq_zero_of_mem_auxiliarySet_and_bracket_eq_zero h3 (auxiliaryMap_mem z) ?_ ?_
  · rw [← auxiliaryMap_apply_eq_xAtTwoZeroMatrix (k := k), ← auxiliaryMap_bracket,
      ← lie_skew, hz, map_neg, map_zero, neg_zero]
  · rw [← auxiliaryMap_apply_eq_upperChainDifferenceMatrix (k := k), ← auxiliaryMap_bracket,
      ← lie_skew, hz, map_neg, map_zero, neg_zero]

/-- Under the stated nonvanishing hypotheses, the displayed composite vanishes on every element satisfying the displayed predicate. -/
theorem auxiliaryComposite_eq_zero_of_predicate (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (h : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryCondition k c) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k
      (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryCondition.auxiliaryTransform c) = 0 :=
  auxiliaryMap_eq_zero_of_forall_bracket_eq_zero h3
    (h.bracket_auxiliaryTransform_eq_zero h2 h3 h5)

/-- Under the stated nonvanishing and injectivity hypotheses, the displayed auxiliary value is zero whenever its input satisfies the displayed predicate. -/
theorem auxiliaryMap_eq_zero_of_predicate (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k))
    {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4}
    (h : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryCondition k c) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryCondition.auxiliaryTransform c = 0 :=
  hinj (by rw [map_zero]; exact auxiliaryComposite_eq_zero_of_predicate h2 h3 h5 h)

/-- Under the stated nonvanishing and injectivity hypotheses, the displayed predicate relates each transformed family element to its displayed auxiliary value. -/
theorem auxiliaryPredicate_transformedElement (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryPairCondition k
      (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.negBracketWithGeneratorOne
        (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m))
      (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracketWithGeneratorThree
        (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.negBracketWithGeneratorOne
          (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m))) :=
  _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryPairCondition.of_auxiliaryCondition_and_transform_eq_zero
    h2 h3
    (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCondition_auxiliarySequence
      h2 h3 h5 m)
    (auxiliaryMap_eq_zero_of_predicate h2 h3 h5 hinj
      (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCondition_auxiliarySequence
        h2 h3 h5 m))

/-- Under the stated nonvanishing and injectivity hypotheses, the displayed iterated bracket is zero for every natural-number index. -/
theorem auxiliaryIteratedBracket_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) (m : ℕ) :
    ⁅⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 1,
        _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 3⁆,
      _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1
        (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)⁆ = 0 := by
  have h :=
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCondition_auxiliarySequence
      h2 h3 h5 m
  rw [← h.auxiliaryTransform_eq_iteratedBracket h2 h3]
  exact auxiliaryMap_eq_zero_of_predicate h2 h3 h5 hinj h

/-- Under the stated nonvanishing and injectivity hypotheses, every member of the displayed auxiliary family is zero. -/
theorem auxiliaryFamily_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily k m = 0 := by
  cases m with
  | zero =>
      exact _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCentralFamily_zero
  | succ m =>
      exact auxiliaryMap_eq_zero_of_predicate h2 h3 h5 hinj
        (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCondition_auxiliarySequence
          h2 h3 h5 m)

/-- Under the stated nonvanishing and injectivity hypotheses, the displayed predicate holds for the two indexed auxiliary family elements. -/
theorem auxiliaryPredicate_familyPair (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.AuxiliaryPairCondition k
      (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k m)
      (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m) :=
  _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryPairCondition_companion_sequence
    h2 h3 h5 (auxiliaryFamily_eq_zero h2 h3 h5 hinj) m

/-- Under the stated nonvanishing and injectivity hypotheses, the range of the displayed family spans the entire module. -/
theorem span_range_auxiliaryFamily_eq_top (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (hinj : Function.Injective
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k)) :
    Submodule.span k
      (Set.range (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k)) = ⊤ :=
  _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.span_range_indexedFamily_eq_top_of_auxiliaryCentralFamily_eq_zero
    h2 h3 h5 (auxiliaryFamily_eq_zero h2 h3 h5 hinj)

end Gbar

end RepresentationTheory.LieAlgebra.PolynomialMatrixRealization

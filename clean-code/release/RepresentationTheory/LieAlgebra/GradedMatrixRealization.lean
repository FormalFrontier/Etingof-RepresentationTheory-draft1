/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.PolynomialMatrixRealization

/-! # Graded matrix realization -/

namespace RepresentationTheory.LieAlgebra.GradedMatrixRealization

attribute [local instance] LieRing.ofAssociativeRing

section BracketTable

variable (k : Type*) [CommRing k]

/-- The bracket of five-index family elements one and four is the displayed three-index family element two. -/
theorem bracket_family5_one_four : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4⁆ = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2 := by
  rw [← lie_skew, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux4, ← neg_smul, neg_neg]

/-- An auxiliary statement whose formal type is unavailable in this packet. -/
theorem auxiliary_fact_aux4 : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3⁆ = (-2 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply] ; ring

/-- The bracket of five-index family element three with three-index family element two is twice five-index family element four. -/
theorem bracket_family5_three_family3_two : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2⁆ = (2 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4 := by
  rw [← lie_skew, auxiliary_fact_aux4, ← neg_smul, neg_neg]

/-- The bracket of three-index family elements zero and two is family element one. -/
theorem bracket_family3_zero_two : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2⁆ = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]

/-- An auxiliary statement whose formal type is unavailable in this packet. -/
theorem auxiliary_fact_aux3 : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1⁆ = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply, Matrix.smul_apply]

/-- The bracket of three-index family element zero with itself is zero. -/
theorem bracket_family3_zero_self : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0⁆ = 0 := lie_self _

/-- The bracket of three-index family element zero with five-index family element zero is zero. -/
theorem bracket_family3_zero_family5_zero : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 0⁆ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply]

end BracketTable

section Generators

variable {k : Type*} [Field k]

/-- The bracket of scalar multiples of graded matrix images is the product scalar times the image at the sum grade of the matrix bracket. -/
theorem bracket_gradedMatrixMap {m n : ℕ} {c d : k} {A B : Matrix (Fin 3) (Fin 3) k} :
    ⁅c • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k m A, d • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n B⁆ = (c * d) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (m + n) ⁅A, B⁆ := by
  rw [lie_smul, smul_lie, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, smul_smul, ← map_smul, ← map_smul, mul_comm d c]

/-- The realization of the displayed initial element is the grade-zero image of the indicated three-index family element. -/
theorem realizationMap_initialElement : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux8 k 4) = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 0 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0) := by
  rw [_root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_apply_eq_upperChainDifferenceMatrix, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux1, one_smul]

/-- The realization of the indexed element at zero is the grade-one image of the displayed five-index family element. -/
theorem realizationMap_indexZero : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 0) = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 1 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) := by
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.displayed_eq_aux2, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_apply_eq_xAtTwoZeroMatrix, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply, one_smul]

/-- The realization of one bracket iterate is obtained by bracketing the representing matrix with the displayed three-index family element. -/
theorem realizationMap_iterateBracket_one {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4} {n : ℕ} {d : k} {A : Matrix (Fin 3) (Fin 3) k}
    (hu : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k u = d • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n A) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 u) = d • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, A⁆ := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_bracket, hu, realizationMap_initialElement, bracket_gradedMatrixMap, one_mul, Nat.zero_add]

/-- If an element realizes as a scalar multiple of a graded matrix, then every iterate realizes as the same scalar multiple of the corresponding iterated matrix bracket. -/
theorem realizationMap_iterateBracket {u : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4} {n : ℕ} {d : k} {A : Matrix (Fin 3) (Fin 3) k}
    (hu : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k u = d • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n A) (j : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k j u) = d • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n ((fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[j] A) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_succ, ← _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_one, realizationMap_iterateBracket_one ih, Function.iterate_succ_apply']

/-- The realization of the displayed indexed element is the grade-one matrix image of the corresponding iterated bracket. -/
theorem realizationMap_indexedIterate (j : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 j) = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 1 ((fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[j] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4)) := by
  have h := realizationMap_iterateBracket (realizationMap_indexZero (k := k)) j
  rwa [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.displayed_eq_aux2, _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket_initialElement] at h

/-- An auxiliary statement whose formal type is unavailable in this packet. -/
theorem auxiliary_fact_aux2 : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 1) = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 1 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3) := by
  rw [realizationMap_indexedIterate, Function.iterate_one, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux6, map_smul, smul_smul, one_mul]

/-- The realization of the indexed element at three is three times the grade-one image of the displayed five-index family element. -/
theorem realizationMap_indexThree : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement k 4 3) = (3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 1 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1) := by
  have h : (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[3] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) = (3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1 := by
    change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4⁆⁆⁆ = (3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1
    rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux6, lie_smul, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux34, lie_smul, lie_smul, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux5,
      smul_smul, smul_smul]
    norm_num
  rw [realizationMap_indexedIterate, h, map_smul, smul_smul]
  norm_num

end Generators

section Tower

variable {k : Type*} [Field k]

/-- Under the displayed realization hypothesis, the negated bracket transform realizes as twice the next graded image of the indicated five-index family element. -/
theorem realizationMap_negBracketTransform {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4} {n : ℕ} {d : k}
    (hc : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k c = d • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2)) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.negBracketWithGeneratorOne c) = (2 * d) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (n + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.negBracketWithGeneratorOne, map_neg, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_bracket, hc, auxiliary_fact_aux2, bracket_gradedMatrixMap, bracket_family5_three_family3_two,
    map_smul, smul_smul, Nat.add_comm 1 n, ← neg_smul]
  congr 1
  ring

/-- Under the displayed realization hypothesis, the auxiliary bracket transform realizes as three times the next graded image of the indicated three-index family element. -/
theorem realizationMap_bracketWithGeneratorThree {b : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryType k 4} {n : ℕ} {d : k}
    (hb : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k b = d • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4)) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracketWithGeneratorThree b) = (3 * d) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (n + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2) := by
  rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.bracketWithGeneratorThree, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_bracket, hb, realizationMap_indexThree, bracket_gradedMatrixMap, bracket_family5_one_four, map_smul,
    smul_smul, Nat.add_comm 1 n, mul_one]

/-- The realization of the `m`-th auxiliary sequence element is `3 * 6^m` times the displayed grade-`2 * m + 2` matrix. -/
theorem realizationMap_auxiliarySequence (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m) = (3 * (6 : k) ^ m) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * m + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2) := by
  induction m with
  | zero =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence_zero, map_neg, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_bracket, realizationMap_indexZero, realizationMap_indexThree,
        bracket_gradedMatrixMap, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux4, map_smul, smul_smul, ← neg_smul]
      norm_num
  | succ m ih =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence_succ, realizationMap_bracketWithGeneratorThree (realizationMap_negBracketTransform ih)]
      have hdeg : 2 * m + 2 + 1 + 1 = 2 * (m + 1) + 2 := by ring
      rw [hdeg]
      congr 1
      rw [pow_succ]
      ring

/-- The realization of the `m`-th auxiliary companion-family element is `6^m` times the displayed grade-`2 * m + 1` matrix. -/
theorem realizationMap_auxiliaryCompanionFamily (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k m) = ((6 : k) ^ m) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * m + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) := by
  cases m with
  | zero => rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily_zero, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_apply_eq_xAtTwoZeroMatrix, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply]; norm_num
  | succ m =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily_succ, realizationMap_negBracketTransform (realizationMap_auxiliarySequence m)]
      have hdeg : 2 * m + 2 + 1 = 2 * (m + 1) + 1 := by ring
      rw [hdeg]
      congr 1
      rw [pow_succ]
      ring

/-- The realization of the first iterate of the `m`-th auxiliary sequence element is `3 * 6^m` times the displayed grade-`2 * m + 2` matrix. -/
theorem realizationMap_iterateOne_auxiliarySequence (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m))
      = (3 * (6 : k) ^ m) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * m + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1) := by
  rw [realizationMap_iterateBracket_one (realizationMap_auxiliarySequence m), bracket_family3_zero_two, map_smul, smul_smul, mul_one]

end Tower

section NonVanishing

variable {k : Type*} [Field k]

/-- For every grade, the displayed matrix map sends a matrix to zero exactly when the matrix itself is zero. -/
theorem gradedMatrixMap_apply_eq_zero_iff (n : ℕ) (A : Matrix (Fin 3) (Fin 3) k) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k n A = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have hz : ∀ a b, Polynomial.monomial n (A a b) = 0 := fun a b => by
    rw [← _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux4 k n A a b, h]; simp
  ext a b
  simpa using hz a b

/-- Every member of the displayed five-index family is nonzero over a field. -/
theorem family5_ne_zero (i : Fin 5) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k i ≠ 0 := (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearIndependent_family_aux4 k).ne_zero i

/-- Every member of the displayed three-index family is nonzero over a field. -/
theorem family3_ne_zero (i : Fin 3) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k i ≠ 0 := (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearIndependent_family_aux5 k).ne_zero i

/-- In a field where two and three are nonzero, six is nonzero. -/
theorem six_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) : (6 : k) ≠ 0 := by
  have : (6 : k) = 2 * 3 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h3

/-- When two and three are nonzero, every element of the auxiliary companion family is nonzero. -/
theorem auxiliaryCompanionFamily_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (m : ℕ) : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k m ≠ 0 := by
  intro h
  have hg : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliaryCompanionFamily k m) = 0 := by rw [h, map_zero]
  rw [realizationMap_auxiliaryCompanionFamily] at hg
  rcases smul_eq_zero.1 hg with hc | hv
  · exact pow_ne_zero m (six_ne_zero h2 h3) hc
  · exact family5_ne_zero 4 ((gradedMatrixMap_apply_eq_zero_iff _ _).1 hv)

/-- When two and three are nonzero, every element of the displayed auxiliary sequence is nonzero. -/
theorem auxiliarySequence_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (m : ℕ) : _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m ≠ 0 := by
  intro h
  have hg : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m) = 0 := by rw [h, map_zero]
  rw [realizationMap_auxiliarySequence] at hg
  rcases smul_eq_zero.1 hg with hc | hv
  · exact mul_ne_zero h3 (pow_ne_zero m (six_ne_zero h2 h3)) hc
  · exact family3_ne_zero 2 ((gradedMatrixMap_apply_eq_zero_iff _ _).1 hv)

/-- When two and three are nonzero, the first iterate of every auxiliary sequence element is nonzero. -/
theorem iterateOne_auxiliarySequence_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m) ≠ 0 := by
  intro h
  have hg : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.iterateBracket k 1 (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.auxiliarySequence k m)) = 0 := by rw [h, map_zero]
  rw [realizationMap_iterateOne_auxiliarySequence] at hg
  rcases smul_eq_zero.1 hg with hc | hv
  · exact mul_ne_zero h3 (pow_ne_zero m (six_ne_zero h2 h3)) hc
  · exact family3_ne_zero 1 ((gradedMatrixMap_apply_eq_zero_iff _ _).1 hv)

end NonVanishing

section Fidelity

variable {k : Type*} [Field k]

/-- An auxiliary statement whose formal type is unavailable in this packet. -/
theorem auxiliary_fact (i : Fin 5) :
    (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[(i : ℕ)] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4)
      = (![1, -1, -1, 3, 6] : Fin 5 → k) i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k i.rev := by
  have e1 : (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[1] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3 := by
    change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4⁆ = _
    rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux6]
  have e2 : (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[2] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 2 := by
    change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4⁆⁆ = _
    simp only [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux6, lie_smul, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux34, smul_smul]
    norm_num
  have e3 : (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[3] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) = (3 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1 := by
    change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4⁆⁆⁆ = _
    simp only [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux6, lie_smul, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux34, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux5, smul_smul]
    norm_num
  have e4 : (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[4] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4) = (6 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 0 := by
    change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4⁆⁆⁆⁆ = _
    simp only [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux6, lie_smul, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux34, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux5, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux33,
      smul_smul]
    norm_num
  fin_cases i
  · simp
  · simpa using e1
  · simpa using e2
  · simpa using e3
  · simpa using e4

/-- An auxiliary statement whose formal type is unavailable in this packet. -/
theorem auxiliary_fact_aux1 (i : Fin 3) :
    (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[(i : ℕ)] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2)
      = (![1, 1, -1] : Fin 3 → k) i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k i.rev := by
  have e1 : (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[1] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2) = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1 := by
    change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2⁆ = _
    rw [bracket_family3_zero_two]
  have e2 : (fun B => ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, B⁆)^[2] (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2) = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0 := by
    change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2⁆⁆ = _
    simp only [bracket_family3_zero_two, lie_smul, auxiliary_fact_aux3, smul_smul]
    norm_num
  fin_cases i
  · simp
  · simpa using e1
  · simpa using e2

/-- The displayed involutive transformation of the auxiliary index type. -/
def indexInvolution : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex
  | .base => .base
  | .odd m i => .odd m i.rev
  | .even m i => .even m i.rev

/-- The index involution fixes the displayed base index. -/
@[simp] theorem indexInvolution_base : indexInvolution .base = .base := rfl

/-- On the displayed five-index family, the index involution reverses the finite index. -/
@[simp] theorem indexInvolution_family5 (m : ℕ) (i : Fin 5) : indexInvolution (.odd m i) = .odd m i.rev := rfl

/-- On the displayed three-index family, the index involution reverses the finite index. -/
@[simp] theorem indexInvolution_family3 (m : ℕ) (i : Fin 3) : indexInvolution (.even m i) = .even m i.rev := rfl

/-- Applying the index involution twice returns the original index. -/
theorem indexInvolution_involutive : Function.Involutive indexInvolution := by
  intro I
  cases I <;> simp

/-- The index involution is injective. -/
theorem indexInvolution_injective : Function.Injective indexInvolution := indexInvolution_involutive.injective

/-- The displayed scalar coefficient associated with an auxiliary index. -/
noncomputable def indexedCoefficient (k : Type*) [CommRing k] : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex → k
  | .base => 1
  | .odd m i => (6 : k) ^ m * (![1, -1, -1, 3, 6] : Fin 5 → k) i
  | .even m i => 3 * (6 : k) ^ m * (![1, 1, -1] : Fin 3 → k) i

/-- The realization of an indexed-family element is its displayed scalar coefficient times the corresponding matrix-family element. -/
theorem realizationMap_indexedFamily (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k I) = indexedCoefficient k I • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux13 k (indexInvolution I) := by
  cases I with
  | base => rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily_base, _root_.RepresentationTheory.LieAlgebra.PolynomialMatrixRealization.auxiliaryMap_apply_eq_upperChainDifferenceMatrix, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux1, indexedCoefficient, indexInvolution_base, one_smul]; rfl
  | odd m i =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily_family5, realizationMap_iterateBracket (realizationMap_auxiliaryCompanionFamily m) (i : ℕ), auxiliary_fact, map_smul,
        smul_smul, indexedCoefficient, indexInvolution_family5]
      rfl
  | even m i =>
      rw [_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily_family3, realizationMap_iterateBracket (realizationMap_auxiliarySequence m) (i : ℕ), auxiliary_fact_aux1, map_smul,
        smul_smul, indexedCoefficient, indexInvolution_family3]
      rfl

/-- When two and three are nonzero, every displayed indexed coefficient is nonzero. -/
theorem indexedCoefficient_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    indexedCoefficient k I ≠ 0 := by
  have h6 : (6 : k) ≠ 0 := six_ne_zero h2 h3
  cases I with
  | base => exact one_ne_zero
  | odd m i =>
      refine mul_ne_zero (pow_ne_zero m h6) ?_
      fin_cases i <;> norm_num [h3, h6]
  | even m i =>
      refine mul_ne_zero (mul_ne_zero h3 (pow_ne_zero m h6)) ?_
      fin_cases i <;> norm_num

/-- When two and three are nonzero, the realized indexed family is linearly independent. -/
theorem linearIndependent_realizationMap_indexedFamily (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    LinearIndependent k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k ∘ _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k) := by
  have hbase : LinearIndependent k (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux13 k ∘ indexInvolution) :=
    (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearIndependent_family_aux7 k).comp indexInvolution indexInvolution_injective
  have hu := hbase.units_smul fun I => Units.mk0 (indexedCoefficient k I) (indexedCoefficient_ne_zero h2 h3 I)
  have heq : ((fun I => Units.mk0 (indexedCoefficient k I) (indexedCoefficient_ne_zero h2 h3 I)) •
      (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux13 k ∘ indexInvolution)) = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k ∘ _root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k := by
    funext I
    rw [Pi.smul_apply', Function.comp_apply, Function.comp_apply, Units.smul_def,
      Units.val_mk0]
    exact (realizationMap_indexedFamily I).symm
  rwa [heq] at hu

/-- When two and three are nonzero, the displayed indexed family is linearly independent. -/
theorem linearIndependent_indexedFamily (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    LinearIndependent k (_root_.RepresentationTheory.LieAlgebra.AuxiliaryBracketCalculus.indexedFamily k) :=
  LinearIndependent.of_comp (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap_aux2 k) (linearIndependent_realizationMap_indexedFamily h2 h3)

end Fidelity

end RepresentationTheory.LieAlgebra.GradedMatrixRealization
attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexInvolution
  RepresentationTheory.LieAlgebra.GradedMatrixRealization.indexedCoefficient

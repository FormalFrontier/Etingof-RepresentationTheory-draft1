/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieAlgebra.BigradedCocycleLifts

/-! # Bigraded Pairing -/

namespace RepresentationTheory.LieAlgebra.BigradedPairing
attribute [local instance] LieRing.ofAssociativeRing

/-- The displayed compatibility relation on pairs of indices. -/
def IndexPairCompatible (I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) : Prop :=
  ∃ m : ℕ, I.bidegree + J.bidegree = (2 * m + 2, 4 * m + 4)

/-- Two indices are compatible exactly in one of the four displayed base, three-index-family, or five-index-family configurations. -/
theorem indexPairCompatible_iff (I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    IndexPairCompatible I J ↔
      (∃ m : ℕ, I = .base ∧ J = .even m 2) ∨
      (∃ m : ℕ, I = .even m 2 ∧ J = .base) ∨
      (∃ (a b : ℕ) (i j : Fin 5),
        I = .odd a i ∧ J = .odd b j ∧ (i : ℕ) + (j : ℕ) = 4) ∨
      ∃ (a b : ℕ) (i j : Fin 3),
        I = .even a i ∧ J = .even b j ∧ (i : ℕ) + (j : ℕ) = 2 := by
  cases I with
  | base =>
      cases J with
      | base => simp [IndexPairCompatible]
      | odd b j => simp [IndexPairCompatible]; omega
      | even b j =>
          fin_cases j <;> simp [IndexPairCompatible, Fin.rev] <;> omega
  | odd a i =>
      cases J with
      | base => simp [IndexPairCompatible]; omega
      | odd b j =>
          fin_cases i <;> fin_cases j <;> simp [IndexPairCompatible, Fin.rev] <;> try omega
          all_goals exact ⟨a + b, by omega⟩
      | even b j => simp [IndexPairCompatible]; omega
  | even a i =>
      cases J with
      | base =>
          fin_cases i <;> simp [IndexPairCompatible, Fin.rev]
      | odd b j => simp [IndexPairCompatible]; omega
      | even b j =>
          fin_cases i <;> fin_cases j <;> simp [IndexPairCompatible, Fin.rev] <;> try omega
          all_goals exact ⟨a + b + 1, by omega⟩

/-- A pair of indices is incompatible exactly when its bidegree sum differs from `(2 * m + 2, 4 * m + 4)` for every natural number `m`. -/
theorem forall_bidegree_add_ne_iff_not_indexPairCompatible (I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    (∀ m : ℕ, I.bidegree + J.bidegree ≠ (2 * m + 2, 4 * m + 4)) ↔
      ¬ IndexPairCompatible I J := by
  simp [IndexPairCompatible]

/-- An auxiliary ring-valued coefficient function on `Fin 5`. -/
def auxiliaryCoeff5 (k : Type*) [Ring k] : Fin 5 → k :=
  ![1, 1, 0, -1, -1]

/-- An auxiliary ring-valued coefficient function on `Fin 3`. -/
def auxiliaryCoeff3 (k : Type*) [Ring k] : Fin 3 → k :=
  ![1, 0, -1]

/-- Two indices in `Fin 5` whose values sum to four are reverses of one another. -/
theorem eq_rev_of_val_add_eq_four {i j : Fin 5}
    (hij : (i : ℕ) + (j : ℕ) = 4) : j = i.rev := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]

/-- Two indices in `Fin 3` whose values sum to two are reverses of one another. -/
theorem eq_rev_of_val_add_eq_two {i j : Fin 3}
    (hij : (i : ℕ) + (j : ℕ) = 2) : j = i.rev := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]

private theorem lie_gone1_gone3_imaginary {k : Type*} [CommRing k] :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3⁆ = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply]

/-- The bracket of a displayed five-index family element with its reverse-index element is its auxiliary coefficient times the displayed common element. -/
theorem bracket_family5_rev {k : Type*} [CommRing k] (i : Fin 5) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k i, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k i.rev⁆ = auxiliaryCoeff5 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1 := by
  fin_cases i
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (0 : Fin 5), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (4 : Fin 5)⁆ = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    rw [← lie_skew (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 0) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 4), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux3]
    simp
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (1 : Fin 5), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (3 : Fin 5)⁆ = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    simpa using lie_gone1_gone3_imaginary (k := k)
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (2 : Fin 5), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (2 : Fin 5)⁆ = (0 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    simp
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (3 : Fin 5), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (1 : Fin 5)⁆ = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    rw [← lie_skew (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 3) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k 1), lie_gone1_gone3_imaginary]
    simp
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (4 : Fin 5), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k (0 : Fin 5)⁆ = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    simpa using _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.auxiliary_fact_aux3 (k := k)

private theorem lie_gzero0_gzero2_imaginary {k : Type*} [CommRing k] :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2⁆ = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11, LieRing.of_associative_ring_bracket, Matrix.mul_apply, Matrix.single,
      Matrix.sub_apply]

/-- The bracket of a displayed three-index family element with its reverse-index element is its auxiliary coefficient times the displayed common element. -/
theorem bracket_family3_rev {k : Type*} [CommRing k] (i : Fin 3) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k i, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k i.rev⁆ = auxiliaryCoeff3 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1 := by
  fin_cases i
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k (0 : Fin 3), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k (2 : Fin 3)⁆ = (1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    simpa using lie_gzero0_gzero2_imaginary (k := k)
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k (1 : Fin 3), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k (1 : Fin 3)⁆ = (0 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    simp
  · change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k (2 : Fin 3), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k (0 : Fin 3)⁆ = (-1 : k) • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1
    rw [← lie_skew (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0), lie_gzero0_gzero2_imaginary]
    simp

/-- The bracket of two displayed five-index family elements at reverse indices is the auxiliary coefficient times the family element indexed by `a + b` at position one. -/
theorem bracket_family5_rev_index
    {k : Type*} [Field k] (a b : ℕ) (i : Fin 5) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a i), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b i.rev)⁆ =
      auxiliaryCoeff5 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b) 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k i), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * b + 1) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux10 k i.rev)⁆ =
    auxiliaryCoeff5 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * (a + b) + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, bracket_family5_rev, map_smul]
  rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + b) + 2 by omega]

/-- When two `Fin 5` indices have values summing to four, the bracket of the corresponding family elements is the auxiliary coefficient times the family element indexed by `a + b` at position one. -/
theorem bracket_family5_of_val_add_eq_four
    {k : Type*} [Field k] (a b : ℕ) (i j : Fin 5)
    (hij : (i : ℕ) + (j : ℕ) = 4) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a i), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b j)⁆ =
      auxiliaryCoeff5 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b) 1) := by
  rw [eq_rev_of_val_add_eq_four hij]
  exact bracket_family5_rev_index a b i

/-- The bracket of two displayed three-index family elements at reverse indices is the auxiliary coefficient times the family element indexed by `a + b + 1` at position one. -/
theorem bracket_family3_rev_index
    {k : Type*} [Field k] (a b : ℕ) (i : Fin 3) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even a i), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even b i.rev)⁆ =
      auxiliaryCoeff3 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b + 1) 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * a + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k i), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * b + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k i.rev)⁆ =
    auxiliaryCoeff3 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * (a + b + 1) + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17, bracket_family3_rev, map_smul]
  rw [show 2 * a + 2 + (2 * b + 2) = 2 * (a + b + 1) + 2 by omega]

/-- When two `Fin 3` indices have values summing to two, the bracket of the corresponding family elements is the auxiliary coefficient times the family element indexed by `a + b + 1` at position one. -/
theorem bracket_family3_of_val_add_eq_two
    {k : Type*} [Field k] (a b : ℕ) (i j : Fin 3)
    (hij : (i : ℕ) + (j : ℕ) = 2) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even a i), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even b j)⁆ =
      auxiliaryCoeff3 k i • _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even (a + b + 1) 1) := by
  rw [eq_rev_of_val_add_eq_two hij]
  exact bracket_family3_rev_index a b i

/-- The bracket of the displayed base indexed element with the family element at position two is the corresponding family element at position one. -/
theorem bracket_base_familyTwo
    {k : Type*} [Field k] (m : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 2)⁆ = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 1) := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket]
  change ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k 0 (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * m + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2)⁆ =
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.linearMap k (2 * m + 2) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1)
  rw [_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.bracket_eq_aux17]
  have h : ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 0, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 2⁆ = _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrix_aux11 k 1 := by
    simpa [auxiliaryCoeff3] using bracket_family3_rev (k := k) (0 : Fin 3)
  rw [h]
  rw [show 0 + (2 * m + 2) = 2 * m + 2 by omega]

/-- The bracket of the displayed family element at position two with the base indexed element is the negation of the corresponding family element at position one. -/
theorem bracket_familyTwo_base
    {k : Type*} [Field k] (m : ℕ) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 2), _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base⁆ = -_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 1) := by
  rw [← lie_skew (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 2)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base),
    bracket_base_familyTwo]

/-- An auxiliary scalar assigned to an index from a scalar sequence. -/
def sequenceCoefficient
    {k : Type*} [Zero k] (s : ℕ → k) : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex → k
  | .base => 0
  | .odd _ _ => 0
  | .even m i => if i = 1 then s m else 0

/-- A scalar-valued linear map on the displayed subtype associated with a scalar sequence when two is nonzero. -/
noncomputable def auxiliaryLinearForm
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k →ₗ[k] k :=
  (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux2 k h2).constr k (sequenceCoefficient s)

/-- The auxiliary linear form evaluated at a displayed indexed element equals its sequence coefficient. -/
@[simp] theorem auxiliaryLinearForm_apply_indexedElement
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    auxiliaryLinearForm h2 s (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) = sequenceCoefficient s I := by
  rw [auxiliaryLinearForm, ← _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.map_apply_aux6 k h2 I, Module.Basis.constr_basis]

/-- A scalar-valued auxiliary pairing on the displayed subtype, determined by a scalar sequence when two is nonzero. -/
noncomputable def auxiliaryPairing
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) :
    _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k :=
  fun a b => auxiliaryLinearForm h2 s ⁅a, b⁆

/-- The auxiliary pairing associated with a scalar sequence satisfies the displayed predicate. -/
theorem auxiliaryPairing_property
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) :
    _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.IsBinaryLieCocycle k (auxiliaryPairing h2 s) :=
  ⟨auxiliaryLinearForm h2 s, fun _ _ => rfl⟩

/-- The auxiliary pairing of the displayed base element with the indexed family element at position two equals the corresponding sequence value. -/
@[simp] theorem auxiliaryPairing_base_familyTwo
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k) (m : ℕ) :
    auxiliaryPairing h2 s (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k .base) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 2)) = s m := by
  rw [auxiliaryPairing, bracket_base_familyTwo, auxiliaryLinearForm_apply_indexedElement]
  simp [sequenceCoefficient]

/-- For complementary `Fin 5` indices, the auxiliary pairing of the two displayed family elements is the five-index coefficient times the sequence value at `a + b`. -/
theorem auxiliaryPairing_family5
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k)
    (a b : ℕ) (i j : Fin 5) (hij : (i : ℕ) + (j : ℕ) = 4) :
    auxiliaryPairing h2 s (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd a i)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.odd b j)) =
      auxiliaryCoeff5 k i * s (a + b) := by
  rw [auxiliaryPairing, bracket_family5_of_val_add_eq_four a b i j hij, map_smul,
    auxiliaryLinearForm_apply_indexedElement]
  simp [sequenceCoefficient, smul_eq_mul]

/-- For complementary `Fin 3` indices, the auxiliary pairing of the two displayed family elements is the three-index coefficient times the sequence value at `a + b + 1`. -/
theorem auxiliaryPairing_family3
    {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (s : ℕ → k)
    (a b : ℕ) (i j : Fin 3) (hij : (i : ℕ) + (j : ℕ) = 2) :
    auxiliaryPairing h2 s (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even a i)) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even b j)) =
      auxiliaryCoeff3 k i * s (a + b + 1) := by
  rw [auxiliaryPairing, bracket_family3_of_val_add_eq_two a b i j hij, map_smul,
    auxiliaryLinearForm_apply_indexedElement]
  simp [sequenceCoefficient, smul_eq_mul]

/-- The displayed submodule at an index's bidegree is the span of the corresponding indexed element. -/
theorem auxiliaryBidegreeSubmodule_eq_span {k : Type*} [Field k] (I : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) :
    _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bidegreeComponent k I.bidegree = Submodule.span k {_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨J, hJ, rfl⟩
    have hJI : J = I := _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bidegree_injective hJ
    subst J
    exact Submodule.subset_span rfl
  · exact Submodule.span_le.2 fun v hv => by
      rw [Set.mem_singleton_iff] at hv
      subst v
      exact _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.indexedElement_mem_bidegreeComponent I

/-- At bidegree `(2 * m + 2, 4 * m + 4)`, the displayed submodule is the span of the corresponding indexed family element at position one. -/
theorem auxiliaryBidegreeSubmodule_eq_span_familyOne {k : Type*} [Field k] (m : ℕ) :
    _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bidegreeComponent k (2 * m + 2, 4 * m + 4) =
      Submodule.span k {_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 1)} := by
  have hdeg : (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex.even m 1).bidegree = (2 * m + 2, 4 * m + 4) := by
    simp [Fin.rev]
  rw [← hdeg, auxiliaryBidegreeSubmodule_eq_span]

/-- Under the stated nonvanishing assumptions, if two index bidegrees sum to `(2 * m + 2, 4 * m + 4)`, then the bracket of their displayed elements belongs to the span of the corresponding family element at position one. -/
theorem bracket_mem_span_of_bidegree_add_eq
    {k : Type*} [Field k]
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex) (m : ℕ)
    (hIJ : I.bidegree + J.bidegree = (2 * m + 2, 4 * m + 4)) :
    ⁅_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I, _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J⁆ ∈
      Submodule.span k {_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k (.even m 1)} := by
  rw [← auxiliaryBidegreeSubmodule_eq_span_familyOne m, ← hIJ]
  exact _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.bracket_indexedElement_mem_bidegreeComponent_add h2 h3 h5 I J

/-- A pairing satisfying the owner's condition vanishes on two displayed indexed elements whenever their indices are not compatible. -/
theorem _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition.apply_eq_zero_of_not_compatible
    {k : Type*} [Field k] {c : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.matrixPolynomialLieSubalgebra k → k}
    (hc : _root_.RepresentationTheory.LieAlgebra.BigradedCocycleLifts.SpecialBinaryFormCondition c) {I J : _root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.AuxiliaryIndex} (hIJ : ¬ IndexPairCompatible I J) :
    c (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k I) (_root_.RepresentationTheory.LieAlgebra.ExplicitConstructions.distinguishedElement_aux3 k J) = 0 :=
  hc I J ((forall_bidegree_add_ne_iff_not_indexPairCompatible I J).2 hIJ)

end RepresentationTheory.LieAlgebra.BigradedPairing
attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.BigradedPairing.IndexPairCompatible
  RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryCoeff5
  RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryCoeff3
  RepresentationTheory.LieAlgebra.BigradedPairing.sequenceCoefficient
  RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryLinearForm
  RepresentationTheory.LieAlgebra.BigradedPairing.auxiliaryPairing

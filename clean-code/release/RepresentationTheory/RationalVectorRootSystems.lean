/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.EightDimensionalRationalVectors
import RepresentationTheory.Alignment.Attribute

/-!
# Root-system structure on distinguished rational vector sets

This file equips three finite sets of eight-dimensional rational vectors with crystallographic
root-set structures and identifies explicit vector families with finite matrix models.
-/

namespace RepresentationTheory.RationalVectorRootSystems

open Finset RepresentationTheory.EightDimensionalRationalVectors
open RepresentationTheory.FiniteIntegerMatrixModels

/-- Reflects an eight-dimensional rational vector through another such vector. -/
def reflectVector (a x : Fin 8 → ℚ) : Fin 8 → ℚ :=
  x - Auxiliary.rationalVectorPairing x a • a

/-- A predicate on sets of eight-dimensional rational vectors encoding crystallographic
root-set conditions. -/
structure IsCrystallographicRootSet (R : Set (Fin 8 → ℚ)) : Prop where
  /-- A crystallographic root set contains only finitely many vectors. -/
  finite : R.Finite
  /-- Every vector in a crystallographic root set has self-pairing equal to two. -/
  pairing_self_eq_two : ∀ a ∈ R, Auxiliary.rationalVectorPairing a a = 2
  /-- The negative of a vector in a crystallographic root set also belongs to the set. -/
  neg_mem : ∀ a ∈ R, -a ∈ R
  /-- An auxiliary consequence of the crystallographic root-set predicate. -/
  auxiliary : ∀ a ∈ R, ∀ q : ℚ, q • a ∈ R → q = 1 ∨ q = -1
  /-- The pairing of any two vectors in a crystallographic root set is an integer. -/
  pairing_integral :
    ∀ a ∈ R, ∀ b ∈ R, ∃ z : ℤ, Auxiliary.rationalVectorPairing a b = z
  /-- Reflecting one member of a crystallographic root set through another yields a member of
  the set. -/
  reflection_mem : ∀ a ∈ R, ∀ b ∈ R, reflectVector a b ∈ R

/-! ## Bilinearity of the coordinate inner product -/

/-- The rational-valued pairing is symmetric. -/
theorem rationalPairing_comm (x y : Fin 8 → ℚ) :
    Auxiliary.rationalVectorPairing x y = Auxiliary.rationalVectorPairing y x := by
  simp only [Auxiliary.rationalVectorPairing]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The rational pairing sends subtraction in its left argument to subtraction of values. -/
theorem rationalPairing_sub_left (x y z : Fin 8 → ℚ) :
    Auxiliary.rationalVectorPairing (x - y) z =
      Auxiliary.rationalVectorPairing x z - Auxiliary.rationalVectorPairing y z := by
  simp only [Auxiliary.rationalVectorPairing, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

/-- The rational pairing sends subtraction in its right argument to subtraction of values. -/
theorem rationalPairing_sub_right (x y z : Fin 8 → ℚ) :
    Auxiliary.rationalVectorPairing x (y - z) =
      Auxiliary.rationalVectorPairing x y - Auxiliary.rationalVectorPairing x z := by
  simp only [Auxiliary.rationalVectorPairing, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

/-- Scaling the left argument of the rational pairing scales its value by the same rational
number. -/
theorem rationalPairing_smul_left (q : ℚ) (x y : Fin 8 → ℚ) :
    Auxiliary.rationalVectorPairing (q • x) y =
      q * Auxiliary.rationalVectorPairing x y := by
  simp only [Auxiliary.rationalVectorPairing, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- Scaling the right argument of the rational pairing scales its value by the same rational
number. -/
theorem rationalPairing_smul_right (q : ℚ) (x y : Fin 8 → ℚ) :
    Auxiliary.rationalVectorPairing x (q • y) =
      q * Auxiliary.rationalVectorPairing x y := by
  rw [rationalPairing_comm, rationalPairing_smul_left, rationalPairing_comm x y]

/-- An auxiliary property of the rational-valued pairing. -/
theorem rationalPairing_auxiliary {a : Fin 8 → ℚ} {q : ℚ}
    (ha : Auxiliary.rationalVectorPairing a a = 2)
    (hqa : Auxiliary.rationalVectorPairing (q • a) (q • a) = 2) :
    q = 1 ∨ q = -1 := by
  rw [rationalPairing_smul_left, rationalPairing_smul_right, ha] at hqa
  apply sq_eq_one_iff.mp
  nlinarith

/-- Reflection through a vector of self-pairing two preserves the self-pairing of every
vector. -/
theorem reflection_preserves_selfPairing {a x : Fin 8 → ℚ}
    (ha : Auxiliary.rationalVectorPairing a a = 2) :
    Auxiliary.rationalVectorPairing (reflectVector a x) (reflectVector a x) =
      Auxiliary.rationalVectorPairing x x := by
  simp only [reflectVector, rationalPairing_sub_left, rationalPairing_sub_right,
    rationalPairing_smul_left, rationalPairing_smul_right, rationalPairing_comm a x, ha]
  ring

/-! ## Integrality of the distinguished vector set -/

/-- An integer-valued matrix indexed by eight row and column indices. -/
def eightVectorIntegerPairingMatrix (i j : Fin 8) : ℤ :=
  if i = j then 2 else -Auxiliary.integerMatrix i j

/-- Each entry of the eight-indexed integer matrix casts to the pairing of the corresponding
rational vectors. -/
theorem eightVectorIntegerPairingMatrix_cast (i j : Fin 8) :
    (eightVectorIntegerPairingMatrix i j : ℚ) =
      Auxiliary.rationalVectorPairing (integralBasisVector i) (integralBasisVector j) := by
  by_cases h : i = j
  · subst j
    simp only [eightVectorIntegerPairingMatrix, if_pos, Int.cast_ofNat]
    exact (integralBasisVector_pairing_self i).symm
  · rcases Auxiliary.integralBasisVector_property i j h with hij | hij
    · simp [eightVectorIntegerPairingMatrix, Auxiliary.integerMatrix, h, hij]
    · simp [eightVectorIntegerPairingMatrix, Auxiliary.integerMatrix, h, hij]

/-- Subtracting an integer multiple of one vector in the distinguished set from another stays
in the set. -/
theorem baseVectorSet_sub_int_smul_mem {x y : Fin 8 → ℚ}
    (hx : x ∈ Auxiliary.rationalVectorSetC) (hy : y ∈ Auxiliary.rationalVectorSetC)
    (z : ℤ) : x - (z : ℚ) • y ∈ Auxiliary.rationalVectorSetC := by
  obtain ⟨c, hc⟩ := rationalVectorSetC_integerSpan_characterization.1 x hx
  obtain ⟨d, hd⟩ := rationalVectorSetC_integerSpan_characterization.1 y hy
  have hmem :=
    rationalVectorSetC_integerSpan_characterization.2 (fun i => c i - z * d i)
  convert hmem using 1
  rw [hc, hd]
  simp only [Int.cast_sub, Int.cast_mul, Finset.sum_sub_distrib, sub_smul,
    mul_smul, Finset.smul_sum]

/-- The distinguished set of rational vectors is closed under negation. -/
theorem baseVectorSet_neg_mem {x : Fin 8 → ℚ} (hx : x ∈ Auxiliary.rationalVectorSetC) :
    -x ∈ Auxiliary.rationalVectorSetC := by
  simpa using
    baseVectorSet_sub_int_smul_mem
      (rationalVectorSetC_integerSpan_characterization.2 0) hx (1 : ℤ)

/-- Two vectors in the distinguished set have an integer-valued rational pairing. -/
theorem rationalPairing_integral_of_mem_baseVectorSet {x y : Fin 8 → ℚ}
    (hx : x ∈ Auxiliary.rationalVectorSetC) (hy : y ∈ Auxiliary.rationalVectorSetC) :
    ∃ z : ℤ, Auxiliary.rationalVectorPairing x y = z := by
  obtain ⟨c, rfl⟩ := rationalVectorSetC_integerSpan_characterization.1 x hx
  obtain ⟨d, rfl⟩ := rationalVectorSetC_integerSpan_characterization.1 y hy
  refine ⟨∑ i, ∑ j, c i * d j * eightVectorIntegerPairingMatrix i j, ?_⟩
  simp only [Auxiliary.rationalVectorPairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp_rw [eightVectorIntegerPairingMatrix_cast, Auxiliary.rationalVectorPairing]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## Reflection closure -/

/-- A vector in the distinguished set remains there after reflection through a vector in the
associated auxiliary set. -/
theorem reflectVector_mem_baseVectorSet_of_mem_auxiliarySet {a x : Fin 8 → ℚ}
    (ha : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC)
    (hx : x ∈ Auxiliary.rationalVectorSetC) :
    reflectVector a x ∈ Auxiliary.rationalVectorSetC := by
  obtain ⟨z, hz⟩ := rationalPairing_integral_of_mem_baseVectorSet hx ha.1
  rw [reflectVector, hz]
  exact baseVectorSet_sub_int_smul_mem hx ha.1 z

/-- The auxiliary set associated with the eight-vector data is closed under vector
reflection. -/
theorem reflectVector_mem_eightVectorAuxiliarySet {a x : Fin 8 → ℚ}
    (ha : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC)
    (hx : x ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC) :
    reflectVector a x ∈
      Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC := by
  refine ⟨reflectVector_mem_baseVectorSet_of_mem_auxiliarySet ha hx.1, ?_⟩
  rw [reflection_preserves_selfPairing ha.2, hx.2]

/-- The auxiliary set associated with the seven-vector data is closed under vector
reflection. -/
theorem reflectVector_mem_sevenVectorAuxiliarySet {a x : Fin 8 → ℚ}
    (ha : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB)
    (hx : x ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB) :
    reflectVector a x ∈
      Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB := by
  have ha8 : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC :=
    ⟨ha.1.1, ha.2⟩
  have hx8 : x ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC :=
    ⟨hx.1.1, hx.2⟩
  refine ⟨⟨(reflectVector_mem_eightVectorAuxiliarySet ha8 hx8).1, ?_⟩,
    (reflectVector_mem_eightVectorAuxiliarySet ha8 hx8).2⟩
  simp only [reflectVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ha.1.2, hx.1.2]

/-- The auxiliary set associated with the six-vector data is closed under vector
reflection. -/
theorem reflectVector_mem_sixVectorAuxiliarySet {a x : Fin 8 → ℚ}
    (ha : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA)
    (hx : x ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA) :
    reflectVector a x ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA := by
  have ha8 : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC :=
    ⟨ha.1.1, ha.2⟩
  have hx8 : x ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC :=
    ⟨hx.1.1, hx.2⟩
  refine ⟨⟨(reflectVector_mem_eightVectorAuxiliarySet ha8 hx8).1, ?_, ?_⟩,
    (reflectVector_mem_eightVectorAuxiliarySet ha8 hx8).2⟩
  · simp only [reflectVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ha.1.2.1, hx.1.2.1]
  · simp only [reflectVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ha.1.2.2, hx.1.2.2]

/-! ## Explicit compatible vector families and their finite matrix models -/

/-- A family of seven vectors with eight rational coordinates. -/
def sevenRationalVectors : Fin 7 → (Fin 8 → ℚ)
  | 0 => twoCoordinateVector 3 5 true true
  | 1 => signVector ![true, true, false, false, false, false, false, false]
  | 2 => twoCoordinateVector 0 1 false false
  | 3 => signVector ![true, true, false, false, true, true, true, true]
  | 4 => twoCoordinateVector 2 6 true false
  | 5 => twoCoordinateVector 6 7 true false
  | 6 => signVector ![true, true, true, true, false, false, true, true]

/-- A family of six vectors with eight rational coordinates. -/
def sixRationalVectors : Fin 6 → (Fin 8 → ℚ)
  | 0 => signVector ![false, false, false, true, false, true, true, true]
  | 1 => twoCoordinateVector 4 5 true false
  | 2 => twoCoordinateVector 3 4 false false
  | 3 => twoCoordinateVector 4 5 true true
  | 4 => signVector ![true, true, true, true, false, false, true, true]
  | 5 => twoCoordinateVector 3 6 true false

set_option maxRecDepth 4000 in
/-- Every member of the seven-vector family lies in the indicated auxiliary set. -/
theorem sevenRationalVectors_mem_auxiliarySet (i : Fin 7) :
    sevenRationalVectors i ∈
      Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB := by
  fin_cases i
  all_goals
    simp only [sevenRationalVectors]
    refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (3, 5, true, true) (by decide)).1
  · decide
  · exact twoCoordinateVector_pairing_self 3 5 true true (by decide)
  · exact (signVector_mem_setTransform_of_even_weight _ (by decide)).1
  · rw [signVector_apply_eq_iff]
    decide
  · exact signVector_pairing_self _
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (0, 1, false, false) (by decide)).1
  · decide
  · exact twoCoordinateVector_pairing_self 0 1 false false (by decide)
  · exact (signVector_mem_setTransform_of_even_weight _ (by decide)).1
  · rw [signVector_apply_eq_iff]
    decide
  · exact signVector_pairing_self _
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (2, 6, true, false) (by decide)).1
  · decide
  · exact twoCoordinateVector_pairing_self 2 6 true false (by decide)
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (6, 7, true, false) (by decide)).1
  · decide
  · exact twoCoordinateVector_pairing_self 6 7 true false (by decide)
  · exact (signVector_mem_setTransform_of_even_weight _ (by decide)).1
  · rw [signVector_apply_eq_iff]
    decide
  · exact signVector_pairing_self _

set_option maxRecDepth 4000 in
/-- Every member of the six-vector family lies in the indicated auxiliary set. -/
theorem sixRationalVectors_mem_auxiliarySet (i : Fin 6) :
    sixRationalVectors i ∈
      Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA := by
  fin_cases i
  all_goals
    simp only [sixRationalVectors]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact (signVector_mem_setTransform_of_even_weight _ (by decide)).1
  · rw [signVector_apply_eq_iff]
    decide
  · rw [signVector_apply_eq_iff]
    decide
  · exact signVector_pairing_self _
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (4, 5, true, false) (by decide)).1
  · decide
  · decide
  · exact twoCoordinateVector_pairing_self 4 5 true false (by decide)
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (3, 4, false, false) (by decide)).1
  · decide
  · decide
  · exact twoCoordinateVector_pairing_self 3 4 false false (by decide)
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (4, 5, true, true) (by decide)).1
  · decide
  · decide
  · exact twoCoordinateVector_pairing_self 4 5 true true (by decide)
  · exact (signVector_mem_setTransform_of_even_weight _ (by decide)).1
  · rw [signVector_apply_eq_iff]
    decide
  · rw [signVector_apply_eq_iff]
    decide
  · exact signVector_pairing_self _
  · exact (parameterRationalVector_mem_setTransform_of_ordered
      (3, 6, true, false) (by decide)).1
  · decide
  · decide
  · exact twoCoordinateVector_pairing_self 3 6 true false (by decide)

/-- Forms an integer-valued square matrix from a finite family of eight-dimensional rational
vectors. -/
def integerPairingMatrix {n : ℕ} (b : Fin n → (Fin 8 → ℚ)) (i j : Fin n) : ℤ :=
  if i = j then 0 else -(Auxiliary.rationalVectorPairing (b i) (b j)).num

/-- Expand the coordinate inner product so the finite Gram computations below are checked by
the kernel rather than by a native-code evaluator. -/
private lemma inner_eq_eight (x y : Fin 8 → ℚ) :
    Auxiliary.rationalVectorPairing x y =
      x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3
        + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7 := by
  simp only [Auxiliary.rationalVectorPairing, Fin.sum_univ_eight]

set_option maxRecDepth 10000 in
/-- The integer pairing matrix of the seven-vector family agrees entrywise with the given
adjacency matrix. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem sevenRationalVectors_integerPairingMatrix_eq_adjacency :
    ∀ i j,
      integerPairingMatrix sevenRationalVectors i j = FiniteMatrixModel.E7.matrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [integerPairingMatrix, sevenRationalVectors, twoCoordinateVector,
      twoCoordinateIntegerVector, signVector, inner_eq_eight, FiniteMatrixModel.matrix,
      Fin.reduceEq, reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    norm_num

set_option maxRecDepth 10000 in
/-- The integer pairing matrix of the six-vector family agrees entrywise with the given
adjacency matrix. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem sixRationalVectors_integerPairingMatrix_eq_adjacency :
    ∀ i j, integerPairingMatrix sixRationalVectors i j = FiniteMatrixModel.E6.matrix i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [integerPairingMatrix, sixRationalVectors, twoCoordinateVector,
      twoCoordinateIntegerVector, signVector, inner_eq_eight, FiniteMatrixModel.matrix,
      Fin.reduceEq, reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    norm_num

/-- Every member of the eight-vector family lies in the indicated auxiliary set. -/
theorem eightRationalVectors_mem_auxiliarySet (i : Fin 8) :
    integralBasisVector i ∈
      Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC := by
  refine ⟨?_, integralBasisVector_pairing_self i⟩
  have hmem :=
    rationalVectorSetC_integerSpan_characterization.2 (fun j => if j = i then 1 else 0)
  simpa only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using hmem

/-! ## The three root-system endpoints -/

private theorem neg_mem_rootsOf_E8 {a : Fin 8 → ℚ}
    (ha : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC) :
    -a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC := by
  refine ⟨baseVectorSet_neg_mem ha.1, ?_⟩
  simpa only [Auxiliary.rationalVectorPairing, Pi.neg_apply, neg_mul_neg] using ha.2

private theorem neg_mem_rootsOf_E7 {a : Fin 8 → ℚ}
    (ha : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB) :
    -a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB := by
  refine ⟨⟨baseVectorSet_neg_mem ha.1.1, ?_⟩, ?_⟩
  · simpa only [Pi.neg_apply, neg_inj] using ha.1.2
  · simpa only [Auxiliary.rationalVectorPairing, Pi.neg_apply, neg_mul_neg] using ha.2

private theorem neg_mem_rootsOf_E6 {a : Fin 8 → ℚ}
    (ha : a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA) :
    -a ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA := by
  refine ⟨⟨baseVectorSet_neg_mem ha.1.1, ?_, ?_⟩, ?_⟩
  · simpa only [Pi.neg_apply, neg_inj] using ha.1.2.1
  · simpa only [Pi.neg_apply, neg_inj] using ha.1.2.2
  · simpa only [Auxiliary.rationalVectorPairing, Pi.neg_apply, neg_mul_neg] using ha.2

/-- The auxiliary set associated with the eight-vector data satisfies the crystallographic
root-set predicate. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem eightVectorAuxiliarySet_isCrystallographicRootSet :
    IsCrystallographicRootSet
      (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC) where
  finite := Set.finite_of_ncard_ne_zero
    (by rw [ncard_setTransform_rationalVectorSetC]; norm_num)
  pairing_self_eq_two := fun _ ha => ha.2
  neg_mem := fun _ ha => neg_mem_rootsOf_E8 ha
  auxiliary := fun _ ha q hqa => rationalPairing_auxiliary ha.2 hqa.2
  pairing_integral := fun _ ha _ hb =>
    rationalPairing_integral_of_mem_baseVectorSet ha.1 hb.1
  reflection_mem := fun _ ha _ hb => reflectVector_mem_eightVectorAuxiliarySet ha hb

/-- The auxiliary set associated with the seven-vector data satisfies the crystallographic
root-set predicate. -/
theorem sevenVectorAuxiliarySet_isCrystallographicRootSet :
    IsCrystallographicRootSet
      (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB) where
  finite := Set.finite_of_ncard_ne_zero
    (by rw [ncard_setTransform_rationalVectorSetB]; norm_num)
  pairing_self_eq_two := fun _ ha => ha.2
  neg_mem := fun _ ha => neg_mem_rootsOf_E7 ha
  auxiliary := fun _ ha q hqa => rationalPairing_auxiliary ha.2 hqa.2
  pairing_integral := fun _ ha _ hb =>
    rationalPairing_integral_of_mem_baseVectorSet ha.1.1 hb.1.1
  reflection_mem := fun _ ha _ hb => reflectVector_mem_sevenVectorAuxiliarySet ha hb

/-- The auxiliary set associated with the six-vector data satisfies the crystallographic
root-set predicate. -/
theorem sixVectorAuxiliarySet_isCrystallographicRootSet :
    IsCrystallographicRootSet
      (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA) where
  finite := Set.finite_of_ncard_ne_zero
    (by rw [ncard_setTransform_rationalVectorSetA]; norm_num)
  pairing_self_eq_two := fun _ ha => ha.2
  neg_mem := fun _ ha => neg_mem_rootsOf_E6 ha
  auxiliary := fun _ ha q hqa => rationalPairing_auxiliary ha.2 hqa.2
  pairing_integral := fun _ ha _ hb =>
    rationalPairing_integral_of_mem_baseVectorSet ha.1.1 hb.1.1
  reflection_mem := fun _ ha _ hb => reflectVector_mem_sixVectorAuxiliarySet ha hb

/-! ## Type-identification capstones -/

/-- The eight-vector construction has the stated root-set, membership, matrix, and permuted
adjacency properties. -/
@[source_ref "Chapter6/Section6.9_heading" (role := supporting),
  source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem eightRationalVectors_configuration :
    IsCrystallographicRootSet
      (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC) ∧
      (∀ i, integralBasisVector i ∈
        Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC) ∧
      AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 8 Auxiliary.integerMatrix ∧
      ∃ σ : Fin 8 ≃ Fin 8,
        ∀ i j, Auxiliary.integerMatrix (σ i) (σ j) = FiniteMatrixModel.E8.matrix i j :=
  ⟨eightVectorAuxiliarySet_isCrystallographicRootSet,
    eightRationalVectors_mem_auxiliarySet, Auxiliary.integerMatrix_structure⟩

/-- The seven-vector construction simultaneously has the root-set, membership, adjacency,
and auxiliary matrix properties displayed in the type. -/
theorem sevenRationalVectors_configuration :
    IsCrystallographicRootSet
      (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB) ∧
      (∀ i, sevenRationalVectors i ∈
        Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB) ∧
      integerPairingMatrix sevenRationalVectors = FiniteMatrixModel.E7.matrix ∧
      AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 7
        (integerPairingMatrix sevenRationalVectors) := by
  have hAdj :
      integerPairingMatrix sevenRationalVectors = FiniteMatrixModel.E7.matrix := by
    funext i j
    exact sevenRationalVectors_integerPairingMatrix_eq_adjacency i j
  exact ⟨sevenVectorAuxiliarySet_isCrystallographicRootSet,
    sevenRationalVectors_mem_auxiliarySet, hAdj,
    hAdj.symm ▸ matrix_satisfies_condition .E7⟩

/-- The six-vector construction simultaneously has the root-set, membership, adjacency, and
auxiliary matrix properties displayed in the type. -/
theorem sixRationalVectors_configuration :
    IsCrystallographicRootSet
      (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA) ∧
      (∀ i, sixRationalVectors i ∈
        Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA) ∧
      integerPairingMatrix sixRationalVectors = FiniteMatrixModel.E6.matrix ∧
      AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 6
        (integerPairingMatrix sixRationalVectors) := by
  have hAdj :
      integerPairingMatrix sixRationalVectors = FiniteMatrixModel.E6.matrix := by
    funext i j
    exact sixRationalVectors_integerPairingMatrix_eq_adjacency i j
  exact ⟨sixVectorAuxiliarySet_isCrystallographicRootSet,
    sixRationalVectors_mem_auxiliarySet, hAdj,
    hAdj.symm ▸ matrix_satisfies_condition .E6⟩

end RepresentationTheory.RationalVectorRootSystems

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.RationalVectorRootSystems.Auxiliary.statement013142 := _root_.RepresentationTheory.RationalVectorRootSystems.rationalPairing_auxiliary

/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.RationalVectorRootSystems.IsCrystallographicRootSet.Auxiliary.statement013072 := _root_.RepresentationTheory.RationalVectorRootSystems.IsCrystallographicRootSet.auxiliary

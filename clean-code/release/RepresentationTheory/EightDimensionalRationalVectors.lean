/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteIntegerMatrixModels
import RepresentationTheory.Alignment.Attribute

/-!
# Eight-dimensional rational vectors

Auxiliary constructions and cardinality results for sets of eight-dimensional rational vectors.
-/

namespace RepresentationTheory.EightDimensionalRationalVectors

open Finset

/-- An auxiliary rational-valued pairing of eight-coordinate rational vectors. -/
def Auxiliary.rationalVectorPairing (x y : Fin 8 → ℚ) : ℚ := ∑ i, x i * y i

/-- A second auxiliary predicate on eight-coordinate rational vectors. -/
def Auxiliary.rationalVectorPredicateB (x : Fin 8 → ℚ) : Prop := ∀ i, ∃ n : ℤ, x i = n

/-- An auxiliary predicate on rational vectors with eight coordinates. -/
def Auxiliary.rationalVectorPredicateA (x : Fin 8 → ℚ) : Prop := ∀ i, ∃ n : ℤ, x i = (n : ℚ) + 1 / 2

/-- A third auxiliary predicate on eight-coordinate rational vectors. -/
def Auxiliary.rationalVectorPredicateC (x : Fin 8 → ℚ) : Prop := ∃ m : ℤ, (∑ i, x i) = 2 * m

/-- A third auxiliary set of rational vectors with eight coordinates. -/
def Auxiliary.rationalVectorSetC : Set (Fin 8 → ℚ) :=
  {x | (Auxiliary.rationalVectorPredicateB x ∨ Auxiliary.rationalVectorPredicateA x) ∧ Auxiliary.rationalVectorPredicateC x}

/-- An auxiliary transformation of sets of eight-coordinate rational vectors. -/
def Auxiliary.rationalVectorSetTransform (S : Set (Fin 8 → ℚ)) : Set (Fin 8 → ℚ) := {x ∈ S | Auxiliary.rationalVectorPairing x x = 2}

/-- An auxiliary rational matrix indexed by eight rows and columns. -/
def Auxiliary.rationalMatrixA (j : Fin 8) : Fin 8 → ℚ := fun i => if i = j then 1 else 0

/-- Associates a rational vector to each of eight basis indices. -/
def integralBasisVector : Fin 8 → (Fin 8 → ℚ)
  | 0 => Auxiliary.rationalMatrixA 0 - Auxiliary.rationalMatrixA 1
  | 1 => Auxiliary.rationalMatrixA 1 - Auxiliary.rationalMatrixA 2
  | 2 => Auxiliary.rationalMatrixA 2 - Auxiliary.rationalMatrixA 3
  | 3 => Auxiliary.rationalMatrixA 3 - Auxiliary.rationalMatrixA 4
  | 4 => Auxiliary.rationalMatrixA 4 - Auxiliary.rationalMatrixA 5
  | 5 => Auxiliary.rationalMatrixA 5 - Auxiliary.rationalMatrixA 6
  | 6 => Auxiliary.rationalMatrixA 5 + Auxiliary.rationalMatrixA 6
  | 7 => fun _ => -(1 / 2)

private lemma inner_eq (x y : Fin 8 → ℚ) :
    Auxiliary.rationalVectorPairing x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3
      + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7 := by
  simp only [Auxiliary.rationalVectorPairing, Fin.sum_univ_eight]

/-- An integer linear combination of the indexed rational vectors is zero only when every coefficient is zero. -/
theorem integralBasisVector_integer_independent (c : Fin 8 → ℤ)
    (h : (∑ i, (c i : ℚ) • integralBasisVector i) = 0) : c = 0 := by

  have e0 := congr_fun h 0
  have e1 := congr_fun h 1
  have e2 := congr_fun h 2
  have e3 := congr_fun h 3
  have e4 := congr_fun h 4
  have e5 := congr_fun h 5
  have e6 := congr_fun h 6
  have e7 := congr_fun h 7
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
    Pi.zero_apply] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply, Fin.reduceEq,
    reduceIte] at e0 e1 e2 e3 e4 e5 e6 e7
  norm_num at e0 e1 e2 e3 e4 e5 e6 e7

  have h7 : (c 7 : ℚ) = 0 := by exact_mod_cast e7
  have h0 : (c 0 : ℚ) = 0 := by linarith
  have h1 : (c 1 : ℚ) = 0 := by linarith
  have h2 : (c 2 : ℚ) = 0 := by linarith
  have h3 : (c 3 : ℚ) = 0 := by linarith
  have h4 : (c 4 : ℚ) = 0 := by linarith
  have h5 : (c 5 : ℚ) = 0 := by linarith
  have h6 : (c 6 : ℚ) = 0 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · exact_mod_cast h7

set_option linter.unusedSimpArgs false in

private lemma sum_α_coord (c : Fin 8 → ℤ) (k : Fin 8) :
    ∃ a : ℤ, (∑ i, (c i : ℚ) • integralBasisVector i) k = (a : ℚ) - (c 7 : ℚ) / 2 := by
  refine ⟨![c 0, c 1 - c 0, c 2 - c 1, c 3 - c 2, c 4 - c 3,
    c 5 + c 6 - c 4, c 6 - c 5, 0] k, ?_⟩
  fin_cases k <;>
    (simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
        integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val,
        Matrix.head_fin_const]
     push_cast
     ring)

set_option linter.unusedSimpArgs false in

/-- The third auxiliary set consists exactly of integer linear combinations of the indexed rational vectors. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem rationalVectorSetC_integerSpan_characterization :
    (∀ x ∈ Auxiliary.rationalVectorSetC, ∃ c : Fin 8 → ℤ, x = ∑ i, (c i : ℚ) • integralBasisVector i) ∧
    (∀ c : Fin 8 → ℤ, (∑ i, (c i : ℚ) • integralBasisVector i) ∈ Auxiliary.rationalVectorSetC) := by
  refine ⟨?_, ?_⟩
  ·
    rintro x ⟨hdisj, M, hM⟩
    rcases hdisj with hInt | hHalf
    ·
      choose n hn using hInt
      refine ⟨![n 0 - n 7, n 0 + n 1 - 2 * n 7, n 0 + n 1 + n 2 - 3 * n 7,
        n 0 + n 1 + n 2 + n 3 - 4 * n 7, n 0 + n 1 + n 2 + n 3 + n 4 - 5 * n 7,
        M - n 6 - 3 * n 7, M - 4 * n 7, -2 * n 7], ?_⟩
      have hs : (n 0 : ℚ) + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 = 2 * M := by
        have h := hM; rw [Fin.sum_univ_eight] at h; simp only [hn] at h; push_cast; linarith [h]
      funext k
      fin_cases k <;>
        (simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
            integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val,
            Matrix.head_fin_const, hn]
         push_cast
         first | linear_combination hs | ring)
    ·
      choose n hn using hHalf
      refine ⟨![n 0 - n 7, n 0 + n 1 - 2 * n 7, n 0 + n 1 + n 2 - 3 * n 7,
        n 0 + n 1 + n 2 + n 3 - 4 * n 7, n 0 + n 1 + n 2 + n 3 + n 4 - 5 * n 7,
        M - 2 - n 6 - 3 * n 7, M - 2 - 4 * n 7, -2 * n 7 - 1], ?_⟩
      have hs : (n 0 : ℚ) + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 = 2 * M - 4 := by
        have h := hM; rw [Fin.sum_univ_eight] at h; simp only [hn] at h; push_cast; linarith [h]
      funext k
      fin_cases k <;>
        (simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
            integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val,
            Matrix.head_fin_const, hn]
         push_cast
         first | linear_combination hs | ring)
  ·
    intro c
    refine ⟨?_, ?_⟩
    ·
      rcases Int.even_or_odd (c 7) with ⟨m, hm⟩ | ⟨m, hm⟩
      · left
        intro k
        obtain ⟨a, ha⟩ := sum_α_coord c k
        exact ⟨a - m, by rw [ha, hm]; push_cast; ring⟩
      · right
        intro k
        obtain ⟨a, ha⟩ := sum_α_coord c k
        exact ⟨a - m - 1, by rw [ha, hm]; push_cast; ring⟩
    ·
      refine ⟨c 6 - 2 * c 7, ?_⟩
      rw [Fin.sum_univ_eight]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_eight,
        integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte]
      push_cast; ring

/-- An auxiliary integer matrix with eight rows and columns. -/
def Auxiliary.integerMatrix (i j : Fin 8) : ℤ :=
  if i = j then 0 else -(Auxiliary.rationalVectorPairing (integralBasisVector i) (integralBasisVector j)).num

/-- Each indexed rational vector has self-pairing equal to two. -/
theorem integralBasisVector_pairing_self (i : Fin 8) : Auxiliary.rationalVectorPairing (integralBasisVector i) (integralBasisVector i) = 2 := by
  fin_cases i <;>
    simp only [inner_eq, integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply, Fin.reduceEq, reduceIte] <;>
    norm_num

/-- An auxiliary property of the indexed rational vectors and their pairing. -/
theorem Auxiliary.integralBasisVector_property (i j : Fin 8) (h : i ≠ j) :
    Auxiliary.rationalVectorPairing (integralBasisVector i) (integralBasisVector j) = 0 ∨ Auxiliary.rationalVectorPairing (integralBasisVector i) (integralBasisVector j) = -1 := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl h
      | (simp [inner_eq, integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply] <;> norm_num)

private def gramMat : Matrix (Fin 8) (Fin 8) ℤ :=
  !![(0 : ℤ),1,0,0,0,0,0,(0 : ℤ);
     (1 : ℤ),0,1,0,0,0,0,(0 : ℤ);
     (0 : ℤ),1,0,1,0,0,0,(0 : ℤ);
     (0 : ℤ),0,1,0,1,0,0,(0 : ℤ);
     (0 : ℤ),0,0,1,0,1,1,(0 : ℤ);
     (0 : ℤ),0,0,0,1,0,0,(0 : ℤ);
     (0 : ℤ),0,0,0,1,0,0,(1 : ℤ);
     (0 : ℤ),0,0,0,0,0,1,(0 : ℤ)]

private lemma gramAdj_eq : Auxiliary.integerMatrix = gramMat := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Auxiliary.integerMatrix, gramMat, inner_eq, integralBasisVector, Auxiliary.rationalMatrixA, Pi.sub_apply, Pi.add_apply,
      Fin.reduceEq, reduceIte] <;>
    norm_num

/-- An auxiliary structural property and adjacency representation for the integer matrix. -/
theorem Auxiliary.integerMatrix_structure :
    RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 8 Auxiliary.integerMatrix ∧
    ∃ σ : Fin 8 ≃ Fin 8, ∀ i j, Auxiliary.integerMatrix (σ i) (σ j) = RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix i j := by



  let σ : Fin 8 ≃ Fin 8 :=
    ⟨![7, 6, 4, 3, 2, 1, 0, 5], ![6, 5, 4, 3, 2, 7, 1, 0], by decide, by decide⟩
  have hiso : ∀ i j, Auxiliary.integerMatrix (σ i) (σ j) = RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.E8.matrix i j := by
    intro i j
    change Auxiliary.integerMatrix (σ.toFun i) (σ.toFun j) = _
    rw [gramAdj_eq]
    fin_cases i <;> fin_cases j <;> rfl
  exact ⟨RepresentationTheory.FiniteIntegerMatrixModels.matrixCondition_of_relabeling σ hiso (RepresentationTheory.FiniteIntegerMatrixModels.matrix_satisfies_condition .E8), σ, hiso⟩

/-- A second auxiliary set of rational vectors with eight coordinates. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
def Auxiliary.rationalVectorSetB : Set (Fin 8 → ℚ) := {x ∈ Auxiliary.rationalVectorSetC | x 0 = x 1}

/-- An auxiliary set of rational vectors indexed by eight coordinates. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
def Auxiliary.rationalVectorSetA : Set (Fin 8 → ℚ) := {x ∈ Auxiliary.rationalVectorSetC | x 0 = x 1 ∧ x 1 = x 2}

/-- Constructs an integer vector from two coordinates and two Boolean parameters. -/
def twoCoordinateIntegerVector (i j : Fin 8) (a b : Bool) (k : Fin 8) : ℤ :=
  (if k = i then (if a then 1 else -1) else 0) + (if k = j then (if b then 1 else -1) else 0)

/-- Constructs a rational vector from two coordinates and two Boolean parameters. -/
def twoCoordinateVector (i j : Fin 8) (a b : Bool) : Fin 8 → ℚ := fun k => (twoCoordinateIntegerVector i j a b k : ℚ)

/-- Encodes eight Boolean signs as an eight-coordinate rational vector. -/
def signVector (s : Fin 8 → Bool) : Fin 8 → ℚ := fun k => if s k then 1 / 2 else -1 / 2

/-- An auxiliary type used to parameterize vector constructions. -/
abbrev Auxiliary.parameterType := Fin 8 × Fin 8 × Bool × Bool

/-- Associates an eight-coordinate rational vector to an auxiliary parameter. -/
def Auxiliary.parameterRationalVector (p : Auxiliary.parameterType) : Fin 8 → ℚ := twoCoordinateVector p.1 p.2.1 p.2.2.1 p.2.2.2

/-- Associates an eight-coordinate integer vector to an auxiliary parameter. -/
def Auxiliary.parameterIntegerVector (p : Auxiliary.parameterType) (k : Fin 8) : ℤ := twoCoordinateIntegerVector p.1 p.2.1 p.2.2.1 p.2.2.2 k

/-- Assigns a natural-number weight to an eight-coordinate Boolean vector. -/
def boolVectorWeight (s : Fin 8 → Bool) : ℕ := (univ.filter (fun k => s k = true)).card

/-- An auxiliary property of the two-coordinate integer vector construction. -/
lemma Auxiliary.twoCoordinateIntegerVector_propertyA (i j a b) (h : i ≠ j) : twoCoordinateIntegerVector i j a b i = if a then 1 else -1 := by
  unfold twoCoordinateIntegerVector; simp [h]

/-- A second auxiliary property of the two-coordinate integer vector construction. -/
lemma Auxiliary.twoCoordinateIntegerVector_propertyB (i j a b) (h : i ≠ j) : twoCoordinateIntegerVector i j a b j = if b then 1 else -1 := by
  unfold twoCoordinateIntegerVector; simp [Ne.symm h]

/-- The constructed integer vector vanishes at coordinates distinct from both selected indices. -/
lemma twoCoordinateIntegerVector_eq_zero_of_ne (i j a b) (k) (hi : k ≠ i) (hj : k ≠ j) : twoCoordinateIntegerVector i j a b k = 0 := by
  simp only [twoCoordinateIntegerVector, if_neg hi, if_neg hj, add_zero]

/-- An auxiliary fact concerning rational vectors. -/
lemma Auxiliary.rationalVector_property (a : Bool) : (if a then (1 : ℤ) else -1) ≠ 0 := by cases a <;> decide

set_option maxRecDepth 4000 in
/-- For distinct selected indices, the sum of squared coordinates of the constructed integer vector is two. -/
lemma twoCoordinateIntegerVector_sq_sum (i j : Fin 8) (a b : Bool) (h : i ≠ j) :
    ∑ k, (twoCoordinateIntegerVector i j a b k) ^ 2 = 2 := by
  revert h; revert a b
  fin_cases i <;> fin_cases j <;> decide

/-- A two-coordinate rational vector at distinct indices has self-pairing two. -/
lemma twoCoordinateVector_pairing_self (i j : Fin 8) (a b : Bool) (h : i ≠ j) :
    Auxiliary.rationalVectorPairing (twoCoordinateVector i j a b) (twoCoordinateVector i j a b) = 2 := by
  have hh : Auxiliary.rationalVectorPairing (twoCoordinateVector i j a b) (twoCoordinateVector i j a b)
      = ((∑ k, (twoCoordinateIntegerVector i j a b k) ^ 2 : ℤ) : ℚ) := by
    simp only [Auxiliary.rationalVectorPairing, twoCoordinateVector]; push_cast; apply Finset.sum_congr rfl; intro k _; ring
  rw [hh, twoCoordinateIntegerVector_sq_sum i j a b h]; norm_num

/-- Every Boolean sign vector has self-pairing equal to two. -/
lemma signVector_pairing_self (s : Fin 8 → Bool) : Auxiliary.rationalVectorPairing (signVector s) (signVector s) = 2 := by
  have hsq : ∀ k, signVector s k * signVector s k = 1 / 4 := by
    intro k; simp only [signVector]; split_ifs <;> norm_num
  simp only [Auxiliary.rationalVectorPairing, hsq]; norm_num

/-- Each vector constructed from two indices and two Boolean values satisfies the second auxiliary predicate. -/
lemma twoCoordinateVector_satisfies_predicateB (i j a b) : Auxiliary.rationalVectorPredicateB (twoCoordinateVector i j a b) :=
  fun k => ⟨twoCoordinateIntegerVector i j a b k, rfl⟩

/-- Every rational vector encoded by Boolean signs satisfies the first auxiliary predicate. -/
lemma signVector_satisfies_predicateA (s) : Auxiliary.rationalVectorPredicateA (signVector s) := by
  intro k; simp only [signVector]
  split_ifs
  · exact ⟨0, by norm_num⟩
  · exact ⟨-1, by norm_num⟩

set_option maxRecDepth 4000 in
/-- The coordinate sum of a two-coordinate integer vector is even. -/
lemma twoCoordinateIntegerVector_sum_even (i j a b) : Even (∑ k, twoCoordinateIntegerVector i j a b k) := by
  revert a b; fin_cases i <;> fin_cases j <;> decide

/-- Every rational vector constructed from two indices and two Boolean values satisfies the third auxiliary predicate. -/
lemma twoCoordinateVector_satisfies_predicateC (i j a b) : Auxiliary.rationalVectorPredicateC (twoCoordinateVector i j a b) := by
  obtain ⟨r, hr⟩ := twoCoordinateIntegerVector_sum_even i j a b
  refine ⟨r, ?_⟩
  have hcast : (∑ k, twoCoordinateVector i j a b k) = ((∑ k, twoCoordinateIntegerVector i j a b k : ℤ) : ℚ) := by
    simp only [twoCoordinateVector]; push_cast; rfl
  rw [hcast, hr]; push_cast; ring

/-- The coordinate sum of a sign vector is its Boolean weight, cast to the rationals, minus four. -/
lemma signVector_sum_eq_weight_sub_four (s) : ∑ k, signVector s k = (boolVectorWeight s : ℚ) - 4 := by
  have hpt : ∀ k, signVector s k = (if s k = true then (1 : ℚ) else 0) - 1 / 2 := by
    intro k; simp only [signVector]; split_ifs <;> norm_num
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, boolVectorWeight]
  push_cast; ring

/-- A Boolean sign vector satisfies the third auxiliary predicate when its weight is even. -/
lemma signVector_satisfies_predicateC_of_even_weight (s) (hev : Even (boolVectorWeight s)) : Auxiliary.rationalVectorPredicateC (signVector s) := by
  obtain ⟨u, hu⟩ := hev
  exact ⟨u - 2, by rw [signVector_sum_eq_weight_sub_four, hu]; push_cast; ring⟩

/-- The third auxiliary predicate holds for a Boolean sign vector exactly when its weight is even. -/
lemma signVector_satisfies_predicateC_iff_even_weight (s) : Auxiliary.rationalVectorPredicateC (signVector s) ↔ Even (boolVectorWeight s) := by
  refine ⟨fun ⟨m, hm⟩ => ?_, signVector_satisfies_predicateC_of_even_weight s⟩
  rw [signVector_sum_eq_weight_sub_four] at hm
  have hz : (boolVectorWeight s : ℤ) = 2 * m + 4 := by
    have : (boolVectorWeight s : ℚ) = 2 * (m : ℚ) + 4 := by linarith [hm]
    exact_mod_cast this
  exact (Int.even_coe_nat _).1 ⟨m + 2, by rw [hz]; ring⟩

/-- The rational-vector encoding of Boolean signs is injective. -/
lemma signVector_injective : Function.Injective signVector := by
  intro s t h; funext k
  have hk := congr_fun h k; simp only [signVector] at hk
  rcases Bool.eq_false_or_eq_true (s k) with hs | hs <;>
    rcases Bool.eq_false_or_eq_true (t k) with ht | ht <;>
    rw [hs, ht] at hk ⊢ <;> first | rfl | (norm_num at hk)

/-- Two coordinates of a sign vector agree exactly when their Boolean signs agree. -/
lemma signVector_apply_eq_iff (s k l) : signVector s k = signVector s l ↔ s k = s l := by
  refine ⟨fun h => ?_, fun h => by rw [signVector, signVector, h]⟩
  simp only [signVector] at h
  rcases Bool.eq_false_or_eq_true (s k) with hk | hk <;>
    rcases Bool.eq_false_or_eq_true (s l) with hl | hl <;>
    rw [hk, hl] at h ⊢ <;> first | rfl | (norm_num at h)

/-- The parameterized rational-vector construction is injective when the two stored indices are increasing. -/
lemma parameterRationalVector_injOn_ordered : Set.InjOn Auxiliary.parameterRationalVector {p : Auxiliary.parameterType | p.1 < p.2.1} := by
  rintro ⟨i, j, a, b⟩ hp ⟨i', j', a', b'⟩ hp' heq
  simp only [Set.mem_setOf_eq] at hp hp'
  have hij : i ≠ j := hp.ne
  have hij' : i' ≠ j' := hp'.ne
  have hcoord : ∀ k, twoCoordinateIntegerVector i j a b k = twoCoordinateIntegerVector i' j' a' b' k := by
    intro k; have := congr_fun heq k
    simp only [Auxiliary.parameterRationalVector, twoCoordinateVector] at this; exact_mod_cast this
  have mem_i' : i' = i ∨ i' = j := by
    by_contra hc; simp only [not_or] at hc
    have h0 : twoCoordinateIntegerVector i j a b i' = 0 := twoCoordinateIntegerVector_eq_zero_of_ne i j a b i' hc.1 hc.2
    have hne : twoCoordinateIntegerVector i' j' a' b' i' ≠ 0 := by
      rw [Auxiliary.twoCoordinateIntegerVector_propertyA i' j' a' b' hij']; exact Auxiliary.rationalVector_property a'
    rw [← hcoord] at hne; exact hne h0
  have mem_j' : j' = i ∨ j' = j := by
    by_contra hc; simp only [not_or] at hc
    have h0 : twoCoordinateIntegerVector i j a b j' = 0 := twoCoordinateIntegerVector_eq_zero_of_ne i j a b j' hc.1 hc.2
    have hne : twoCoordinateIntegerVector i' j' a' b' j' ≠ 0 := by
      rw [Auxiliary.twoCoordinateIntegerVector_propertyB i' j' a' b' hij']; exact Auxiliary.rationalVector_property b'
    rw [← hcoord] at hne; exact hne h0
  have hii : i' = i := by
    rcases mem_i' with h | h
    · exact h
    · exfalso; subst h; rcases mem_j' with h2 | h2 <;> omega
  have hjj : j' = j := by
    rcases mem_j' with h | h
    · exfalso; subst hii; omega
    · exact h
  subst hii; subst hjj
  have ha : a = a' := by
    have h1 := Auxiliary.twoCoordinateIntegerVector_propertyA i' j' a b hij
    have h2 := Auxiliary.twoCoordinateIntegerVector_propertyA i' j' a' b' hij
    rw [hcoord i'] at h1; rw [h1] at h2; cases a <;> cases a' <;> simp_all
  have hb : b = b' := by
    have h1 := Auxiliary.twoCoordinateIntegerVector_propertyB i' j' a b hij
    have h2 := Auxiliary.twoCoordinateIntegerVector_propertyB i' j' a' b' hij
    rw [hcoord j'] at h1; rw [h1] at h2; cases b <;> cases b' <;> simp_all
  subst ha; subst hb; rfl

/-- No two-coordinate rational vector equals a vector encoded by Boolean signs. -/
lemma twoCoordinateVector_ne_signVector (i j a b s) : twoCoordinateVector i j a b ≠ signVector s := by
  intro h
  have h0 := congr_fun h 0
  simp only [twoCoordinateVector, signVector] at h0
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℚ) = if s 0 = true then (1 : ℚ) / 2 else -1 / 2 :=
    ⟨twoCoordinateIntegerVector i j a b 0, by rw [h0]⟩
  have : (2 * n : ℤ) = 1 ∨ (2 * n : ℤ) = -1 := by
    split_ifs at hn
    · left; have : (2 * n : ℚ) = 1 := by rw [hn]; ring
      exact_mod_cast this
    · right; have : (2 * n : ℚ) = -1 := by rw [hn]; ring
      exact_mod_cast this
  omega

/-- A vector satisfying the first predicate and having self-pairing two is encoded by Boolean signs. -/
lemma eq_signVector_of_predicateA_and_pairing_self_eq_two (x : Fin 8 → ℚ) (hHalf : Auxiliary.rationalVectorPredicateA x) (hnorm : Auxiliary.rationalVectorPairing x x = 2) :
    ∃ s : Fin 8 → Bool, x = signVector s := by
  choose n hn using hHalf
  have hgz : ∀ k, (0 : ℤ) ≤ n k * (n k + 1) := by
    intro k
    rcases lt_or_ge (n k) 0 with h | h
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -(n k) by linarith)
        (show (0 : ℤ) ≤ -(n k + 1) by linarith)]
    · exact mul_nonneg h (by linarith)
  have hge : ∀ k ∈ (univ : Finset (Fin 8)), (0 : ℚ) ≤ x k * x k - 1 / 4 := by
    intro k _
    have hc : (0 : ℚ) ≤ (n k : ℚ) * ((n k : ℚ) + 1) := by exact_mod_cast hgz k
    rw [hn k]; nlinarith [hc]
  have hsum0 : ∑ k, (x k * x k - 1 / 4) = 0 := by
    simp only [Finset.sum_sub_distrib]
    have h4 : (∑ _k : Fin 8, (1 : ℚ) / 4) = 2 := by
      rw [Finset.sum_const, card_univ]; norm_num
    rw [h4]; simp only [Auxiliary.rationalVectorPairing] at hnorm; rw [hnorm]; ring
  have heach : ∀ k ∈ (univ : Finset (Fin 8)), x k * x k - 1 / 4 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hge).1 hsum0
  refine ⟨fun k => decide (x k = 1 / 2), ?_⟩
  funext k
  have hk : x k * x k = 1 / 4 := by have := heach k (mem_univ k); linarith
  have hor : x k = 1 / 2 ∨ x k = -1 / 2 := by
    have hfac : (x k - 1 / 2) * (x k + 1 / 2) = 0 := by nlinarith [hk]
    rcases mul_eq_zero.1 hfac with h | h
    · left; linarith
    · right; linarith
  simp only [signVector]
  rcases hor with h | h <;> simp [h]

/-- A vector satisfying the second predicate with self-pairing two has a two-coordinate representation at increasing indices. -/
lemma eq_twoCoordinateVector_of_predicateB_and_pairing_self_eq_two (x : Fin 8 → ℚ) (hInt : Auxiliary.rationalVectorPredicateB x) (hnorm : Auxiliary.rationalVectorPairing x x = 2) :
    ∃ i j a b, i < j ∧ x = twoCoordinateVector i j a b := by
  choose c hc using hInt
  have hZ : ∑ k, (c k) ^ 2 = 2 := by
    have h : ((∑ k, (c k) ^ 2 : ℤ) : ℚ) = 2 := by
      push_cast; simp only [Auxiliary.rationalVectorPairing, hc] at hnorm
      rw [← hnorm]; apply Finset.sum_congr rfl; intro k _; ring
    exact_mod_cast h
  have hbound : ∀ k, c k = -1 ∨ c k = 0 ∨ c k = 1 := by
    intro k
    have hle : (c k) ^ 2 ≤ 2 := by
      have := Finset.single_le_sum (f := fun k => (c k) ^ 2)
        (fun i _ => sq_nonneg (c i)) (mem_univ k)
      rw [hZ] at this; exact this
    have h4 : (c k) ^ 2 ≤ 2 ^ 2 := by nlinarith [hle]
    obtain ⟨hlo, hhi⟩ := abs_le_of_sq_le_sq' h4 (by norm_num : (0 : ℤ) ≤ 2)
    interval_cases (c k) <;> simp_all
  set S := univ.filter (fun k => c k ≠ 0) with hS
  have memS : ∀ k, k ∈ S ↔ c k ≠ 0 := by intro k; rw [hS]; simp
  have hsq1 : ∀ k ∈ S, (c k) ^ 2 = 1 := by
    intro k hk; rw [memS] at hk
    rcases hbound k with h | h | h <;> simp_all
  have hsumS : ∑ k ∈ S, (c k) ^ 2 = 2 := by
    have hsub : ∑ k ∈ S, (c k) ^ 2 = ∑ k, (c k) ^ 2 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k _ hk; rw [memS, not_not] at hk; simp [hk]
    rw [hsub, hZ]
  have hcard : S.card = 2 := by
    have heq : (∑ k ∈ S, (c k) ^ 2) = (S.card : ℤ) := by
      rw [Finset.sum_congr rfl hsq1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [heq] at hsumS; exact_mod_cast hsumS
  obtain ⟨p, q, hpq, hSpq⟩ := Finset.card_eq_two.1 hcard
  have hpS : p ∈ S := by rw [hSpq]; simp
  have hqS : q ∈ S := by rw [hSpq]; simp
  have helper : ∀ (i j : Fin 8), i ≠ j → c i ≠ 0 → c j ≠ 0 →
      (∀ k, k ≠ i → k ≠ j → c k = 0) →
      (fun k => (c k : ℚ)) = twoCoordinateVector i j (decide (c i = 1)) (decide (c j = 1)) := by
    intro i j hij hci hcj hoth
    have keyi : (if decide (c i = 1) then (1 : ℤ) else -1) = c i := by
      rcases hbound i with h | h | h
      · simp [h]
      · exact absurd h hci
      · simp [h]
    have keyj : (if decide (c j = 1) then (1 : ℤ) else -1) = c j := by
      rcases hbound j with h | h | h
      · simp [h]
      · exact absurd h hcj
      · simp [h]
    funext k; simp only [twoCoordinateVector]
    have hint : c k = twoCoordinateIntegerVector i j (decide (c i = 1)) (decide (c j = 1)) k := by
      rw [twoCoordinateIntegerVector]
      by_cases hki : k = i
      · subst hki; rw [if_pos rfl, if_neg hij, keyi]; ring
      · rw [if_neg hki]
        by_cases hkj : k = j
        · subst hkj; rw [if_pos rfl, keyj]; ring
        · rw [if_neg hkj, hoth k hki hkj]; ring
    exact_mod_cast hint
  have hci : c p ≠ 0 := (memS p).1 hpS
  have hcj : c q ≠ 0 := (memS q).1 hqS
  have hoth : ∀ k, k ≠ p → k ≠ q → c k = 0 := by
    intro k hkp hkq; by_contra hne
    have hkS := (memS k).2 hne
    rw [hSpq] at hkS; simp only [mem_insert, mem_singleton] at hkS
    rcases hkS with h | h
    · exact hkp h
    · exact hkq h
  have hx : x = fun k => (c k : ℚ) := funext hc
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact ⟨p, q, _, _, hlt, hx.trans (helper p q hpq hci hcj hoth)⟩
  · refine ⟨q, p, _, _, hgt, hx.trans (helper q p (Ne.symm hpq) hcj hci ?_)⟩
    intro k hkq hkp; exact hoth k hkp hkq

/-- A parameterized rational vector lies in the transformed third auxiliary set when its stored indices are increasing. -/
lemma parameterRationalVector_mem_setTransform_of_ordered (p : Auxiliary.parameterType) (hp : p.1 < p.2.1) :
    Auxiliary.parameterRationalVector p ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC :=
  ⟨⟨Or.inl (twoCoordinateVector_satisfies_predicateB _ _ _ _), twoCoordinateVector_satisfies_predicateC _ _ _ _⟩, twoCoordinateVector_pairing_self _ _ _ _ hp.ne⟩

/-- A sign vector of even Boolean weight belongs to the transformed third auxiliary set. -/
lemma signVector_mem_setTransform_of_even_weight (s) (hev : Even (boolVectorWeight s)) :
    signVector s ∈ Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC :=
  ⟨⟨Or.inr (signVector_satisfies_predicateA _), signVector_satisfies_predicateC_of_even_weight _ hev⟩, signVector_pairing_self _⟩

/-- An auxiliary finite collection of eight-coordinate rational vectors. -/
def Auxiliary.rationalVectorFinset : Finset (Fin 8 → ℚ) :=
  (univ.filter (fun p : Auxiliary.parameterType => p.1 < p.2.1)).image Auxiliary.parameterRationalVector ∪
  (univ.filter (fun s => Even (boolVectorWeight s))).image signVector

private lemma disjoint_int_half {I : Finset Auxiliary.parameterType} {J : Finset (Fin 8 → Bool)} :
    Disjoint (I.image Auxiliary.parameterRationalVector) (J.image signVector) := by
  rw [Finset.disjoint_left]
  rintro x hx1 hx2
  rw [Finset.mem_image] at hx1 hx2
  obtain ⟨p, _, rfl⟩ := hx1
  obtain ⟨s, _, hs⟩ := hx2
  exact twoCoordinateVector_ne_signVector p.1 p.2.1 p.2.2.1 p.2.2.2 s hs.symm

set_option maxRecDepth 10000 in

/-- The transformed third auxiliary vector set has cardinality two hundred forty. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem ncard_setTransform_rationalVectorSetC : (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC).ncard = 240 := by
  have hset : Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetC = ↑((univ.filter (fun p : Auxiliary.parameterType => p.1 < p.2.1)).image Auxiliary.parameterRationalVector ∪
      (univ.filter (fun s => Even (boolVectorWeight s))).image signVector) := by
    ext x
    simp only [Auxiliary.rationalVectorSetTransform, Auxiliary.rationalVectorSetC, Set.mem_setOf_eq, Finset.coe_union,
      Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨hdisj, hev⟩, hnorm⟩
      rcases hdisj with hInt | hHalf
      · obtain ⟨i, j, a, b, hlt, hx⟩ := eq_twoCoordinateVector_of_predicateB_and_pairing_self_eq_two x hInt hnorm
        exact Or.inl ⟨(i, j, a, b), hlt, hx.symm⟩
      · obtain ⟨s, hx⟩ := eq_signVector_of_predicateA_and_pairing_self_eq_two x hHalf hnorm
        exact Or.inr ⟨s, (signVector_satisfies_predicateC_iff_even_weight s).1 (hx ▸ hev), hx.symm⟩
    · rintro (⟨p, hlt, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact parameterRationalVector_mem_setTransform_of_ordered p hlt
      · exact signVector_mem_setTransform_of_even_weight s hs
  have hinj : Set.InjOn Auxiliary.parameterRationalVector ↑(univ.filter (fun p : Auxiliary.parameterType => p.1 < p.2.1)) := by
    refine parameterRationalVector_injOn_ordered.mono ?_
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint disjoint_int_half,
    Finset.card_image_of_injOn hinj, Finset.card_image_of_injOn signVector_injective.injOn]
  decide

set_option maxRecDepth 40000 in

/-- The transformed second auxiliary vector set has cardinality one hundred twenty-six. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem ncard_setTransform_rationalVectorSetB : (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB).ncard = 126 := by
  have hset : Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetB =
      ↑((univ.filter (fun p : Auxiliary.parameterType => p.1 < p.2.1 ∧ Auxiliary.parameterIntegerVector p 0 = Auxiliary.parameterIntegerVector p 1)).image Auxiliary.parameterRationalVector ∪
        (univ.filter (fun s => Even (boolVectorWeight s) ∧ s 0 = s 1)).image signVector) := by
    ext x
    simp only [Auxiliary.rationalVectorSetTransform, Auxiliary.rationalVectorSetB, Auxiliary.rationalVectorSetC, Set.mem_setOf_eq,
      Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨hdisj, hev⟩, h01⟩, hnorm⟩
      rcases hdisj with hInt | hHalf
      · obtain ⟨i, j, a, b, hlt, hx⟩ := eq_twoCoordinateVector_of_predicateB_and_pairing_self_eq_two x hInt hnorm
        refine Or.inl ⟨(i, j, a, b), ⟨hlt, ?_⟩, hx.symm⟩
        have : twoCoordinateVector i j a b 0 = twoCoordinateVector i j a b 1 := by rw [← hx]; exact h01
        simp only [Auxiliary.parameterIntegerVector, twoCoordinateVector] at this ⊢; exact_mod_cast this
      · obtain ⟨s, hx⟩ := eq_signVector_of_predicateA_and_pairing_self_eq_two x hHalf hnorm
        refine Or.inr ⟨s, ⟨(signVector_satisfies_predicateC_iff_even_weight s).1 (hx ▸ hev), ?_⟩, hx.symm⟩
        have : signVector s 0 = signVector s 1 := by rw [← hx]; exact h01
        exact (signVector_apply_eq_iff s 0 1).1 this
    · rintro (⟨p, ⟨hlt, hcz⟩, rfl⟩ | ⟨s, ⟨hs, hs01⟩, rfl⟩)
      · refine ⟨⟨parameterRationalVector_mem_setTransform_of_ordered p hlt |>.1, ?_⟩, parameterRationalVector_mem_setTransform_of_ordered p hlt |>.2⟩
        simp only [Auxiliary.parameterRationalVector, twoCoordinateVector]; exact_mod_cast hcz
      · refine ⟨⟨signVector_mem_setTransform_of_even_weight s hs |>.1, ?_⟩, signVector_mem_setTransform_of_even_weight s hs |>.2⟩
        rw [signVector_apply_eq_iff]; exact hs01
  have hinj : Set.InjOn Auxiliary.parameterRationalVector ↑(univ.filter (fun p : Auxiliary.parameterType => p.1 < p.2.1 ∧ Auxiliary.parameterIntegerVector p 0 = Auxiliary.parameterIntegerVector p 1)) := by
    refine parameterRationalVector_injOn_ordered.mono ?_
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.1
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint disjoint_int_half,
    Finset.card_image_of_injOn hinj, Finset.card_image_of_injOn signVector_injective.injOn]
  decide

set_option maxRecDepth 40000 in

/-- The transformed first auxiliary vector set has cardinality seventy-two. -/
@[source_ref "Chapter6/Problem6.9.2" (role := supporting)]
theorem ncard_setTransform_rationalVectorSetA : (Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA).ncard = 72 := by
  have hset : Auxiliary.rationalVectorSetTransform Auxiliary.rationalVectorSetA =
      ↑((univ.filter (fun p : Auxiliary.parameterType => p.1 < p.2.1 ∧ Auxiliary.parameterIntegerVector p 0 = Auxiliary.parameterIntegerVector p 1 ∧ Auxiliary.parameterIntegerVector p 1 = Auxiliary.parameterIntegerVector p 2)).image
          Auxiliary.parameterRationalVector ∪
        (univ.filter (fun s => Even (boolVectorWeight s) ∧ s 0 = s 1 ∧ s 1 = s 2)).image signVector) := by
    ext x
    simp only [Auxiliary.rationalVectorSetTransform, Auxiliary.rationalVectorSetA, Auxiliary.rationalVectorSetC, Set.mem_setOf_eq,
      Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨hdisj, hev⟩, h01, h12⟩, hnorm⟩
      rcases hdisj with hInt | hHalf
      · obtain ⟨i, j, a, b, hlt, hx⟩ := eq_twoCoordinateVector_of_predicateB_and_pairing_self_eq_two x hInt hnorm
        refine Or.inl ⟨(i, j, a, b), ⟨hlt, ?_, ?_⟩, hx.symm⟩
        · have : twoCoordinateVector i j a b 0 = twoCoordinateVector i j a b 1 := by rw [← hx]; exact h01
          simp only [Auxiliary.parameterIntegerVector, twoCoordinateVector] at this ⊢; exact_mod_cast this
        · have : twoCoordinateVector i j a b 1 = twoCoordinateVector i j a b 2 := by rw [← hx]; exact h12
          simp only [Auxiliary.parameterIntegerVector, twoCoordinateVector] at this ⊢; exact_mod_cast this
      · obtain ⟨s, hx⟩ := eq_signVector_of_predicateA_and_pairing_self_eq_two x hHalf hnorm
        refine Or.inr ⟨s, ⟨(signVector_satisfies_predicateC_iff_even_weight s).1 (hx ▸ hev), ?_, ?_⟩, hx.symm⟩
        · have : signVector s 0 = signVector s 1 := by rw [← hx]; exact h01
          exact (signVector_apply_eq_iff s 0 1).1 this
        · have : signVector s 1 = signVector s 2 := by rw [← hx]; exact h12
          exact (signVector_apply_eq_iff s 1 2).1 this
    · rintro (⟨p, ⟨hlt, hcz01, hcz12⟩, rfl⟩ | ⟨s, ⟨hs, hs01, hs12⟩, rfl⟩)
      · refine ⟨⟨parameterRationalVector_mem_setTransform_of_ordered p hlt |>.1, ?_, ?_⟩,
          parameterRationalVector_mem_setTransform_of_ordered p hlt |>.2⟩
        · simp only [Auxiliary.parameterRationalVector, twoCoordinateVector]; exact_mod_cast hcz01
        · simp only [Auxiliary.parameterRationalVector, twoCoordinateVector]; exact_mod_cast hcz12
      · refine ⟨⟨signVector_mem_setTransform_of_even_weight s hs |>.1, ?_, ?_⟩,
          signVector_mem_setTransform_of_even_weight s hs |>.2⟩
        · rw [signVector_apply_eq_iff]; exact hs01
        · rw [signVector_apply_eq_iff]; exact hs12
  have hinj : Set.InjOn Auxiliary.parameterRationalVector
      ↑(univ.filter (fun p : Auxiliary.parameterType => p.1 < p.2.1 ∧ Auxiliary.parameterIntegerVector p 0 = Auxiliary.parameterIntegerVector p 1 ∧ Auxiliary.parameterIntegerVector p 1 = Auxiliary.parameterIntegerVector p 2)) := by
    refine parameterRationalVector_injOn_ordered.mono ?_
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.1
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint disjoint_int_half,
    Finset.card_image_of_injOn hinj, Finset.card_image_of_injOn signVector_injective.injOn]
  decide

end RepresentationTheory.EightDimensionalRationalVectors

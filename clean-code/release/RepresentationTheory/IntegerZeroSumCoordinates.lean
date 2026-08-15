/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FiniteAssociatedSetCardinality
import RepresentationTheory.Alignment.Attribute

/-!
# Integer zero-sum coordinates

Adjacent-difference coordinates for integer-valued functions with zero coordinate sum.
-/

set_option backward.isDefEq.respectTransparency false

namespace RepresentationTheory.IntegerZeroSumCoordinates

open Matrix Finset Module

variable (n : ℕ)

/-- The integer-valued function given by the difference of unit coordinates at an index and its successor. -/
def adjacent_difference (i : Fin n) : Fin (n + 1) → ℤ :=
  Pi.single i.castSucc 1 - Pi.single i.succ 1

/-- An adjacent-difference function evaluates as the indicator of its first coordinate minus the indicator of the succeeding coordinate. -/
lemma adjacent_difference_apply (i : Fin n) (k : Fin (n + 1)) :
    adjacent_difference n i k = (if i.val = k.val then 1 else 0) - (if i.val + 1 = k.val then 1 else 0) := by
  simp only [adjacent_difference, Pi.sub_apply, Pi.single_apply]
  congr 1
  · congr 1
    simp only [eq_iff_iff]
    constructor
    · intro h; exact congrArg Fin.val h.symm
    · intro h; exact Fin.ext h.symm
  · congr 1
    simp only [eq_iff_iff, Fin.ext_iff, Fin.val_succ]
    omega

/-- The sum of the coordinates of an adjacent-difference function is zero. -/
lemma sum_adjacent_difference (i : Fin n) : ∑ k, adjacent_difference n i k = 0 := by
  simp only [adjacent_difference, Pi.sub_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_pi_single', Finset.sum_pi_single']
  simp

/-- The integer-linear map that sums all coordinates of a function on `Fin (n + 1)`. -/
def coordinate_sum_linear_map : (Fin (n + 1) → ℤ) →ₗ[ℤ] ℤ := ∑ i, LinearMap.proj i

/-- The coordinate-sum linear map evaluates to the sum of the input over all indices. -/
@[simp] lemma coordinate_sum_linear_map_apply (x : Fin (n + 1) → ℤ) :
    coordinate_sum_linear_map n x = ∑ i, x i := by
  simp [coordinate_sum_linear_map, LinearMap.sum_apply]

/-- The submodule of integer-valued functions on `Fin (n + 1)` whose coordinates sum to zero. -/
def zero_sum_submodule : Submodule ℤ (Fin (n + 1) → ℤ) :=
  LinearMap.ker (coordinate_sum_linear_map n)

/-- An integer-valued function belongs to the zero-sum submodule exactly when the sum of all its coordinates is zero. -/
@[simp] lemma mem_zero_sum_submodule_iff {x : Fin (n + 1) → ℤ} :
    x ∈ zero_sum_submodule n ↔ ∑ i, x i = 0 := by
  simp [zero_sum_submodule, LinearMap.mem_ker]

/-- The integer-linear map sending coefficients on `Fin n` to the corresponding linear combination of adjacent-difference functions. -/
def adjacent_difference_linear_map : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) :=
  ∑ i, (LinearMap.proj i).smulRight (adjacent_difference n i)

/-- The adjacent-difference linear map evaluates as the sum of each coefficient multiplied by its adjacent-difference function. -/
lemma adjacent_difference_linear_map_apply (c : Fin n → ℤ) :
    adjacent_difference_linear_map n c = ∑ i, c i • adjacent_difference n i := by
  simp [adjacent_difference_linear_map, LinearMap.sum_apply, LinearMap.smulRight_apply]

/-- The adjacent-difference linear map sends a unit singleton coefficient function to the corresponding adjacent-difference vector. -/
lemma adjacent_difference_linear_map_single (i : Fin n) :
    adjacent_difference_linear_map n (Pi.single i 1) = adjacent_difference n i := by
  rw [adjacent_difference_linear_map_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- An auxiliary result whose formal statement is unavailable. -/
lemma auxiliary_theorem (c : Fin n → ℤ) (k : Fin (n + 1)) :
    adjacent_difference_linear_map n c k =
      (if h : k.val < n then c ⟨k.val, h⟩ else 0)
        - (if h : 0 < k.val then c ⟨k.val - 1, by omega⟩ else 0) := by
  rw [adjacent_difference_linear_map_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, adjacent_difference_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [mul_ite, mul_one, mul_zero]
    split_ifs with hk
    · rw [Finset.sum_eq_single (⟨k.val, hk⟩ : Fin n)]
      · simp
      · intro j _ hj; simp only [ite_eq_right_iff]; intro h; exact absurd (Fin.ext h) hj
      · intro h; exact absurd (Finset.mem_univ _) h
    · apply Finset.sum_eq_zero; intro i _
      simp only [ite_eq_right_iff]; intro h; omega
  · simp only [mul_ite, mul_one, mul_zero]
    split_ifs with hk
    · rw [Finset.sum_eq_single (⟨k.val - 1, by omega⟩ : Fin n)]
      · have hval : (⟨k.val - 1, by omega⟩ : Fin n).val = k.val - 1 := rfl
        rw [if_pos (by rw [hval]; omega)]
      · intro j _ hj; simp only [ite_eq_right_iff]; intro h
        exact absurd (Fin.ext (show j.val = k.val - 1 by omega)) hj
      · intro h; exact absurd (Finset.mem_univ _) h
    · apply Finset.sum_eq_zero; intro i _
      simp only [ite_eq_right_iff]; intro h; omega

/-- The integer-linear map taking a function on `Fin (n + 1)` to its prefix sums indexed by `Fin n`. -/
def prefix_sum_linear_map : (Fin (n + 1) → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  LinearMap.pi fun i : Fin n =>
    ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), LinearMap.proj j

/-- At an index, the prefix-sum map is the sum of the input coordinates whose indices are at most that index. -/
lemma prefix_sum_linear_map_apply (x : Fin (n + 1) → ℤ) (i : Fin n) :
    prefix_sum_linear_map n x i =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), x j := by
  simp [prefix_sum_linear_map, LinearMap.pi_apply, LinearMap.sum_apply]

/-- Taking prefix sums after applying the adjacent-difference linear map recovers the original coefficient function. -/
lemma prefix_sum_adjacent_difference_linear_map (c : Fin n → ℤ) :
    prefix_sum_linear_map n (adjacent_difference_linear_map n c) = c := by
  funext i
  rw [prefix_sum_linear_map_apply]
  have hpt : ∀ j : Fin (n + 1), adjacent_difference_linear_map n c j =
      ∑ k, c k * adjacent_difference n k j := by
    intro j; rw [adjacent_difference_linear_map_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have inner : ∀ k : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val),
          adjacent_difference n k j = if k = i then 1 else 0 := by
    intro k
    simp only [adjacent_difference, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [Finset.sum_pi_single', Finset.sum_pi_single']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_succ]
    by_cases hki : k = i
    · subst hki; simp
    · rw [if_neg hki]
      have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      split_ifs <;> omega
  simp_rw [inner, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/-- For a zero-sum integer-valued function, applying the adjacent-difference map to its prefix sums recovers the function. -/
lemma adjacent_difference_prefix_sum_of_mem {x : Fin (n + 1) → ℤ}
    (hx : x ∈ zero_sum_submodule n) :
    adjacent_difference_linear_map n (prefix_sum_linear_map n x) = x := by
  have hsum : ∑ i, x i = 0 := (mem_zero_sum_submodule_iff n).mp hx
  set S : ℕ → ℤ :=
    fun m => ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ m), x j with hS
  have hPf : ∀ (m : ℕ) (hm : m < n), prefix_sum_linear_map n x ⟨m, hm⟩ = S m := by
    intro m hm; rw [prefix_sum_linear_map_apply]
  have hzero : S 0 = x ⟨0, by omega⟩ := by
    simp only [hS]
    rw [show Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ 0)
          = {(⟨0, by omega⟩ : Fin (n + 1))} from ?_]
    · rw [Finset.sum_singleton]
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact Fin.ext (show j.val = 0 by omega)
      · intro h; rw [h]
  have hstepFin : ∀ (i : Fin (n + 1)), 0 < i.val → S i.val = S (i.val - 1) + x i := by
    intro i hi; simp only [hS]
    rw [show Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val)
          = insert i (Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val - 1)) from ?_]
    · rw [Finset.sum_insert (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)]
      ring
    · ext j; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_cases hji : j.val ≤ i.val - 1
        · exact Or.inr hji
        · exact Or.inl (Fin.ext (by omega))
      · rintro (rfl | h) <;> omega
  have hfull : S n = 0 := by
    simp only [hS]
    rw [show Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ n) = Finset.univ from ?_]
    · rw [← hsum]
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Nat.lt_succ_iff.mp j.isLt
  funext k
  rw [auxiliary_theorem]
  by_cases hk : k.val < n
  · rw [dif_pos hk, hPf k.val hk]
    by_cases hk0 : 0 < k.val
    · rw [dif_pos hk0, hPf (k.val - 1) (by omega)]
      have hst := hstepFin k (by omega)
      rw [hst, add_sub_cancel_left]
    · rw [dif_neg hk0]
      have hk0' : k.val = 0 := by omega
      rw [hk0', sub_zero, hzero]
      congr 1; exact Fin.ext hk0'.symm
  · rw [dif_neg hk]
    have hkn : k.val = n := by omega
    by_cases hn0 : 0 < n
    · rw [dif_pos (by omega : 0 < k.val), hPf (k.val - 1) (by omega)]
      have hst := hstepFin k (by omega)
      have hSk : S k.val = 0 := by rw [hkn]; exact hfull
      rw [hSk] at hst
      linarith [hst]
    · rw [dif_neg (by omega : ¬ 0 < k.val), sub_zero]
      have hn : n = 0 := by omega
      have hx0 : x ⟨0, by omega⟩ = 0 := by
        have hf := hfull; rw [hn] at hf; rw [hzero] at hf; exact hf
      rw [show k = ⟨0, by omega⟩ from Fin.ext (show k.val = 0 by omega)]
      exact hx0.symm

/-- The adjacent-difference linear map with codomain restricted to the zero-sum submodule. -/
def adjacent_difference_to_zero_sum : (Fin n → ℤ) →ₗ[ℤ] zero_sum_submodule n :=
  LinearMap.codRestrict (zero_sum_submodule n) (adjacent_difference_linear_map n) fun c => by
    rw [mem_zero_sum_submodule_iff, adjacent_difference_linear_map_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_adjacent_difference, mul_zero, Finset.sum_const_zero]

/-- The zero-sum-valued adjacent-difference map has underlying function equal to the ambient adjacent-difference linear map. -/
@[simp] lemma adjacent_difference_to_zero_sum_coe (c : Fin n → ℤ) :
    (adjacent_difference_to_zero_sum n c : Fin (n + 1) → ℤ) =
      adjacent_difference_linear_map n c := rfl

/-- The integer-linear equivalence from coefficient functions on `Fin n` to zero-sum functions on `Fin (n + 1)`. -/
def adjacent_difference_equiv_zero_sum : (Fin n → ℤ) ≃ₗ[ℤ] zero_sum_submodule n :=
  LinearEquiv.ofLinear (adjacent_difference_to_zero_sum n)
    (prefix_sum_linear_map n ∘ₗ (zero_sum_submodule n).subtype)
    (by
      refine LinearMap.ext fun y => Subtype.ext ?_
      change adjacent_difference_linear_map n (prefix_sum_linear_map n y.val) = y.val
      exact adjacent_difference_prefix_sum_of_mem n y.2)
    (by
      refine LinearMap.ext fun c => ?_
      change prefix_sum_linear_map n (adjacent_difference_linear_map n c) = c
      exact prefix_sum_adjacent_difference_linear_map n c)

/-- The underlying function of the adjacent-difference equivalence is its ambient adjacent-difference linear-map value. -/
@[simp] lemma adjacent_difference_equiv_zero_sum_coe (c : Fin n → ℤ) :
    (adjacent_difference_equiv_zero_sum n c : Fin (n + 1) → ℤ) =
      adjacent_difference_linear_map n c := rfl

/-- A basis of the zero-sum integer-valued functions on `Fin (n + 1)`, indexed by `Fin n`. -/
noncomputable def zero_sum_basis : Basis (Fin n) ℤ (zero_sum_submodule n) :=
  (Pi.basisFun ℤ (Fin n)).map (adjacent_difference_equiv_zero_sum n)

/-- The zero-sum basis vector at an index has underlying function equal to the corresponding adjacent-difference vector. -/
@[simp] lemma zero_sum_basis_apply (i : Fin n) :
    (zero_sum_basis n i : Fin (n + 1) → ℤ) = adjacent_difference n i := by
  rw [zero_sum_basis, Basis.map_apply, Pi.basisFun_apply,
    adjacent_difference_equiv_zero_sum_coe, adjacent_difference_linear_map_single]

/-- The dot product of two adjacent-difference vectors is the corresponding entry of twice the identity minus the specified adjacency matrix. -/
lemma dotProduct_adjacent_difference (hn : 1 ≤ n) (i j : Fin n) :
    dotProduct (adjacent_difference n i) (adjacent_difference n j) =
      (2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.A n hn).matrix) i j := by
  rw [show adjacent_difference n j = Pi.single j.castSucc 1 - Pi.single j.succ 1 from rfl,
    dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  simp only [adjacent_difference_apply, Fin.val_castSucc, Fin.val_succ,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix]
  split_ifs <;> simp_all [Fin.ext_iff] ; omega

/-- The dot product of two images under the adjacent-difference linear map equals the coefficient pairing defined by twice the identity minus the specified adjacency matrix. -/
lemma dotProduct_adjacent_difference_linear_map (hn : 1 ≤ n) (c d : Fin n → ℤ) :
    dotProduct (adjacent_difference_linear_map n c) (adjacent_difference_linear_map n d) =
      dotProduct c ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) -
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.A n hn).matrix).mulVec d) := by
  rw [adjacent_difference_linear_map_apply, adjacent_difference_linear_map_apply,
    sum_dotProduct]
  simp only [smul_dotProduct, dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_adjacent_difference n hn]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The set of integer-valued functions obtained as differences of unit singleton functions at distinct indices. -/
def singleton_difference_set : Set (Fin (n + 1) → ℤ) :=
  {x | x ∈ zero_sum_submodule n ∧ x ≠ 0 ∧ dotProduct x x = 2}

/-- A function belongs to the singleton-difference set exactly when it is the difference of two unit singleton functions at distinct indices. -/
@[source_ref "Chapter6/Example6.4.9" (role := primary)]
theorem mem_singleton_difference_set_iff (x : Fin (n + 1) → ℤ) :
    x ∈ singleton_difference_set n ↔
      ∃ i j : Fin (n + 1), i ≠ j ∧ x = Pi.single i 1 - Pi.single j 1 := by
  constructor
  · rintro ⟨hmem, _, hq⟩
    have hsum : ∑ k, x k = 0 := (mem_zero_sum_submodule_iff n).mp hmem
    have hqq : ∑ k, x k ^ 2 = 2 := by rw [← hq]; simp [dotProduct, pow_two]
    have hb2 : ∀ k, x k ^ 2 ≤ 2 := fun k =>
      hqq ▸ Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (mem_univ k)
    have hpm : ∀ k, x k = -1 ∨ x k = 0 ∨ x k = 1 := by
      intro k
      have hb := hb2 k
      have hlo : -1 ≤ x k := by
        by_contra h; push Not at h
        have hle : x k ≤ -2 := by omega
        nlinarith [hb, sq_nonneg (x k + 2)]
      have hhi : x k ≤ 1 := by
        by_contra h; push Not at h
        have hge : 2 ≤ x k := by omega
        nlinarith [hb, sq_nonneg (x k - 2)]
      interval_cases (x k) <;> tauto
    have hsq : ∀ k, x k ^ 2 = if x k ≠ 0 then 1 else 0 := by
      intro k; rcases hpm k with h | h | h <;> simp [h]
    have hcard : (univ.filter (fun k => x k ≠ 0)).card = 2 := by
      have h := hqq
      rw [Finset.sum_congr rfl (fun k _ => hsq k), Finset.sum_boole] at h
      exact_mod_cast h
    obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp hcard
    have hzero : ∀ k, k ≠ i → k ≠ j → x k = 0 := by
      intro k hki hkj
      by_contra h
      have hmemk : k ∈ univ.filter (fun k => x k ≠ 0) :=
        Finset.mem_filter.mpr ⟨mem_univ k, h⟩
      rw [hT] at hmemk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemk
      tauto
    have hxi : x i ≠ 0 := by
      have : i ∈ univ.filter (fun k => x k ≠ 0) := by rw [hT]; simp
      exact (Finset.mem_filter.mp this).2
    have hxj : x j ≠ 0 := by
      have : j ∈ univ.filter (fun k => x k ≠ 0) := by rw [hT]; simp
      exact (Finset.mem_filter.mp this).2
    have hsij : x i + x j = 0 := by
      have hsupp : ∑ k ∈ univ.filter (fun k => x k ≠ 0), x k = ∑ k, x k :=
        Finset.sum_filter_ne_zero univ
      rw [hT, Finset.sum_pair hij, hsum] at hsupp
      exact hsupp
    have key : ∀ (p q : Fin (n + 1)), x p = 1 → x q = -1 → p ≠ q →
        (∀ k, k ≠ p → k ≠ q → x k = 0) → x = Pi.single p 1 - Pi.single q 1 := by
      intro p q hp hq hpq hz
      funext k
      by_cases hkp : k = p
      · subst hkp
        rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hpq, hp, sub_zero]
      · by_cases hkq : k = q
        · subst hkq
          rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hpq), Pi.single_eq_same, hq, zero_sub]
        · rw [Pi.sub_apply, Pi.single_eq_of_ne hkp, Pi.single_eq_of_ne hkq,
            hz k hkp hkq, sub_zero]
    have hxi' : x i = -1 ∨ x i = 1 := by
      rcases hpm i with h | h | h; exacts [Or.inl h, absurd h hxi, Or.inr h]
    rcases hxi' with hi1 | hi1
    · have hj1 : x j = 1 := by omega
      exact ⟨j, i, hij.symm, key j i hj1 hi1 hij.symm (fun k hkj hki => hzero k hki hkj)⟩
    · have hj1 : x j = -1 := by omega
      exact ⟨i, j, hij, key i j hi1 hj1 hij hzero⟩
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_zero_sum_submodule_iff]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [Finset.sum_pi_single', Finset.sum_pi_single']
      simp
    · intro h
      have hi := congr_fun h i
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        sub_zero, Pi.zero_apply] at hi
      exact one_ne_zero hi
    · rw [sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        Pi.single_eq_of_ne (Ne.symm hij)]
      ring

/-- For the specified adjacency matrix, the auxiliary vector property holds exactly when the associated adjacent-difference vector belongs to the singleton-difference set. -/
theorem auxiliary_property_iff_mem_singleton_difference_set (hn : 1 ≤ n) (c : Fin n → ℤ) :
    RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n
        (RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.A n hn).matrix c ↔
      adjacent_difference_linear_map n c ∈ singleton_difference_set n := by
  unfold RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix
    singleton_difference_set
  simp only [Set.mem_setOf_eq]
  rw [dotProduct_adjacent_difference_linear_map n hn]
  constructor
  · rintro ⟨hne, hq⟩
    exact ⟨(adjacent_difference_to_zero_sum n c).2,
      fun h => hne (by rw [← prefix_sum_adjacent_difference_linear_map n c, h, map_zero]), hq⟩
  · rintro ⟨_, hne, hq⟩
    exact ⟨fun h => hne (by rw [h, map_zero]), hq⟩

/-- An auxiliary set of integer-valued functions on `Fin (n + 1)`. -/
def auxiliary_set : Set (Fin (n + 1) → ℤ) :=
  {x | ∃ i j : Fin (n + 1), i < j ∧ x = Pi.single i 1 - Pi.single j 1}

private lemma diff_injOn :
    Set.InjOn (fun p : Fin (n + 1) × Fin (n + 1) =>
        (Pi.single p.1 1 - Pi.single p.2 1 : Fin (n + 1) → ℤ))
      {p | p.1 < p.2} := by
  have hval1 : ∀ (a b k : Fin (n + 1)), a ≠ b →
      ((Pi.single a 1 - Pi.single b 1 : Fin (n + 1) → ℤ) k = 1 ↔ k = a) := by
    intro a b k hab
    rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]
    constructor
    · intro h; by_contra hka; rw [if_neg hka] at h; split_ifs at h <;> omega
    · intro h; subst h; rw [if_pos rfl, if_neg hab, sub_zero]
  have hvaln : ∀ (a b k : Fin (n + 1)), a ≠ b →
      ((Pi.single a 1 - Pi.single b 1 : Fin (n + 1) → ℤ) k = -1 ↔ k = b) := by
    intro a b k hab
    rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]
    constructor
    · intro h; by_contra hkb; rw [if_neg hkb] at h; split_ifs at h <;> omega
    · intro h; subst h; rw [if_neg (Ne.symm hab), if_pos rfl, zero_sub]
  rintro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ heq
  simp only [Set.mem_setOf_eq] at h₁ h₂
  have hne₁ : i₁ ≠ j₁ := ne_of_lt h₁
  have hne₂ : i₂ ≠ j₂ := ne_of_lt h₂
  have hci : (Pi.single i₁ 1 - Pi.single j₁ 1 : Fin (n + 1) → ℤ) i₁ =
      (Pi.single i₂ 1 - Pi.single j₂ 1 : Fin (n + 1) → ℤ) i₁ := congr_fun heq i₁
  have hcj : (Pi.single i₁ 1 - Pi.single j₁ 1 : Fin (n + 1) → ℤ) j₁ =
      (Pi.single i₂ 1 - Pi.single j₂ 1 : Fin (n + 1) → ℤ) j₁ := congr_fun heq j₁
  rw [(hval1 i₁ j₁ i₁ hne₁).mpr rfl] at hci
  rw [(hvaln i₁ j₁ j₁ hne₁).mpr rfl] at hcj
  exact Prod.ext ((hval1 i₂ j₂ i₁ hne₂).mp hci.symm)
    ((hvaln i₂ j₂ j₁ hne₂).mp hcj.symm)

private lemma card_strictPairs :
    (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).card =
      n * (n + 1) / 2 := by
  have hD : (univ : Finset (Fin (n + 1))).offDiag.card = n * (n + 1) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.succ_mul,
      Nat.add_sub_cancel]
  have hAB : (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).card =
      (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.2 < p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [mem_filter, mem_univ, true_and] at *; exact hp
    · intro p₁ h₁ p₂ h₂ he; simp only [Prod.mk.injEq] at he; exact Prod.ext he.2 he.1
    · intro p hp; simp only [mem_filter, mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), by simp [hp], by simp⟩
  have hunion : univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2) ∪
        univ.filter (fun p => p.2 < p.1) =
      (univ : Finset (Fin (n + 1))).offDiag := by
    ext p; simp only [mem_union, mem_filter, mem_univ, true_and, Finset.mem_offDiag]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact (ne_of_lt h).symm
    · intro hne; rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hdisj : Disjoint
      (univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2))
      (univ.filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]; intro p h₁ h₂
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    exact absurd h₁ (not_lt.mpr (le_of_lt h₂))
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion, hD, ← hAB] at hcu
  omega

/-- The auxiliary set has cardinality `n * (n + 1) / 2`. -/
@[source_ref "Chapter6/Example6.4.9" (role := primary)]
theorem auxiliary_set_ncard : Set.ncard (auxiliary_set n) = n * (n + 1) / 2 := by
  have hset : auxiliary_set n =
      ↑((univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)).image
        (fun p => (Pi.single p.1 1 - Pi.single p.2 1 : Fin (n + 1) → ℤ))) := by
    ext x
    simp only [auxiliary_set, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, j, hij, rfl⟩; exact ⟨(i, j), hij, rfl⟩
    · rintro ⟨⟨i, j⟩, hij, rfl⟩; exact ⟨i, j, hij, rfl⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn, card_strictPairs]
  intro p hp q hq he
  exact diff_injOn n (by simpa using (mem_filter.mp hp).2)
    (by simpa using (mem_filter.mp hq).2) he

end RepresentationTheory.IntegerZeroSumCoordinates

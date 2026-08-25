/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.Alignment.Attribute

/-! # Root Order Matrices -/

namespace RepresentationTheory.Combinatorics.Partition.RootOrderMatrices

open RepresentationTheory.PermutationPolynomialAuxiliary
  RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
  RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter
  RepresentationTheory.SymmetricGroup.PartitionDominance

/-- An auxiliary natural-valued part accessor for a partition. -/
noncomputable def Partition.auxiliaryPartAt {n : ℕ} (la : Nat.Partition n) (i : ℕ) : ℕ :=
  (auxiliaryPartitionNatList la).getD i 0

private theorem sum_take_succ_getD (l : List ℕ) (k : ℕ) :
    (l.take (k + 1)).sum = (l.take k).sum + l.getD k 0 := by
  rw [List.take_add_one, List.sum_append]
  congr 1
  rcases h : l[k]? with _ | x
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- The sum of an initial segment of the sorted parts equals the sum of the indexed parts over the same range. -/
theorem Partition.sum_take_sortedParts {n : ℕ} (la : Nat.Partition n) (k : ℕ) :
    ((auxiliaryPartitionNatList la).take k).sum =
      ∑ i ∈ Finset.range k, Partition.auxiliaryPartAt la i := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_take_succ_getD, ih, Finset.sum_range_succ]; rfl

/-- The list of sorted parts has length at most the size of the partition. -/
theorem Partition.sortedParts_length_le {n : ℕ} (la : Nat.Partition n) :
    (auxiliaryPartitionNatList la).length ≤ n := by
  have hsum : (auxiliaryPartitionNatList la).sum = n := by
    have hsort : ((auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts :=
      la.parts.sort_eq (· ≥ ·)
    have : (auxiliaryPartitionNatList la).sum = la.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, la.parts_sum]
  have hpos : ∀ x ∈ (auxiliaryPartitionNatList la), 1 ≤ x := fun x hx =>
    la.parts_pos ((Multiset.mem_sort _).mp hx)
  calc (auxiliaryPartitionNatList la).length ≤ (auxiliaryPartitionNatList la).sum :=
      List.length_le_sum_of_one_le _ hpos
    _ = n := hsum

/-- The auxiliary part accessor is zero at indices at least the size of the partition. -/
theorem Partition.auxiliaryPartAt_eq_zero_of_length_le {n : ℕ} (la : Nat.Partition n) {i : ℕ}
    (hi : n ≤ i) : Partition.auxiliaryPartAt la i = 0 := by
  have := Partition.sortedParts_length_le la
  simp [Partition.auxiliaryPartAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by omega : (auxiliaryPartitionNatList la).length ≤ i)]

/-- Taking at least the partition size from the sorted parts gives a sum equal to that size. -/
theorem Partition.sum_take_sortedParts_eq_size {n : ℕ} (la : Nat.Partition n) {k : ℕ}
    (hk : n ≤ k) : ((auxiliaryPartitionNatList la).take k).sum = n := by
  have hlen : (auxiliaryPartitionNatList la).length ≤ k :=
    le_trans (Partition.sortedParts_length_le la) hk
  rw [List.take_of_length_le hlen]
  have hsort : ((auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts :=
    la.parts.sort_eq (· ≥ ·)
  have : (auxiliaryPartitionNatList la).sum = la.parts.sum := by
    rw [← Multiset.sum_coe, hsort]
  rw [this, la.parts_sum]

/-- An auxiliary integer-valued function of three natural numbers. -/
def auxiliaryIntegerFunction (i j : ℕ) : ℕ → ℤ := fun k => (if i = k then 1 else 0) - (if j = k then 1 else 0)

/-- An auxiliary root-order relation on partitions. -/
def Partition.rootOrder {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  ∃ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 < p.2) ∧
    ∀ k : ℕ, (Partition.auxiliaryPartAt mu k : ℤ) =
      Partition.auxiliaryPartAt la k +
        (L.map (fun p => auxiliaryIntegerFunction p.1 p.2 k)).sum

/-- Every partition is root-below itself. -/
theorem Partition.rootOrder.refl {n : ℕ} (la : Nat.Partition n) : Partition.rootOrder la la :=
  ⟨[], by simp, by simp⟩

/-- The root-order relation on partitions is transitive. -/
theorem Partition.rootOrder.trans {n : ℕ} {la mu nu : Nat.Partition n}
    (h₁ : Partition.rootOrder la mu) (h₂ : Partition.rootOrder mu nu) :
    Partition.rootOrder la nu := by
  obtain ⟨L₁, hL₁, hs₁⟩ := h₁
  obtain ⟨L₂, hL₂, hs₂⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    exacts [hL₁ p hp, hL₂ p hp]
  · intro k
    rw [List.map_append, List.sum_append, hs₂ k, hs₁ k]
    ring

private theorem sum_range_rootVec (i j k : ℕ) :
    ∑ m ∈ Finset.range k, auxiliaryIntegerFunction i j m =
      (if i < k then (1 : ℤ) else 0) - (if j < k then 1 else 0) := by
  simp only [auxiliaryIntegerFunction, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq (Finset.range k) i (fun _ => (1 : ℤ)),
    Finset.sum_ite_eq (Finset.range k) j (fun _ => (1 : ℤ))]
  simp [Finset.mem_range]

private theorem sum_range_list_rootVec (L : List (ℕ × ℕ)) (k : ℕ) :
    ∑ m ∈ Finset.range k, (L.map (fun p => auxiliaryIntegerFunction p.1 p.2 m)).sum =
      (L.map (fun p => (if p.1 < k then (1 : ℤ) else 0) - (if p.2 < k then 1 else 0))).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih, sum_range_rootVec]

/-- The root-order relation implies the reversed auxiliary relation. -/
theorem Partition.rootOrder.auxiliaryRelation_of_le {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.rootOrder la mu) : Partition.Dominates mu la := by
  obtain ⟨L, hL, hs⟩ := h
  intro k

  have key : (((auxiliaryPartitionNatList la).take k).sum : ℤ) ≤
      (((auxiliaryPartitionNatList mu).take k).sum : ℤ) := by
    rw [Partition.sum_take_sortedParts la k, Partition.sum_take_sortedParts mu k]
    push_cast
    have hsum : ∑ i ∈ Finset.range k, (Partition.auxiliaryPartAt mu i : ℤ) =
        ∑ i ∈ Finset.range k, (Partition.auxiliaryPartAt la i : ℤ) +
          (L.map (fun p => (if p.1 < k then (1 : ℤ) else 0) - (if p.2 < k then 1 else 0))).sum := by
      rw [← sum_range_list_rootVec L k, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hs i
    have hnonneg : (0 : ℤ) ≤
        (L.map (fun p => (if p.1 < k then (1 : ℤ) else 0) - (if p.2 < k then 1 else 0))).sum := by
      refine List.sum_nonneg ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hlt := hL p hp

      rcases Nat.lt_or_ge p.2 k with h2 | h2
      · have h1 : p.1 < k := by omega
        simp [h1, h2]
      · have h2' : ¬ p.2 < k := by omega
        rcases Nat.lt_or_ge p.1 k with h1 | h1
        · simp [h1, h2']
        · have h1' : ¬ p.1 < k := by omega
          simp [h1', h2']
    omega
  exact_mod_cast key

private noncomputable def domDefect {n : ℕ} (la mu : Nat.Partition n) (k : ℕ) : ℕ :=
  ((auxiliaryPartitionNatList mu).take k).sum -
    ((auxiliaryPartitionNatList la).take k).sum

private theorem domDefect_cast {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.Dominates mu la) (k : ℕ) :
    (domDefect la mu k : ℤ) =
      (((auxiliaryPartitionNatList mu).take k).sum : ℤ) -
        (((auxiliaryPartitionNatList la).take k).sum : ℤ) := by
  have := h k
  simp only [domDefect]
  omega

private theorem domDefect_eq_zero_of_le {n : ℕ} (la mu : Nat.Partition n) {k : ℕ}
    (hk : n ≤ k) : domDefect la mu k = 0 := by
  simp [domDefect, Partition.sum_take_sortedParts_eq_size la hk,
    Partition.sum_take_sortedParts_eq_size mu hk]

private theorem domDefect_succ_sub {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.Dominates mu la) (i : ℕ) :
    (domDefect la mu (i + 1) : ℤ) - (domDefect la mu i : ℤ) =
      (Partition.auxiliaryPartAt mu i : ℤ) - (Partition.auxiliaryPartAt la i : ℤ) := by
  rw [domDefect_cast h, domDefect_cast h, sum_take_succ_getD, sum_take_succ_getD]
  push_cast
  simp only [Partition.auxiliaryPartAt]
  ring

private noncomputable def domWitnessAux {n : ℕ} (la mu : Nat.Partition n) :
    ℕ → List (ℕ × ℕ)
  | 0 => []
  | k + 1 => domWitnessAux la mu k ++ List.replicate (domDefect la mu (k + 1)) (k, k + 1)

private theorem domWitnessAux_mem {n : ℕ} (la mu : Nat.Partition n) (m : ℕ) :
    ∀ p ∈ domWitnessAux la mu m, p.1 < p.2 := by
  induction m with
  | zero => simp [domWitnessAux]
  | succ m ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih p hp
    · rw [List.eq_of_mem_replicate hp]; omega

private theorem domWitnessAux_sum {n : ℕ} (la mu : Nat.Partition n) (m i : ℕ) :
    ((domWitnessAux la mu m).map (fun p => auxiliaryIntegerFunction p.1 p.2 i)).sum =
      ∑ k ∈ Finset.range m, (domDefect la mu (k + 1) : ℤ) * auxiliaryIntegerFunction k (k + 1) i := by
  induction m with
  | zero => simp [domWitnessAux]
  | succ m ih =>
    rw [domWitnessAux, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
      List.map_replicate, List.sum_replicate, nsmul_eq_mul]

private theorem domWitnessAux_coeff {n : ℕ} (la mu : Nat.Partition n) (i : ℕ) :
    ((domWitnessAux la mu n).map (fun p => auxiliaryIntegerFunction p.1 p.2 i)).sum =
      (domDefect la mu (i + 1) : ℤ) - (domDefect la mu i : ℤ) := by
  rw [domWitnessAux_sum]
  have hsplit : ∀ k ∈ Finset.range n,
      (domDefect la mu (k + 1) : ℤ) * auxiliaryIntegerFunction k (k + 1) i =
        (if k = i then (domDefect la mu (k + 1) : ℤ) else 0) -
          (if k + 1 = i then (domDefect la mu (k + 1) : ℤ) else 0) := by
    intro k _
    simp only [auxiliaryIntegerFunction, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]

  have hA : (∑ k ∈ Finset.range n, if k = i then (domDefect la mu (k + 1) : ℤ) else 0) =
      (domDefect la mu (i + 1) : ℤ) := by
    rw [Finset.sum_ite_eq' (Finset.range n) i fun k => (domDefect la mu (k + 1) : ℤ)]
    by_cases hi : i < n
    · simp [Finset.mem_range, hi]
    · simp [Finset.mem_range, hi, domDefect_eq_zero_of_le la mu (show n ≤ i + 1 by omega)]

  have hB : (∑ k ∈ Finset.range n, if k + 1 = i then (domDefect la mu (k + 1) : ℤ) else 0) =
      (domDefect la mu i : ℤ) := by
    rcases i with _ | j
    · simp [domDefect]
    · have hcongr : ∀ k ∈ Finset.range n,
          (if k + 1 = j + 1 then (domDefect la mu (k + 1) : ℤ) else 0) =
            (if k = j then (domDefect la mu (k + 1) : ℤ) else 0) := by
        intro k _
        by_cases hkj : k = j <;> simp [hkj]
      rw [Finset.sum_congr rfl hcongr,
        Finset.sum_ite_eq' (Finset.range n) j fun k => (domDefect la mu (k + 1) : ℤ)]
      by_cases hj : j < n
      · simp [Finset.mem_range, hj]
      · simp [Finset.mem_range, hj, domDefect_eq_zero_of_le la mu (show n ≤ j + 1 by omega)]
  rw [hA, hB]

/-- The auxiliary relation implies the reversed root relation. -/
theorem _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.rootLe_of_auxiliaryRelation {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.Dominates mu la) : Partition.rootOrder la mu := by
  refine ⟨domWitnessAux la mu n, domWitnessAux_mem la mu n, fun i => ?_⟩
  rw [domWitnessAux_coeff]
  have hdiff := domDefect_succ_sub h i
  omega

/-- The root-order relation is equivalent to the reversed auxiliary relation. -/
@[source_ref "Chapter5/Remark5.15.5" (role := supporting)]
theorem Partition.rootOrder_iff_auxiliaryRelation {n : ℕ} (la mu : Nat.Partition n) :
    Partition.rootOrder la mu ↔ Partition.Dominates mu la :=
  ⟨Partition.rootOrder.auxiliaryRelation_of_le,
    _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.rootLe_of_auxiliaryRelation⟩

/-- The root-order relation on partitions is antisymmetric. -/
theorem Partition.rootOrder.antisymm {n : ℕ} {la mu : Nat.Partition n}
    (h₁ : Partition.rootOrder la mu) (h₂ : Partition.rootOrder mu la) : la = mu :=
  (_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.antisymm
    (Partition.rootOrder.auxiliaryRelation_of_le h₂)
    (Partition.rootOrder.auxiliaryRelation_of_le h₁))

/-- The root relation on partitions defines a partial order. -/
@[source_ref "Chapter5/Remark5.15.5" (role := supporting)]
instance Partition.rootOrder_isPartialOrder (n : ℕ) :
    IsPartialOrder (Nat.Partition n) Partition.rootOrder where
  refl := Partition.rootOrder.refl
  trans _ _ _ := Partition.rootOrder.trans
  antisymm _ _ h₁ h₂ := Partition.rootOrder.antisymm h₁ h₂

/-- The auxiliary count vanishes when the first partition is not root-below the second. -/
@[source_ref "Chapter5/Remark5.15.5" (role := supporting)]
theorem Partition.auxiliaryCount_eq_zero_of_not_rootLe (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ Partition.rootOrder la mu) : auxiliaryPartitionNat n la mu = 0 :=
  auxiliaryPartitionNat_eq_zero_of_not_auxiliaryRelation n la mu
    (fun hd => h
      (_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.rootLe_of_auxiliaryRelation hd))

/-- The auxiliary relation on partitions is reflexive. -/
theorem _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.refl {n : ℕ} (la : Nat.Partition n) :
    Partition.Dominates la la := fun _ => le_refl _

/-- The auxiliary relation on partitions is transitive. -/
theorem _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.trans {n : ℕ} {la mu nu : Nat.Partition n}
    (h₁ : Partition.Dominates la mu) (h₂ : Partition.Dominates mu nu) :
    Partition.Dominates la nu := fun k => le_trans (h₂ k) (h₁ k)

private theorem sum_take_le {n : ℕ} (la : Nat.Partition n) (k : ℕ) :
    ((auxiliaryPartitionNatList la).take k).sum ≤ n := by
  have hsplit : ((auxiliaryPartitionNatList la).take k).sum +
      ((auxiliaryPartitionNatList la).drop k).sum = (auxiliaryPartitionNatList la).sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hfull : (auxiliaryPartitionNatList la).sum = n := by
    have hsort : ((auxiliaryPartitionNatList la) : Multiset ℕ) = la.parts :=
      la.parts.sort_eq (· ≥ ·)
    have : (auxiliaryPartitionNatList la).sum = la.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, la.parts_sum]
  omega

/-- An auxiliary natural-valued statistic on partitions. -/
noncomputable def Partition.auxiliaryNatStatistic {n : ℕ} (la : Nat.Partition n) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), ((auxiliaryPartitionNatList la).take k).sum

private theorem domRank_le {n : ℕ} (la : Nat.Partition n) : Partition.auxiliaryNatStatistic la ≤ (n + 1) * n := by
  calc Partition.auxiliaryNatStatistic la ≤ ∑ _k ∈ Finset.range (n + 1), n :=
        Finset.sum_le_sum fun k _ => sum_take_le la k
    _ = (n + 1) * n := by simp [Finset.sum_const, mul_comm]

private theorem domRank_mono {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.Dominates mu la) : Partition.auxiliaryNatStatistic la ≤ Partition.auxiliaryNatStatistic mu :=
  Finset.sum_le_sum fun k _ => h k

private theorem domRank_lt {n : ℕ} {la mu : Nat.Partition n}
    (h : Partition.Dominates mu la) (hne : la ≠ mu) : Partition.auxiliaryNatStatistic la < Partition.auxiliaryNatStatistic mu := by
  rcases lt_or_eq_of_le (domRank_mono h) with hlt | heq
  · exact hlt
  ·
    exfalso
    have hall : ∀ k ∈ Finset.range (n + 1),
        ((auxiliaryPartitionNatList la).take k).sum =
          ((auxiliaryPartitionNatList mu).take k).sum :=
      (Finset.sum_eq_sum_iff_of_le fun k _ => h k).mp heq
    have hconv : Partition.Dominates la mu := by
      intro k
      rcases le_or_gt k n with hk | hk
      · exact le_of_eq (hall k (Finset.mem_range.mpr (by omega))).symm
      · rw [Partition.sum_take_sortedParts_eq_size la (by omega),
          Partition.sum_take_sortedParts_eq_size mu (by omega)]
    exact hne (Partition.Dominates.antisymm hconv h)

section Matrices

variable {n : ℕ}

private def TriSupp (M : Matrix (Nat.Partition n) (Nat.Partition n) ℂ) : Prop :=
  ∀ i j, M i j ≠ 0 → Partition.Dominates i j

private theorem TriSupp.one : TriSupp (1 : Matrix (Nat.Partition n) (Nat.Partition n) ℂ) := by
  intro i j hij
  by_cases h : i = j
  · exact h ▸ Partition.Dominates.refl i
  · simp [Matrix.one_apply_ne h] at hij

private theorem TriSupp.mul {A B : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : TriSupp A) (hB : TriSupp B) : TriSupp (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact Partition.Dominates.trans (hA i l (left_ne_zero_of_mul hl))
    (hB l j (right_ne_zero_of_mul hl))

private theorem TriSupp.neg {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : TriSupp A) : TriSupp (-A) := fun i j hij => hA i j (neg_ne_zero.mp hij)

private theorem TriSupp.pow {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : TriSupp A) (k : ℕ) : TriSupp (A ^ k) := by
  induction k with
  | zero => simpa using TriSupp.one
  | succ k ih => rw [pow_succ]; exact ih.mul hA

private theorem TriSupp.sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Nat.Partition n) (Nat.Partition n) ℂ) (hf : ∀ i ∈ s, TriSupp (f i)) :
    TriSupp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => intro i j hij; simp at hij
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    intro i j hij
    rw [Matrix.add_apply] at hij
    by_cases h : f a i j = 0
    · exact ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) i j (by simpa [h] using hij)
    · exact hf a (Finset.mem_insert_self a s) i j h

private def GradedBy (M : Matrix (Nat.Partition n) (Nat.Partition n) ℂ) (d : ℕ) : Prop :=
  ∀ i j, M i j ≠ 0 → Partition.auxiliaryNatStatistic j + d ≤ Partition.auxiliaryNatStatistic i

private theorem GradedBy.mul {A B : Matrix (Nat.Partition n) (Nat.Partition n) ℂ} {d e : ℕ}
    (hA : GradedBy A d) (hB : GradedBy B e) : GradedBy (A * B) (d + e) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  have h1 := hA i l (left_ne_zero_of_mul hl)
  have h2 := hB l j (right_ne_zero_of_mul hl)
  omega

private theorem GradedBy.pow {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : GradedBy A 1) (k : ℕ) : GradedBy (A ^ k) k := by
  induction k with
  | zero =>
    intro i j hij
    have hij' : i = j := by
      by_contra hne
      simp [pow_zero, Matrix.one_apply_ne hne] at hij
    simp [hij']
  | succ k ih =>
    have := ih.mul hA
    rwa [← pow_succ] at this

private theorem GradedBy.eq_zero {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ} {d : ℕ}
    (hA : GradedBy A d) (hd : (n + 1) * n < d) : A = 0 := by
  ext i j
  by_contra hij
  have := hA i j hij
  have := domRank_le i
  omega

end Matrices

section Kostka

variable {n : ℕ}

/-- An auxiliary complex matrix indexed by partitions with natural-number entries. -/
noncomputable def Partition.auxiliaryNatMatrix (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) ℂ :=
  Matrix.of fun i j => (auxiliaryPartitionNat n j i : ℂ)

/-- An entry of the auxiliary natural-entry matrix is the cast of the corresponding auxiliary count. -/
theorem Partition.auxiliaryNatMatrix_apply (i j : Nat.Partition n) :
    Partition.auxiliaryNatMatrix n i j = (auxiliaryPartitionNat n j i : ℂ) := rfl

/-- Every diagonal entry of the auxiliary natural-entry matrix is one. -/
theorem Partition.auxiliaryNatMatrix_apply_self (i : Nat.Partition n) : Partition.auxiliaryNatMatrix n i i = 1 := by
  rw [Partition.auxiliaryNatMatrix_apply, auxiliaryPartitionNat_self]; norm_num

/-- An entry of the auxiliary natural-entry matrix vanishes unless its column is root-below its row. -/
theorem Partition.auxiliaryNatMatrix_apply_eq_zero_of_not_rootLe {i j : Nat.Partition n}
    (h : ¬ Partition.rootOrder j i) :
    Partition.auxiliaryNatMatrix n i j = 0 := by
  rw [Partition.auxiliaryNatMatrix_apply, Partition.auxiliaryCount_eq_zero_of_not_rootLe n j i h]
  norm_num

private theorem kostkaMatrix_triSupp : TriSupp (Partition.auxiliaryNatMatrix n) := by
  intro i j hij
  by_contra hd
  exact hij (Partition.auxiliaryNatMatrix_apply_eq_zero_of_not_rootLe
    (fun hr => hd (Partition.rootOrder.auxiliaryRelation_of_le hr)))

private noncomputable def kostkaNil (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) ℂ :=
  Partition.auxiliaryNatMatrix n - 1

private theorem kostkaNil_triSupp : TriSupp (kostkaNil n) := by
  intro i j hij
  by_cases h : i = j
  · exact h ▸ Partition.Dominates.refl i
  · refine kostkaMatrix_triSupp i j ?_
    intro hz
    apply hij
    simp [kostkaNil, Matrix.sub_apply, hz, Matrix.one_apply_ne h]

private theorem kostkaNil_gradedBy : GradedBy (kostkaNil n) 1 := by
  intro i j hij
  by_cases h : i = j
  · exfalso
    apply hij
    simp [kostkaNil, Matrix.sub_apply, h, Partition.auxiliaryNatMatrix_apply_self, Matrix.one_apply_eq]
  · have hdom : Partition.Dominates i j := kostkaNil_triSupp i j hij
    exact domRank_lt hdom (Ne.symm h)

private theorem kostkaNil_pow_eq_zero :
    kostkaNil n ^ ((n + 1) * n + 1) = 0 :=
  (kostkaNil_gradedBy.pow _).eq_zero (by omega)

private noncomputable def kostkaGeom (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) ℂ :=
  ∑ k ∈ Finset.range ((n + 1) * n + 1), (-kostkaNil n) ^ k

private theorem neg_kostkaNil_pow_eq_zero :
    (-kostkaNil n) ^ ((n + 1) * n + 1) = 0 := by
  rw [neg_pow, kostkaNil_pow_eq_zero, mul_zero]

private theorem kostkaMatrix_eq_neg : Partition.auxiliaryNatMatrix n = -(-kostkaNil n - 1) := by
  rw [kostkaNil]; abel

private theorem kostkaGeom_mul : kostkaGeom n * Partition.auxiliaryNatMatrix n = 1 := by
  have hgeom := geom_sum_mul (-kostkaNil n) ((n + 1) * n + 1)
  rw [neg_kostkaNil_pow_eq_zero] at hgeom
  rw [kostkaGeom, kostkaMatrix_eq_neg, mul_neg, hgeom]
  simp

private theorem mul_kostkaGeom : Partition.auxiliaryNatMatrix n * kostkaGeom n = 1 := by
  have hgeom := mul_geom_sum (-kostkaNil n) ((n + 1) * n + 1)
  rw [neg_kostkaNil_pow_eq_zero] at hgeom
  rw [kostkaGeom, kostkaMatrix_eq_neg, neg_mul, hgeom]
  simp

/-- An auxiliary complex matrix indexed by partitions. -/
noncomputable def Partition.auxiliaryInverseMatrix (n : ℕ) :
    Matrix (Nat.Partition n) (Nat.Partition n) ℂ := (Partition.auxiliaryNatMatrix n)⁻¹

/-- The auxiliary inverse matrix is a left inverse of the auxiliary natural-entry matrix. -/
theorem Partition.auxiliaryInverseMatrix_mul_auxiliaryNatMatrix : Partition.auxiliaryInverseMatrix n * Partition.auxiliaryNatMatrix n = 1 := by
  rw [Partition.auxiliaryInverseMatrix, Matrix.inv_eq_left_inv kostkaGeom_mul]
  exact kostkaGeom_mul

/-- The auxiliary inverse matrix is a right inverse of the auxiliary natural-entry matrix. -/
theorem Partition.auxiliaryNatMatrix_mul_auxiliaryInverseMatrix : Partition.auxiliaryNatMatrix n * Partition.auxiliaryInverseMatrix n = 1 := by
  rw [Partition.auxiliaryInverseMatrix, Matrix.inv_eq_left_inv kostkaGeom_mul]
  exact mul_kostkaGeom

/-- The auxiliary natural-entry matrix is a unit. -/
theorem Partition.isUnit_auxiliaryNatMatrix : IsUnit (Partition.auxiliaryNatMatrix n) :=
  ⟨⟨Partition.auxiliaryNatMatrix n, Partition.auxiliaryInverseMatrix n, Partition.auxiliaryNatMatrix_mul_auxiliaryInverseMatrix, Partition.auxiliaryInverseMatrix_mul_auxiliaryNatMatrix⟩,
    rfl⟩

/-- An entry of the auxiliary inverse matrix vanishes unless the column partition is root-below the row partition. -/
@[source_ref "Chapter5/Remark5.15.5" (role := supporting)]
theorem Partition.auxiliaryInverseMatrix_apply_eq_zero_of_not_rootLe {mu la : Nat.Partition n}
    (h : ¬ Partition.rootOrder la mu) : Partition.auxiliaryInverseMatrix n mu la = 0 := by
  have hgeom : Partition.auxiliaryInverseMatrix n = kostkaGeom n := by
    rw [Partition.auxiliaryInverseMatrix, Matrix.inv_eq_left_inv kostkaGeom_mul]
  have htri : TriSupp (kostkaGeom n) :=
    TriSupp.sum _ _ fun k _ => TriSupp.pow kostkaNil_triSupp.neg k
  by_contra hne
  rw [hgeom] at hne
  exact h
    (_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.rootLe_of_auxiliaryRelation
      (htri mu la hne))

/-- The auxiliary value of a partition and permutation is a sum over partitions weighted by matrix entries. -/
theorem Partition.auxiliaryValue_eq_matrix_sum (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    auxiliaryPartitionPermutationValue n la σ =
      ∑ mu : Nat.Partition n,
        Partition.auxiliaryInverseMatrix n mu la * (partitionPermutationValue n mu σ : ℂ) := by
  symm
  have hyoung : ∀ mu : Nat.Partition n, (partitionPermutationValue n mu σ : ℂ) =
      ∑ nu : Nat.Partition n, Partition.auxiliaryNatMatrix n nu mu * auxiliaryPartitionPermutationValue n nu σ := by
    intro mu
    rw [natCast_auxiliary_eq_sum_auxiliary_mul_auxiliary n mu σ]
    rfl
  calc ∑ mu : Nat.Partition n,
        Partition.auxiliaryInverseMatrix n mu la * (partitionPermutationValue n mu σ : ℂ)
      = ∑ mu : Nat.Partition n, ∑ nu : Nat.Partition n,
          (Partition.auxiliaryNatMatrix n nu mu * Partition.auxiliaryInverseMatrix n mu la) *
            auxiliaryPartitionPermutationValue n nu σ := by
        refine Finset.sum_congr rfl fun mu _ => ?_
        rw [hyoung mu, Finset.mul_sum]
        exact Finset.sum_congr rfl fun nu _ => by ring
    _ = ∑ nu : Nat.Partition n,
          (Partition.auxiliaryNatMatrix n * Partition.auxiliaryInverseMatrix n) nu la * auxiliaryPartitionPermutationValue n nu σ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun nu _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
    _ = auxiliaryPartitionPermutationValue n la σ := by
        rw [Partition.auxiliaryNatMatrix_mul_auxiliaryInverseMatrix]
        rw [Finset.sum_eq_single la]
        · rw [Matrix.one_apply_eq, one_mul]
        · intro b _ hb
          rw [Matrix.one_apply_ne hb, zero_mul]
        · intro h; exact absurd (Finset.mem_univ la) h

open Classical in

/-- The auxiliary matrix sum may be restricted to partitions above the given partition in the root relation. -/
@[source_ref "Chapter5/Remark5.15.5" (role := primary)]
theorem Partition.auxiliaryValue_eq_rootLe_matrix_sum (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    auxiliaryPartitionPermutationValue n la σ =
      ∑ mu ∈ Finset.univ.filter (fun mu : Nat.Partition n => Partition.rootOrder la mu),
        Partition.auxiliaryInverseMatrix n mu la * (partitionPermutationValue n mu σ : ℂ) := by
  rw [Partition.auxiliaryValue_eq_matrix_sum la σ]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro mu _ hmu
  rw [Partition.auxiliaryInverseMatrix_apply_eq_zero_of_not_rootLe (by simpa using hmu), zero_mul]

end Kostka

end RepresentationTheory.Combinatorics.Partition.RootOrderMatrices

/-- An auxiliary natural-valued function of a partition and a natural-number index. -/
alias _root_.RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.auxiliaryIndexedNatValue := _root_.RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.auxiliaryPartAt

/-- A partition's indexed part is zero at indices at least its size. -/
alias _root_.RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.partAt_eq_zero_of_length_le := _root_.RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.auxiliaryPartAt_eq_zero_of_length_le

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionLinearIndependence









namespace RepresentationTheory.AuxiliaryPartitionOrder

noncomputable section



private theorem youngRuleBlockCumulCount_eq_tabloidCumulCount {n : ℕ}
    (mu nu : Nat.Partition n) (sigma : Equiv.Perm (Fin n)) (a i m : ℕ)
    (hm : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take a).sum = m + 1) (hmn : m < n) :
    RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction mu nu sigma a i =
      RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToIndexedNatFunction nu sigma ⟨m, hmn⟩ i := by
  classical
  unfold RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationToIndexedNatFunction
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
  have he : e.val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum := by
    rw [RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n mu]
    exact e.isLt
  rw [RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) e.val a he, hm]
  omega


/-- The displayed relation between permutations yields pointwise inequalities between the associated natural-number values. -/
theorem auxiliary_nat_function_le_of_relation {n : ℕ}
    (mu nu : Nat.Partition n) {sigma tau : Equiv.Perm (Fin n)}
    (hdom : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationRel nu sigma tau) (a i : ℕ) :
    RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction mu nu tau a i ≤
      RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction mu nu sigma a i := by
  classical
  let b := ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take a).sum
  have hb_le : b ≤ n := by
    rw [← RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n mu]
    exact (List.take_sublist a (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu)).sum_le_sum (fun _ _ => Nat.zero_le _)
  cases hb : b with
  | zero =>
      unfold RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction
      have he : ∀ e : Fin n, ¬ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) e.val < a := by
        intro e hrow
        have hvalid : e.val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum := by
          rw [RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n mu]
          exact e.isLt
        rw [RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) e.val a hvalid] at hrow
        have hzero : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take a).sum = 0 := by
          simpa only [b] using hb
        omega
      simp only [he, false_and, Finset.filter_false, Finset.card_empty, le_refl]
  | succ m =>
      have hm : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take a).sum = m + 1 := by
        simpa only [b] using hb
      have hmn : m < n := by omega
      rw [youngRuleBlockCumulCount_eq_tabloidCumulCount mu nu tau a i m hm hmn,
        youngRuleBlockCumulCount_eq_tabloidCumulCount mu nu sigma a i m hm hmn]
      exact hdom ⟨m, hmn⟩ i



/-- An auxiliary relation on objects indexed by two partitions. -/
def _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.AuxiliaryRelation {n : ℕ} {nu mu : Nat.Partition n}
    (T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) : Prop :=
  ∀ a i : ℕ, U.auxiliaryNatFunction a i ≤ T.auxiliaryNatFunction a i

/-- Every auxiliary object is related to itself. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryRelation_refl {n : ℕ} {nu mu : Nat.Partition n}
    (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) : T.AuxiliaryRelation T :=
  fun _ _ => le_rfl

/-- The auxiliary relation is transitive. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryRelation_trans {n : ℕ} {nu mu : Nat.Partition n}
    {T U V : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu} (hTU : T.AuxiliaryRelation U)
    (hUV : U.AuxiliaryRelation V) : T.AuxiliaryRelation V :=
  fun a i => (hUV a i).trans (hTU a i)



/-- The displayed subgroup membership and permutation relation imply the auxiliary relation between the two objects. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryRelation_of_permutation {n : ℕ}
    {nu mu : Nat.Partition n} (T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (p : Equiv.Perm (Fin n)) (hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)
    (hdom : RepresentationTheory.Permutation.PartitionIndexedAuxiliary.permutationRel nu (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu T.toAuxiliaryObject)
      (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu U.toAuxiliaryObject * p)) :
    T.AuxiliaryRelation U := by
  intro a i
  rw [← RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction_standardization T,
    ← RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction_standardization U,
    ← RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliaryPermutationNatFunction_mul_eq mu nu
      (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu U.toAuxiliaryObject) p hp]
  exact auxiliary_nat_function_le_of_relation mu nu hdom a i


private theorem cell_mem_toYoungDiagram {n : ℕ} {nu : Nat.Partition n}
    (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) : c.1 ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) := by
  change c.1 ∈ YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) _
  rw [YoungDiagram.mem_ofRowLens]
  refine ⟨c.2.1, ?_⟩
  have hc := c.2.2
  rwa [List.getD_eq_getElem _ _ c.2.1] at hc


private noncomputable def KostkaTableau.rowProfile {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (a r : ℕ) : ℕ :=
  ((Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 = r).card


private theorem KostkaTableau.cumulativeProfile_succ {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (a r : ℕ) :
    T.auxiliaryNatFunction a (r + 1) =
      T.auxiliaryNatFunction a r + T.rowProfile a r := by
  classical
  let below := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 < r
  let atRow := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter fun c =>
    T.1 c.1.1 c.1.2 < a ∧ c.1.1 = r
  have hunion :
      ((Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter fun c =>
        T.1 c.1.1 c.1.2 < a ∧ c.1.1 < r + 1) = below ∪ atRow := by
    ext c
    simp only [below, atRow, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    omega
  have hdisj : Disjoint below atRow := by
    rw [Finset.disjoint_left]
    intro c hcBelow hcRow
    simp only [below, atRow, Finset.mem_filter, Finset.mem_univ, true_and] at hcBelow hcRow
    omega
  unfold RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryNatFunction KostkaTableau.rowProfile
  rw [hunion, Finset.card_union_of_disjoint hdisj]


private theorem KostkaTableau.rowProfile_eq_of_cumulativeProfile_eq {n : ℕ}
    {nu mu : Nat.Partition n} {T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu}
    (h : ∀ a i : ℕ, T.auxiliaryNatFunction a i = U.auxiliaryNatFunction a i)
    (a r : ℕ) : T.rowProfile a r = U.rowProfile a r := by
  have hT := T.cumulativeProfile_succ a r
  have hU := U.cumulativeProfile_succ a r
  rw [h a (r + 1), h a r] at hT
  omega



private theorem KostkaTableau.not_entry_lt_of_cumulativeProfile_eq {n : ℕ}
    {nu mu : Nat.Partition n} {T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu}
    (h : ∀ a i : ℕ, T.auxiliaryNatFunction a i = U.auxiliaryNatFunction a i)
    (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) : ¬ T.1 c.1.1 c.1.2 < U.1 c.1.1 c.1.2 := by
    intro hlt
    let a := U.1 c.1.1 c.1.2
    let left : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) := (Finset.univ.filter fun d =>
      d.1.1 = c.1.1 ∧ d.1.2 ≤ c.1.2)
    have hleft_card : left.card = c.1.2 + 1 := by
      rw [← Finset.card_range (c.1.2 + 1)]
      apply Finset.card_bij (fun d _ => d.1.2)
      · intro d hd
        rw [Finset.mem_range]
        simp only [left, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        omega
      · intro d₁ hd₁ d₂ hd₂ heq
        apply Subtype.ext
        have h₁ := (Finset.mem_filter.mp hd₁).2.1
        have h₂ := (Finset.mem_filter.mp hd₂).2.1
        exact Prod.ext (h₁.trans h₂.symm) heq
      · intro k hk
        rw [Finset.mem_range] at hk
        let d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu :=
          ⟨(c.1.1, k), c.2.1, lt_of_lt_of_le hk c.2.2⟩
        refine ⟨d, ?_, rfl⟩
        simp only [left, Finset.mem_filter, Finset.mem_univ, true_and, d]
        omega
    have hleft_subset : left ⊆ (Finset.univ.filter fun d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu =>
        T.1 d.1.1 d.1.2 < a ∧ d.1.1 = c.1.1) := by
      intro d hd
      simp only [left, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      refine ⟨?_, hd.1⟩
      have hweak : T.1 d.1.1 d.1.2 ≤ T.1 c.1.1 c.1.2 := by
        rw [hd.1]
        exact T.1.row_weak_of_le hd.2 (cell_mem_toYoungDiagram c)
      exact hweak.trans_lt hlt
    have hTlower : c.1.2 + 1 ≤ T.rowProfile a c.1.1 := by
      rw [← hleft_card]
      exact Finset.card_le_card hleft_subset
    have hUupper : U.rowProfile a c.1.1 ≤ c.1.2 := by
      let source := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter fun d =>
        U.1 d.1.1 d.1.2 < a ∧ d.1.1 = c.1.1
      change source.card ≤ c.1.2
      rw [← Finset.card_range c.1.2]
      apply Finset.card_le_card_of_injOn (fun d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu => d.1.2)
      · intro d hd
        rw [Finset.mem_coe, Finset.mem_range]
        simp only [source, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hd
        by_contra hnot
        have hweak : U.1 c.1.1 c.1.2 ≤ U.1 d.1.1 d.1.2 := by
          calc
            U.1 c.1.1 c.1.2 = U.1 d.1.1 c.1.2 := by rw [hd.2]
            _ ≤ U.1 d.1.1 d.1.2 :=
              U.1.row_weak_of_le (Nat.le_of_not_gt hnot) (cell_mem_toYoungDiagram d)
        exact (not_lt_of_ge hweak) hd.1
      · intro d₁ hd₁ d₂ hd₂ heq
        apply Subtype.ext
        have hrow₁ := (Finset.mem_filter.mp hd₁).2.2
        have hrow₂ := (Finset.mem_filter.mp hd₂).2.2
        exact Prod.ext (hrow₁.trans hrow₂.symm) heq
    have hroweq := KostkaTableau.rowProfile_eq_of_cumulativeProfile_eq h a c.1.1
    omega


private theorem KostkaTableau.eq_of_cumulativeProfile_eq {n : ℕ}
    {nu mu : Nat.Partition n} {T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu}
    (h : ∀ a i : ℕ, T.auxiliaryNatFunction a i = U.auxiliaryNatFunction a i) : T = U := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro r j
  by_cases hc : (r, j) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu)
  · have hc' := hc
    change (r, j) ∈ YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) _ at hc'
    rw [YoungDiagram.mem_ofRowLens] at hc'
    have hcol := hc'.2
    have hcol' : j < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu).getD r 0 := by
      rw [List.getD_eq_getElem _ _ hc'.1]
      exact hcol
    let c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu := ⟨(r, j), hc'.1, hcol'⟩
    change T.1 c.1.1 c.1.2 = U.1 c.1.1 c.1.2
    exact Nat.le_antisymm
      (Nat.le_of_not_gt (KostkaTableau.not_entry_lt_of_cumulativeProfile_eq
        (fun a i => (h a i).symm) c))
      (Nat.le_of_not_gt (KostkaTableau.not_entry_lt_of_cumulativeProfile_eq h c))
  · rw [T.1.zeros hc, U.1.zeros hc]


/-- Two auxiliary objects related in both directions are equal. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryRelation_antisymm {n : ℕ} {nu mu : Nat.Partition n}
    {T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu} (hTU : T.AuxiliaryRelation U)
    (hUT : U.AuxiliaryRelation T) : T = U := by
  apply KostkaTableau.eq_of_cumulativeProfile_eq
  intro a i
  exact Nat.le_antisymm (hUT a i) (hTU a i)




/-- An auxiliary partial-order structure on the partition-indexed objects. -/
instance _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.instPartialOrder {n : ℕ} {nu mu : Nat.Partition n} :
    PartialOrder (RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) where
  le T U := U.AuxiliaryRelation T
  le_refl T := T.auxiliaryRelation_refl
  le_trans T U V hTU hUV :=
    RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryRelation_trans hUV hTU
  le_antisymm T U hTU hUT := auxiliaryRelation_antisymm hUT hTU



/-- A nonzero auxiliary evaluation implies the corresponding order relation. -/
theorem auxiliary_le_of_evaluation_ne_zero {n : ℕ}
    (mu nu : Nat.Partition n) (T U : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu)
    (hne : RepresentationTheory.AuxiliaryPartitionLinearIndependence.auxiliaryCoordinate mu nu T
      (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu U) ≠ 0) :
    T ≤ U := by
  change RepresentationTheory.Auxiliary.MembershipSubtypes.membershipSubtypeLinearMap
    ((RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryAmbientToSubmodule n mu nu
      (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype U.toAuxiliaryObject)).1)
        (RepresentationTheory.Permutation.PartitionIndexedAuxiliary.objectToAuxiliaryType n nu T.toAuxiliaryObject) ≠ 0 at hne
  obtain ⟨p, hp⟩ :=
    RepresentationTheory.AuxiliaryPartitionPermutationAverages.auxiliary_exists_of_ne_zero U T hne
  exact RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliaryRelation_of_permutation U T p.val p.prop hp



/-- Nonvanishing of every diagonal auxiliary evaluation implies linear independence of the displayed family. -/
theorem auxiliary_linearIndependent_of_diagonal_evaluation_ne_zero {n : ℕ}
    (mu nu : Nat.Partition n)
    (hdiag : ∀ T,
      RepresentationTheory.AuxiliaryPartitionLinearIndependence.auxiliaryCoordinate mu nu T
        (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu T) ≠ 0) :
    LinearIndependent ℂ (RepresentationTheory.AuxiliaryPartitionIndexMaps.auxiliaryFamilyMap n mu nu) :=
  RepresentationTheory.AuxiliaryPartitionLinearIndependence.auxiliary_linearIndependent mu nu
    (auxiliary_le_of_evaluation_ne_zero mu nu) hdiag

end

end RepresentationTheory.AuxiliaryPartitionOrder

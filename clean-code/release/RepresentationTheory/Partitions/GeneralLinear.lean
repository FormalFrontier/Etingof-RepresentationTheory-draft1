/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.SymmetricGroup.PartitionDominance
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# General linear constructions indexed by partitions

Partition-indexed endomorphisms, submodules, and general linear representations, together with
rank-dependent vanishing and finite-dimensional formulas.
-/

open MvPolynomial Finset CategoryTheory

noncomputable section

namespace RepresentationTheory.Partitions.GeneralLinear

variable (k : Type*) [Field k]

/-- Defines a composite endomorphism of the partition-indexed ambient module. -/
def partitionIndexedCompositeEndomorphism (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.End k
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) :=
  RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
    k (Fin N → k) n
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer k n la)

/-- Defines an endomorphism of the ambient module associated with a partition and an ambient rank. -/
def partitionIndexedAlternatingEndomorphism (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.End k
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) :=
  haveI : DecidablePred
      (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :=
    Classical.decPred _
  RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
    k (Fin N → k) n
    (∑ g :
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
      ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • MonoidAlgebra.of k _ g.val)

/-- Defines an auxiliary endomorphism of the partition-indexed ambient module. -/
def partitionIndexedAuxiliaryEndomorphism (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.End k
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) :=
  haveI : DecidablePred
      (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la) :=
    Classical.decPred _
  RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
    k (Fin N → k) n
    (∑ g :
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la),
      MonoidAlgebra.of k _ g.val)

/-- Factors the composite endomorphism as the product of the alternating endomorphism and an auxiliary endomorphism. -/
theorem partitionIndexedCompositeEndomorphism_eq_alternating_mul_auxiliary
    (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    partitionIndexedCompositeEndomorphism k N la =
      partitionIndexedAlternatingEndomorphism k N la *
        partitionIndexedAuxiliaryEndomorphism k N la := by
  rw [partitionIndexedCompositeEndomorphism, partitionIndexedAlternatingEndomorphism,
    partitionIndexedAuxiliaryEndomorphism,
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionSymmetrizer, map_mul]

/-- Identifies the composite endomorphism for a partition created from a finite function with the corresponding function-indexed endomorphism. -/
theorem partitionIndexedCompositeEndomorphism_apply_partitionFromFunction
    (N : ℕ) (lam : Fin N → ℕ) :
    partitionIndexedCompositeEndomorphism k N
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam) =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.symmetrizerEndomorphism k N lam :=
  rfl

/-- Defines a rank-indexed natural-valued function associated with a partition. -/
def partitionPaddedFunction (N : ℕ) {n : ℕ} (la : Nat.Partition n) : Fin N → ℕ :=
  fun i =>
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD
      i.val 0

/-- The rank-indexed function associated with a partition is weakly decreasing. -/
theorem partitionPaddedFunction_antitone (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Antitone (partitionPaddedFunction N la) := by
  intro i j hij
  have hsorted :
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).Pairwise
        (· ≥ ·) := la.parts.pairwise_sort (· ≥ ·)
  have hij' : (i : ℕ) ≤ (j : ℕ) := hij
  simp only [partitionPaddedFunction]
  by_cases hj :
      (j : ℕ) <
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length
  · have hi :
        (i : ℕ) <
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length :=
      lt_of_le_of_lt hij' hj
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    rcases eq_or_lt_of_le hij' with h | h
    · simp [h]
    · exact List.pairwise_iff_getElem.mp hsorted _ _ hi hj h
  · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
    exact Nat.zero_le _

/-- The length of a partition's sorted-parts list equals the number of its parts. -/
theorem sortedParts_length_eq_parts_card (n : ℕ) (la : Nat.Partition n) :
    (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length =
      Multiset.card la.parts := by
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList,
    Multiset.length_sort]

/-- For an admissible rank, the values of the rank-indexed partition function are the sorted parts followed by enough zeros. -/
theorem partitionPaddedFunction_toList_eq_sortedParts_append_zeros
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hcard : Multiset.card la.parts ≤ N) :
    List.ofFn (partitionPaddedFunction N la) =
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) ++
        List.replicate
          (N -
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length)
          0 := by
  have hlen :
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length ≤
        N := by
    rw [sortedParts_length_eq_parts_card]; exact hcard
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro m h₁ h₂
    simp only [List.getElem_ofFn, partitionPaddedFunction]
    by_cases hm :
        m <
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length
    · rw [List.getD_eq_getElem _ _ hm, List.getElem_append_left hm]
    · rw [List.getD_eq_default _ _ (not_lt.mp hm),
        List.getElem_append_right (not_lt.mp hm), List.getElem_replicate]

/-- For an admissible rank, the sum of the rank-indexed partition function equals the size of the partition. -/
theorem sum_partitionPaddedFunction_eq_partitionSize_of_partitionLength_le_rank
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hcard : Multiset.card la.parts ≤ N) :
    ∑ i, partitionPaddedFunction N la i = n := by
  have hsum :
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum =
        n := by
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    have hcoe :
        ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) :
            Multiset ℕ).sum = la.parts.sum :=
      congrArg Multiset.sum h
    rw [Multiset.sum_coe] at hcoe
    rw [hcoe, la.parts_sum]
  rw [← List.sum_ofFn,
    partitionPaddedFunction_toList_eq_sortedParts_append_zeros N la hcard,
    List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero, add_zero, hsum]

/-- An admissible padded partition function reconstructs the original multiset of partition parts. -/
theorem partitionFromPaddedFunction_parts_eq_of_partitionLength_le_rank
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hcard : Multiset.card la.parts ≤ N) :
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N
        (partitionPaddedFunction N la)).parts = la.parts := by
  have hpos :
      ∀ x ∈
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la),
        0 < x := fun x hx => la.parts_pos ((Multiset.mem_sort _).mp hx)
  change Multiset.filter (0 < ·)
      (Multiset.map (partitionPaddedFunction N la) Finset.univ.val) = la.parts
  rw [Fin.univ_val_map, Multiset.filter_coe,
    partitionPaddedFunction_toList_eq_sortedParts_append_zeros N la hcard,
    List.filter_append]
  have h₁ :
      List.filter (fun b => decide (0 < b))
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) =
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) := by
    rw [List.filter_eq_self]
    exact fun x hx => decide_eq_true (hpos x hx)
  have h₂ :
      List.filter (fun b => decide (0 < b))
          (List.replicate
            (N -
              (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length)
            0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    simp
  rw [h₁, h₂, List.append_nil]
  exact Multiset.sort_eq la.parts (· ≥ ·)

/-- The permutation-dependent operator sends the element indexed by a function to the element indexed by precomposition with the inverse permutation. -/
theorem permutationOperator_apply_functionIndexedElement
    (N n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → Fin N) :
    (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv
        k (Fin N → k) n σ)
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n f) =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n
        (f ∘ σ.symm) := by
  simp only [RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis,
    _root_.Basis.piTensorProduct_apply,
    RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpacePermutationEquiv,
    PiTensorProduct.reindex_tprod, Function.comp, Pi.basisFun_apply]

/-- Evaluates the endomorphism as a signed sum indexed by permutations, with each summand obtained by inverse precomposition. -/
theorem partitionIndexedAlternatingEndomorphism_apply
    (N : ℕ) {n : ℕ} (la : Nat.Partition n) (f : Fin n → Fin N) :
    haveI : DecidablePred
        (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :=
      Classical.decPred _
    partitionIndexedAlternatingEndomorphism k N la
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n f) =
      ∑ g :
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
        ((↑(Equiv.Perm.sign g.val) : ℤ) : k) •
          RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n
            (f ∘ g.val.symm) := by
  haveI : DecidablePred
      (· ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :=
    Classical.decPred _
  rw [partitionIndexedAlternatingEndomorphism, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  congr 1
  change
    (RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction
        k (Fin N → k) n (MonoidAlgebra.single g.val 1))
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n f) = _
  rw [RepresentationTheory.Auxiliary.MutualCentralizers.permutationGroupAlgebraAction,
    MonoidAlgebra.lift_single, one_smul]
  exact permutationOperator_apply_functionIndexedElement k N n g.val f

/-- If the number of parts exceeds the ambient rank, every map has distinct indices where both the specified sorted-parts construction and the map agree. -/
theorem exists_ne_with_sortedPartsData_eq_and_apply_eq_of_rank_lt_partitionLength
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) (f : Fin n → Fin N) :
    ∃ i j : Fin n, i ≠ j ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
          i.val =
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
          j.val ∧
      f i = f j := by
  classical
  have hlsum :
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum =
        n := by
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    have hcoe :
        ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) :
            Multiset ℕ).sum = la.parts.sum :=
      congrArg Multiset.sum h
    rw [Multiset.sum_coe] at hcoe
    rw [hcoe, la.parts_sum]
  have hcell :
      ∀ r : Fin
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length,
        ∃ m,
          m <
              (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum ∧
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow
                (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
                m = r.val ∧
              RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn
                  (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
                  m = 0 := by
    intro r
    refine
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
        r.val 0 ?_
    rw [List.getD_eq_getElem _ _ r.isLt]
    exact la.parts_pos ((Multiset.mem_sort _).mp (List.getElem_mem r.isLt))
  choose F hFlt hFrow hFcol using hcell
  set G :
      Fin
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length →
        Fin n := fun r => ⟨F r, by rw [← hlsum]; exact hFlt r⟩ with hG
  have hcard :
      Fintype.card (Fin N) <
        Fintype.card
          (Fin
            (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length) := by
    rw [Fintype.card_fin, Fintype.card_fin, sortedParts_length_eq_parts_card]
    exact hN
  obtain ⟨r, s, hrs, hfg⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun r => f (G r)) hcard
  refine ⟨G r, G s, fun h => hrs ?_, ?_, hfg⟩
  · have hval : F r = F s := congrArg Fin.val h
    exact Fin.ext (by rw [← hFrow r, ← hFrow s, hval])
  · change
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
          (F r) =
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)
          (F s)
    rw [hFcol r, hFcol s]

variable [CharZero k]

/-- The alternating endomorphism is zero when the ambient rank is smaller than the partition length. -/
theorem partitionIndexedAlternatingEndomorphism_eq_zero_of_rank_lt_partitionLength
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) :
    partitionIndexedAlternatingEndomorphism k N la = 0 := by
  classical
  refine
    Module.Basis.ext
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n)
      fun f => ?_
  rw [LinearMap.zero_apply, partitionIndexedAlternatingEndomorphism_apply]
  obtain ⟨i, j, hij, hcol, hf⟩ :=
    exists_ne_with_sortedPartsData_eq_and_apply_eq_of_rank_lt_partitionLength N la hN f
  set τ : Equiv.Perm (Fin n) := Equiv.swap i j with hτdef
  have hτmem :
      τ ∈
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la :=
    RepresentationTheory.SymmetricGroup.PartitionDominance.swap_mem_of_column_eq hcol
  have hfτ : ∀ x, f (τ.symm x) = f x := by
    intro x
    rw [hτdef, Equiv.symm_swap]
    rcases eq_or_ne x i with rfl | hx
    · rw [Equiv.swap_apply_left]; exact hf.symm
    · rcases eq_or_ne x j with rfl | hx'
      · rw [Equiv.swap_apply_right]; exact hf
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  set S :=
    ∑ g :
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la),
      ((↑(Equiv.Perm.sign g.val) : ℤ) : k) •
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n
          (f ∘ g.val.symm) with hS
  have hneg : S = -S := by
    conv_lhs =>
      rw [hS, ← Equiv.sum_comp
        (Equiv.mulRight
          (⟨τ, hτmem⟩ :
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la))]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hcomp :
        f ∘
            ((g * ⟨τ, hτmem⟩ :
                RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
              Equiv.Perm (Fin n)).symm =
          f ∘ (g : Equiv.Perm (Fin n)).symm := by
      funext x
      exact hfτ ((g : Equiv.Perm (Fin n)).symm x)
    have hsign :
        Equiv.Perm.sign
            ((g * ⟨τ, hτmem⟩ :
                RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la) :
              Equiv.Perm (Fin n)) =
          -Equiv.Perm.sign (g : Equiv.Perm (Fin n)) := by
      change Equiv.Perm.sign ((g : Equiv.Perm (Fin n)) * τ) = _
      rw [map_mul, hτdef, Equiv.Perm.sign_swap hij]
      exact mul_neg_one _
    simp only [Equiv.coe_mulRight, hcomp, hsign, Int.cast_neg, Units.val_neg]
    exact
      @neg_smul k
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n)
        inferInstance inferInstance inferInstance
        (((Equiv.Perm.sign (g : Equiv.Perm (Fin n)) : ℤ) : k))
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.piTensorProductBasis k N n
          (f ∘ (g : Equiv.Perm (Fin n)).symm))
  have : (2 : k) • S = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    exact add_neg_cancel S
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  calc
    S = (2 : k)⁻¹ • ((2 : k) • S) := by
      rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    _ = 0 := by rw [this, smul_zero]

/-- The composite endomorphism is zero when the ambient rank is smaller than the partition length. -/
theorem partitionIndexedCompositeEndomorphism_eq_zero_of_rank_lt_partitionLength
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) :
    partitionIndexedCompositeEndomorphism k N la = 0 := by
  rw [partitionIndexedCompositeEndomorphism_eq_alternating_mul_auxiliary,
    partitionIndexedAlternatingEndomorphism_eq_zero_of_rank_lt_partitionLength k N la hN,
    zero_mul]

end RepresentationTheory.Partitions.GeneralLinear

namespace RepresentationTheory.Partitions.GeneralLinear

variable (k : Type*) [Field k]

/-- The composite endomorphism commutes with each specified operator indexed by the general linear group. -/
theorem partitionIndexedCompositeEndomorphism_commutes_with_generalLinearOperator
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g ∘ₗ
        partitionIndexedCompositeEndomorphism k N la =
      partitionIndexedCompositeEndomorphism k N la ∘ₗ
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g := by
  set V := Fin N → k
  have h_sym :
      (partitionIndexedCompositeEndomorphism k N la :
          Module.End k
            (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) ∈
        (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n :
          Set
            (Module.End k
              (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))) := by
    rw [←
      RepresentationTheory.Auxiliary.MutualCentralizers.range_permutationGroupAlgebraAction
        k V n]
    exact ⟨_, rfl⟩
  have h_diag :
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g :
          Module.End k
            (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) ∈
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n :
          Set
            (Module.End k
              (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))) :=
    Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩
  have hcent :=
    RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
      k V n h_diag
  rw [Subalgebra.mem_centralizer_iff] at hcent
  exact (hcent _ h_sym).symm

/-- The range of the composite endomorphism is preserved by each specified operator indexed by the general linear group. -/
theorem partitionIndexedCompositeEndomorphism_range_stable_under_generalLinearOperator
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (v : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n)
    (hv : v ∈ LinearMap.range (partitionIndexedCompositeEndomorphism k N la)) :
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g) v ∈
      LinearMap.range (partitionIndexedCompositeEndomorphism k N la) := by
  obtain ⟨w, rfl⟩ := hv
  exact
    ⟨(RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g) w,
      (LinearMap.ext_iff.mp
        (partitionIndexedCompositeEndomorphism_commutes_with_generalLinearOperator k N la g)
        w).symm⟩

/-- Defines a partition-indexed submodule of the specified ambient module built from the function space. -/
def partitionIndexedSubmodule (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Submodule k
      (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n) :=
  LinearMap.range (partitionIndexedCompositeEndomorphism k N la)

/-- Provides the additive commutative group structure on the carrier of the partition-indexed submodule. -/
noncomputable local instance (priority := high) partitionIndexedSubmodule_addCommGroup
    (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    AddCommGroup (partitionIndexedSubmodule k N la) :=
  { Module.addCommMonoidToAddCommGroup k with
    toAddCommMonoid := (partitionIndexedSubmodule k N la).addCommMonoid }

/-- Defines the general linear representation carried by the partition-indexed submodule. -/
def partitionIndexedSubmoduleRepresentation (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (partitionIndexedSubmodule k N la) where
  toFun g :=
    (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation k N n g).restrict
      (p := partitionIndexedSubmodule k N la) (q := partitionIndexedSubmodule k N la)
      (fun v hv =>
        partitionIndexedCompositeEndomorphism_range_stable_under_generalLinearOperator
          k N la g v hv)
  map_one' := by
    ext ⟨v, hv⟩
    simp only [LinearMap.coe_restrict_apply]
    exact
      LinearMap.ext_iff.mp
        (map_one
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation
            k N _))
        v
  map_mul' g₁ g₂ := by
    ext ⟨v, hv⟩
    have h_mul :=
      LinearMap.ext_iff.mp
        (map_mul
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.tensorPowerRepresentation
            k N n)
          g₁ g₂)
        v
    simp only [LinearMap.coe_restrict_apply, Module.End.mul_apply] at h_mul ⊢
    exact h_mul

/-- The carrier of the partition-indexed submodule is a finite module over the coefficient field. -/
instance partitionIndexedSubmodule_moduleFinite (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.Finite k (partitionIndexedSubmodule k N la) :=
  inferInstance

/-- Associates a finite-dimensional representation of the general linear group to a partition and an ambient rank over an algebraically closed field. -/
@[reducible] def partitionIndexedGeneralLinearRepresentation
    (k : Type*) [Field k] [IsAlgClosed k]
    (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  @FDRep.of k (Matrix.GeneralLinearGroup (Fin N) k) inferInstance inferInstance
    (partitionIndexedSubmodule k N la) inferInstance inferInstance inferInstance
    (partitionIndexedSubmoduleRepresentation k N la)

/-- Identifies the submodule for a partition built from a finite function with the corresponding function-indexed submodule. -/
theorem partitionIndexedSubmodule_apply_partitionFromFunction
    (N : ℕ) (lam : Fin N → ℕ) :
    partitionIndexedSubmodule k N
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam) =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N lam :=
  rfl

/-- Identifies the representation for a partition formed from a finite function with the corresponding function-indexed representation. -/
theorem partitionIndexedGeneralLinearRepresentation_apply_partitionFromFunction
    (k : Type*) [Field k] [IsAlgClosed k]
    (N : ℕ) (lam : Fin N → ℕ) :
    partitionIndexedGeneralLinearRepresentation k N
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam) =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam :=
  rfl

variable [CharZero k]

/-- The partition-indexed submodule is bottom when the ambient rank is smaller than the number of partition parts. -/
theorem partitionIndexedSubmodule_eq_bot_of_rank_lt_partitionLength
    (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) : partitionIndexedSubmodule k N la = ⊥ := by
  rw [partitionIndexedSubmodule,
    partitionIndexedCompositeEndomorphism_eq_zero_of_rank_lt_partitionLength k N la hN,
    LinearMap.range_zero]

/-- The specified value of a rank-indexed function is positive whenever that function is weakly decreasing. -/
theorem associatedValue_pos_of_antitone
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    0 < RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurDimension N lam := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  have h1 : (lam j : ℚ) ≤ (lam i : ℚ) := by
    exact_mod_cast hlam (le_of_lt hij)
  have h2 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by
    exact_mod_cast (Fin.lt_def.mp hij)
  exact div_pos (by linarith) (by linarith)

/-- The partition-indexed submodule is nontrivial when the number of partition parts does not exceed the ambient rank. -/
theorem partitionIndexedSubmodule_ne_bot_of_partitionLength_le_rank
    [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (hcard : Multiset.card la.parts ≤ N) :
    partitionIndexedSubmodule k N la ≠ ⊥ := by
  obtain ⟨lam, hanti, hsum, hparts⟩ :
      ∃ lam : Fin N → ℕ, Antitone lam ∧
        (∑ i, lam i) = n ∧
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam).parts =
            la.parts :=
    ⟨partitionPaddedFunction N la, partitionPaddedFunction_antitone N la,
      sum_partitionPaddedFunction_eq_partitionSize_of_partitionLength_le_rank N la hcard,
      partitionFromPaddedFunction_parts_eq_of_partitionLength_le_rank N la hcard⟩
  clear hcard
  subst hsum
  have hla :
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam = la :=
    Nat.Partition.ext hparts
  subst hla
  rw [partitionIndexedSubmodule_apply_partitionFromFunction]
  intro hbot
  have hdim :
      (Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam) :
          ℚ) =
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurDimension N lam :=
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.finrank_schurRepresentation_eq
      k N lam hanti
  have hzero :
      Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N lam) =
        0 :=
    Submodule.finrank_eq_zero.mpr hbot
  rw [show
      Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam) =
        Module.finrank k
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N lam) from
      rfl, hzero] at hdim
  exact
    absurd hdim.symm
      (ne_of_gt (associatedValue_pos_of_antitone N lam hanti))

/-- Characterizes when the partition-indexed submodule is bottom by comparison of ambient rank and partition length. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := primary)]
theorem partitionIndexedSubmodule_eq_bot_iff_rank_lt_partitionLength
    [IsAlgClosed k] (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    partitionIndexedSubmodule k N la = ⊥ ↔ N < Multiset.card la.parts := by
  refine
    ⟨fun hbot => ?_, partitionIndexedSubmodule_eq_bot_of_rank_lt_partitionLength k N la⟩
  by_contra hle
  exact
    partitionIndexedSubmodule_ne_bot_of_partitionLength_le_rank
      k N la (not_lt.mp hle) hbot

/-- Characterizes when the partition-indexed submodule is nontrivial by comparison of partition length and ambient rank. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := supporting)]
theorem partitionIndexedSubmodule_ne_bot_iff_partitionLength_le_rank
    [IsAlgClosed k] (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    partitionIndexedSubmodule k N la ≠ ⊥ ↔ Multiset.card la.parts ≤ N := by
  rw [ne_eq, partitionIndexedSubmodule_eq_bot_iff_rank_lt_partitionLength, not_lt]

/-- The associated representation has zero finite dimension exactly when the ambient rank is smaller than the partition length. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := supporting)]
theorem partitionIndexedRepresentation_finrank_eq_zero_iff_rank_lt_partitionLength
    [IsAlgClosed k] (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.finrank k (partitionIndexedGeneralLinearRepresentation k N la) = 0 ↔
      N < Multiset.card la.parts := by
  rw [show
      Module.finrank k (partitionIndexedGeneralLinearRepresentation k N la) =
        Module.finrank k (partitionIndexedSubmodule k N la) from
      rfl,
    Submodule.finrank_eq_zero,
    partitionIndexedSubmodule_eq_bot_iff_rank_lt_partitionLength]

/-- For a weakly decreasing finite function with the prescribed sum and partition parts, the specified value of the representation equals the corresponding function value. -/
theorem partitionIndexedRepresentation_associatedValue_eq_of_matchingFunction
    [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (lam : Fin N → ℕ) (hanti : Antitone lam)
    (hsum : (∑ i, lam i) = n)
    (hparts :
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam).parts =
        la.parts) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N
        (partitionIndexedGeneralLinearRepresentation k N la) =
      RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam := by
  subst hsum
  have hla :
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam = la :=
    Nat.Partition.ext hparts
  subst hla
  rw [partitionIndexedGeneralLinearRepresentation_apply_partitionFromFunction]
  exact
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter_schurRepresentation_eq
      k N lam hanti

/-- For a weakly decreasing finite function with the prescribed sum and partition parts, the cast finite rank equals the corresponding specified value. -/
theorem partitionIndexedRepresentation_finrank_cast_eq_associatedValue_of_matchingFunction
    [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (lam : Fin N → ℕ) (hanti : Antitone lam)
    (hsum : (∑ i, lam i) = n)
    (hparts :
      (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam).parts =
        la.parts) :
    (Module.finrank k (partitionIndexedGeneralLinearRepresentation k N la) : ℚ) =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurDimension N lam := by
  subst hsum
  have hla :
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam = la :=
    Nat.Partition.ext hparts
  subst hla
  change
    (Module.finrank k
        (partitionIndexedSubmodule k N
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N lam)) :
        ℚ) = _
  rw [partitionIndexedSubmodule_apply_partitionFromFunction]
  exact
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.finrank_schurRepresentation_eq
      k N lam hanti

/-- In admissible rank, the specified representation-dependent value equals the corresponding value of the rank-indexed partition function. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := primary)]
theorem partitionIndexedRepresentation_associatedValue_eq_of_partitionLength_le_rank
    [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (hcard : Multiset.card la.parts ≤ N) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N
        (partitionIndexedGeneralLinearRepresentation k N la) =
      RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N
        (partitionPaddedFunction N la) :=
  partitionIndexedRepresentation_associatedValue_eq_of_matchingFunction
    k N la (partitionPaddedFunction N la) (partitionPaddedFunction_antitone N la)
    (sum_partitionPaddedFunction_eq_partitionSize_of_partitionLength_le_rank N la hcard)
    (partitionFromPaddedFunction_parts_eq_of_partitionLength_le_rank N la hcard)

/-- In admissible rank, the cast of the finite rank of the associated representation equals the specified value of its rank-indexed partition function. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := supporting)]
theorem partitionIndexedRepresentation_finrank_cast_eq_associatedValue
    [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (hcard : Multiset.card la.parts ≤ N) :
    (Module.finrank k (partitionIndexedGeneralLinearRepresentation k N la) : ℚ) =
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurDimension N
        (partitionPaddedFunction N la) :=
  partitionIndexedRepresentation_finrank_cast_eq_associatedValue_of_matchingFunction
    k N la (partitionPaddedFunction N la) (partitionPaddedFunction_antitone N la)
    (sum_partitionPaddedFunction_eq_partitionSize_of_partitionLength_le_rank N la hcard)
    (partitionFromPaddedFunction_parts_eq_of_partitionLength_le_rank N la hcard)

/-- Records the bottom criterion for the partition-indexed submodule and, in admissible rank, two equalities involving its associated representation. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := primary),
  source_ref "Chapter5/Discussion_after_Theorem5.22.1" (role := supporting)]
theorem partitionIndexedSubmodule_vanishing_and_representationFormulas
    [IsAlgClosed k] (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    (partitionIndexedSubmodule k N la = ⊥ ↔ N < Multiset.card la.parts) ∧
      (Multiset.card la.parts ≤ N →
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N
              (partitionIndexedGeneralLinearRepresentation k N la) =
            RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N
              (partitionPaddedFunction N la) ∧
          (Module.finrank k (partitionIndexedGeneralLinearRepresentation k N la) : ℚ) =
            RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurDimension N
              (partitionPaddedFunction N la)) :=
  ⟨partitionIndexedSubmodule_eq_bot_iff_rank_lt_partitionLength k N la,
    fun hcard =>
      ⟨partitionIndexedRepresentation_associatedValue_eq_of_partitionLength_le_rank
          k N la hcard,
        partitionIndexedRepresentation_finrank_cast_eq_associatedValue k N la hcard⟩⟩

/-- A specified partition of the natural number two. -/
def selectedPartitionOfTwo : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by decide
  parts_sum := by decide

/-- The selected partition of two has exactly two parts. -/
theorem selectedPartitionOfTwo_parts_card_eq_two :
    Multiset.card selectedPartitionOfTwo.parts = 2 := by
  decide

/-- Over the complex numbers, the submodule indexed by the selected partition of two is bottom in rank one. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := supporting)]
theorem selectedPartitionOfTwo_complexSubmodule_rank_one_eq_bot :
    partitionIndexedSubmodule ℂ 1 selectedPartitionOfTwo = ⊥ := by
  rw [partitionIndexedSubmodule_eq_bot_iff_rank_lt_partitionLength]
  decide

/-- Over the complex numbers, the submodule indexed by the selected partition of two is nonzero in rank two. -/
@[source_ref "Chapter5/Theorem5.22.1" (role := supporting)]
theorem selectedPartitionOfTwo_complexSubmodule_rank_two_ne_bot :
    partitionIndexedSubmodule ℂ 2 selectedPartitionOfTwo ≠ ⊥ := by
  rw [partitionIndexedSubmodule_ne_bot_iff_partitionLength_le_rank]
  decide

end RepresentationTheory.Partitions.GeneralLinear

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.YoungDiagram.PartitionFormulas

noncomputable section

namespace RepresentationTheory.Auxiliary.PartitionPermutationRelations

open scoped Classical

/-- An auxiliary monoid homomorphism from permutations of a finite type to permutations of its successor. -/
noncomputable def Auxiliary.permutation_hom_succ (n : ℕ) :
    Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb

/-- An auxiliary finite set of partitions of the predecessor associated with a partition of successor size. -/
noncomputable def Auxiliary.partition_finset_pred {n : ℕ} (μ : Nat.Partition (n + 1)) :
    Finset (Nat.Partition n) :=
  Finset.univ.filter fun la => (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) ≤ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ)

/-- An auxiliary finite set of partitions of the successor associated with a partition. -/
noncomputable def Auxiliary.partition_finset_succ {n : ℕ} (μ : Nat.Partition n) :
    Finset (Nat.Partition (n + 1)) :=
  Finset.univ.filter fun la => (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ) ≤ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la)

/-- An auxiliary complex-valued operation on two complex-valued functions on permutations of a finite type. -/
noncomputable def Auxiliary.complex_function_operation (n : ℕ)
    (χ ψ : Equiv.Perm (Fin n) → ℂ) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), χ σ * ψ σ⁻¹

/-- Applying the auxiliary multiset-valued map after the successor permutation homomorphism adjoins one to its original value. -/
lemma Auxiliary.multiset_value_permutation_hom_succ (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset (n + 1) (Auxiliary.permutation_hom_succ n σ) = 1 ::ₘ RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset n σ := by
  have hct : (Auxiliary.permutation_hom_succ n σ).cycleType = σ.cycleType := by
    rw [Auxiliary.permutation_hom_succ, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
    simp only [Equiv.Perm.cycleType_extendDomain]
  have hsupp : (Auxiliary.permutation_hom_succ n σ).support.card = σ.support.card := by
    rw [Auxiliary.permutation_hom_succ, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
    simp only [Equiv.Perm.card_support_extend_domain]
  have hle : σ.support.card ≤ n := σ.support.card_le_univ.trans_eq (Fintype.card_fin n)
  unfold RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset
  rw [hct, hsupp, show n + 1 - σ.support.card = (n - σ.support.card) + 1 from by omega,
    Multiset.replicate_succ, Multiset.add_cons]

/-- The partial power-sum expression after the successor permutation homomorphism equals the sum of all variables multiplied by the original partial power-sum expression. -/
lemma Auxiliary.psum_part_permutation_hom_succ (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.psumPart (Fin (n + 1)) ℚ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType (Auxiliary.permutation_hom_succ n σ)) =
      (∑ i, MvPolynomial.X i) *
        MvPolynomial.psumPart (Fin (n + 1)) ℚ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType σ) := by
  simp only [MvPolynomial.psumPart]
  rw [show (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType (Auxiliary.permutation_hom_succ n σ)).parts = RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset (n + 1) (Auxiliary.permutation_hom_succ n σ) from
      rfl, Auxiliary.multiset_value_permutation_hom_succ n σ,
    show (1 ::ₘ RepresentationTheory.PermutationPolynomialAuxiliary.permutationNatMultiset n σ) = (1 : ℕ) ::ₘ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType σ).parts from rfl,
    Multiset.map_cons, Multiset.prod_cons, MvPolynomial.psum_one]

/-- One Young diagram is at most another exactly when each of its row lengths is at most the corresponding row length. -/
lemma YoungDiagram.le_iff_row_len_le {μ ν : YoungDiagram} :
    μ ≤ ν ↔ ∀ i, μ.rowLen i ≤ ν.rowLen i := by
  constructor
  · intro h i
    rcases Nat.eq_zero_or_pos (μ.rowLen i) with hz | hz
    · omega
    · have hmem : (i, μ.rowLen i - 1) ∈ μ := by rw [YoungDiagram.mem_iff_lt_rowLen]; omega
      have := SetLike.le_def.mp h hmem
      rw [YoungDiagram.mem_iff_lt_rowLen] at this; omega
  · intro h
    rw [SetLike.le_def]
    rintro ⟨i, j⟩ hc
    rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
    exact lt_of_lt_of_le hc (h i)

/-- A partition has row length zero at every index greater than or equal to its size. -/
lemma partition_row_len_eq_zero_of_size_le {n : ℕ} (la : Nat.Partition n) {i : ℕ} (hi : n ≤ i) :
    (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i = 0 := by
  classical
  by_contra hne
  have hmem : (i, 0) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have hsub : (Finset.range (i + 1)).image (fun k => ((k, 0) : ℕ × ℕ)) ⊆
      (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells := by
    intro c hc'
    simp only [Finset.mem_image, Finset.mem_range] at hc'
    obtain ⟨k, hk, rfl⟩ := hc'
    exact (YoungDiagram.mem_cells _).mpr
      ((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).isLowerSet (show ((k, 0) : ℕ × ℕ) ≤ (i, 0) from ⟨by omega, le_refl 0⟩)
        hmem)
  have h1 : ((Finset.range (i + 1)).image (fun k => ((k, 0) : ℕ × ℕ))).card ≤
      (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells.card := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range,
    RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.card_toYoungDiagram_cells la] at h1
  omega

/-- The row lengths of a partition, summed over indices below its size, add up to that size. -/
lemma partition_sum_row_len (n : ℕ) (la : Nat.Partition n) :
    ∑ i : Fin (n + 1), (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i.val = n := by
  classical
  have hcell : ∀ i j : ℕ, (i, j) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells → i < n + 1 := by
    intro i j hc
    by_contra h
    have := (YoungDiagram.mem_cells _).mp hc
    rw [YoungDiagram.mem_iff_lt_rowLen] at this
    rw [partition_row_len_eq_zero_of_size_le la (by omega)] at this
    omega
  have hbi : (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells = Finset.univ.biUnion
      (fun i : Fin (n + 1) =>
        ({i.val} : Finset ℕ) ×ˢ Finset.range ((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i.val)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_range]
    constructor
    · intro hc
      exact ⟨⟨i, hcell i j hc⟩, rfl,
        (YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells _).mp hc))⟩
    · rintro ⟨i', rfl, hj⟩
      exact (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  have hsum : (∑ i : Fin (n + 1), (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i.val)
      = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells.card := by
    rw [hbi, Finset.card_biUnion (fun x _ y _ hxy => Finset.disjoint_left.mpr (by
      rintro ⟨a, b⟩ ha hb
      simp only [Finset.mem_product, Finset.mem_singleton] at ha hb
      exact hxy (Fin.val_injective (ha.1.symm.trans hb.1))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul]
  rw [hsum, RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.card_toYoungDiagram_cells la]

/-- Positive natural-number lists are equal if their zero-defaulted entries agree at every index. -/
lemma List.eq_of_get_d_zero_eq_of_pos {L M : List ℕ} (hL : ∀ x ∈ L, 0 < x) (hM : ∀ x ∈ M, 0 < x)
    (h : ∀ i, L.getD i 0 = M.getD i 0) : L = M := by
  apply List.ext_getElem?
  intro i
  rcases lt_or_ge i L.length with hiL | hiL
  · rcases lt_or_ge i M.length with hiM | hiM
    · rw [List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hiM]
      have := h i
      rw [List.getD_eq_getElem _ _ hiL, List.getD_eq_getElem _ _ hiM] at this
      rw [this]
    · exfalso
      have hLi : 0 < L.getD i 0 := by
        rw [List.getD_eq_getElem _ _ hiL]; exact hL _ (List.getElem_mem _)
      rw [h i, List.getD_eq_default _ _ hiM] at hLi; exact absurd hLi (lt_irrefl 0)
  · rcases lt_or_ge i M.length with hiM | hiM
    · exfalso
      have hMi : 0 < M.getD i 0 := by
        rw [List.getD_eq_getElem _ _ hiM]; exact hM _ (List.getElem_mem _)
      rw [← h i, List.getD_eq_default _ _ hiL] at hMi; exact absurd hMi (lt_irrefl 0)
    · rw [List.getElem?_eq_none hiL, List.getElem?_eq_none hiM]

/-- Constructs an auxiliary successor-indexed object from a partition. -/
noncomputable def Auxiliary.construct_from_partition {n : ℕ} (la : Nat.Partition n) : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (n + 1) n where
  parts i := (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i.val
  parts_antitone i j hij := (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen_anti i.val j.val hij
  sum_parts := partition_sum_row_len n la

/-- Converting the parts of the auxiliary object constructed from a partition recovers the original partition. -/
lemma Auxiliary.convert_construct_from_partition {n : ℕ} (la : Nat.Partition n) :
    ((Auxiliary.construct_from_partition la).sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple (n + 1) (Auxiliary.construct_from_partition la).parts : Nat.Partition n) = la := by
  have hrec : ∀ (p q : ℕ) (heq : p = q) (P : Nat.Partition p), (heq ▸ P).parts = P.parts := by
    intro p q heq P; subst heq; rfl
  set WP := RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple (n + 1) (Auxiliary.construct_from_partition la).parts with hWP

  have hrl : ∀ i : ℕ, (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition WP).rowLen i = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i := by
    intro i
    rcases lt_or_ge i (n + 1) with hi | hi
    · rw [hWP, RepresentationTheory.YoungDiagram.PartitionFormulas.toYoungDiagram_rowLen_eq_parts (n + 1) (Auxiliary.construct_from_partition la) ⟨i, hi⟩]; rfl
    · rw [hWP, RepresentationTheory.YoungDiagram.PartitionFormulas.toYoungDiagram_rowLen_eq_zero_of_bound (n + 1) _ hi,
        partition_row_len_eq_zero_of_size_le la (by omega)]

  have hsp : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList WP) = (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) := by
    apply List.eq_of_get_d_zero_eq_of_pos
    · intro x hx; exact WP.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro x hx; exact la.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro i
      have := hrl i
      rwa [RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD,
        RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD] at this
  apply Nat.Partition.ext
  rw [hrec _ _ (Auxiliary.construct_from_partition la).sum_parts]
  have hWPp : WP.parts = ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList WP) := (Multiset.sort_eq _ _).symm
  have hlap : la.parts = ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) := (Multiset.sort_eq _ _).symm
  rw [hWPp, hlap, hsp]

/-- Each part of an auxiliary object agrees with the corresponding row length after its parts are converted to a partition. -/
lemma Auxiliary.parts_eq_converted_partition_row_len {N m : ℕ} (bp : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition N m) (i : Fin N) :
    bp.parts i =
      (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (bp.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple N bp.parts : Nat.Partition m)).rowLen i.val := by
  have hrec : ∀ (p q : ℕ) (heq : p = q) (P : Nat.Partition p),
      (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (heq ▸ P)) = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition P) := by intro p q heq P; subst heq; rfl
  rw [hrec _ _ bp.sum_parts, RepresentationTheory.YoungDiagram.PartitionFormulas.toYoungDiagram_rowLen_eq_parts N bp i]

/-- Two partitions are equal when their Young diagrams have the same row length at every natural index. -/
lemma partition_eq_of_row_len_eq {n : ℕ} {p q : Nat.Partition n}
    (h : ∀ i, (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition p).rowLen i = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition q).rowLen i) : p = q := by
  have hsp : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList p) = (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList q) := by
    apply List.eq_of_get_d_zero_eq_of_pos
    · intro x hx; exact p.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro x hx; exact q.parts_pos ((Multiset.mem_sort _).mp hx)
    · intro i
      have := h i
      rwa [RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD,
        RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD] at this
  apply Nat.Partition.ext
  rw [show p.parts = ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList p) from (Multiset.sort_eq _ _).symm,
    show q.parts = ↑(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList q) from (Multiset.sort_eq _ _).symm, hsp]

/-- An auxiliary predicate on an index of a natural-number sequence of length one more than its parameter. -/
def Auxiliary.index_condition {n : ℕ} (a : Fin (n + 1) → ℕ) (i : Fin (n + 1)) : Prop :=
  1 ≤ a i ∧ ∀ j : Fin (n + 1), i < j → a j ≤ a i - 1

/-- Constructs an auxiliary object from an antitone sequence indexed by `Fin (n + 1)` whose entries sum to `n + 1`, and a distinguished index satisfying the auxiliary condition. -/
def Auxiliary.construct_from_index_condition {n : ℕ} (a : Fin (n + 1) → ℕ) (hant : Antitone a) (hsum : ∑ j, a j = n + 1)
    (i : Fin (n + 1)) (hleg : Auxiliary.index_condition a i) : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (n + 1) n where
  parts j := if j = i then a j - 1 else a j
  parts_antitone := by
    intro p r hpr
    change (if r = i then a r - 1 else a r) ≤ (if p = i then a p - 1 else a p)
    by_cases hp : p = i <;> by_cases hr : r = i
    · rw [if_pos hp, if_pos hr]
      have : a p = a r := by rw [hp, hr]
      omega
    · rw [if_pos hp, if_neg hr]
      have hlt : i < r := lt_of_le_of_ne (hp ▸ hpr) (Ne.symm hr)
      have := hleg.2 r hlt; rw [hp]; exact this
    · rw [if_neg hp, if_pos hr]
      have : a r ≤ a p := hant hpr
      omega
    · rw [if_neg hp, if_neg hr]; exact hant hpr
  sum_parts := by
    have hsplit : ∀ j, (if j = i then a j - 1 else a j) + (if j = i then 1 else 0) = a j := by
      intro j; by_cases hj : j = i
      · rw [if_pos hj, if_pos hj]; have : 1 ≤ a j := hj ▸ hleg.1; omega
      · rw [if_neg hj, if_neg hj, add_zero]
    have h2 : ∑ j, ((if j = i then a j - 1 else a j) + (if j = i then 1 else 0)) = n + 1 := by
      rw [Finset.sum_congr rfl (fun j _ => hsplit j)]; exact hsum
    rw [Finset.sum_add_distrib] at h2
    have h3 : ∑ j : Fin (n + 1), (if j = i then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ i (fun _ => 1)]; simp
    omega

/-- The parts of the auxiliary object are obtained by truncated subtraction of one at the distinguished index and are unchanged elsewhere. -/
@[simp] lemma Auxiliary.construct_from_index_condition_parts {n : ℕ} (a : Fin (n + 1) → ℕ) (hant : Antitone a)
    (hsum : ∑ j, a j = n + 1) (i : Fin (n + 1)) (hleg : Auxiliary.index_condition a i) (j : Fin (n + 1)) :
    (Auxiliary.construct_from_index_condition a hant hsum i hleg).parts j = if j = i then a j - 1 else a j := rfl

/-- The auxiliary sequence transform at an index is the original entry plus the truncated difference of the parameter and the index value. -/
lemma Auxiliary.sequence_transform_apply {n : ℕ} (f : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (n + 1) f j = f j + (n - j.val) := by
  simp [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]

/-- The displayed coefficient of the nested product determinant * ((sum of all variables) * partial power-sum expression) equals the sum of auxiliary values over the predecessor partition finset. -/
lemma Auxiliary.coeff_eq_sum_partition_finset_pred (n : ℕ) (bpμ : RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (n + 1) (n + 1)) (ν : Nat.Partition n) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (n + 1) bpμ.parts))
        ((RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix (n + 1) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (n + 1))).det *
          ((∑ i, MvPolynomial.X i) * MvPolynomial.psumPart (Fin (n + 1)) ℚ ν))
      = ∑ la ∈ Auxiliary.partition_finset_pred (bpμ.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple (n + 1) bpμ.parts),
          RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (n + 1) (Auxiliary.construct_from_partition la) ν := by
  classical
  set μ := (bpμ.sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple (n + 1) bpμ.parts : Nat.Partition (n + 1)) with hμ
  set g := (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix (n + 1) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (n + 1))).det *
    MvPolynomial.psumPart (Fin (n + 1)) ℚ ν with hg
  set D := Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (n + 1) bpμ.parts) with hD

  set bpd : (i : Fin (n + 1)) → Auxiliary.index_condition bpμ.parts i → RepresentationTheory.SymmetricPolynomials.Alternant.FinPartition (n + 1) n :=
    fun i hleg => Auxiliary.construct_from_index_condition bpμ.parts bpμ.parts_antitone bpμ.sum_parts i hleg with hbpd
  set partOf : (i : Fin (n + 1)) → Auxiliary.index_condition bpμ.parts i → Nat.Partition n :=
    fun i hleg => (bpd i hleg).sum_parts ▸ RepresentationTheory.GeneralLinearGroup.WeightCharacter.partitionOfTuple (n + 1) (bpd i hleg).parts with hpartOf
  have hbpd_parts : ∀ (i : Fin (n + 1)) (hleg : Auxiliary.index_condition bpμ.parts i) (j : Fin (n + 1)),
      (bpd i hleg).parts j = if j = i then bpμ.parts j - 1 else bpμ.parts j := by
    intro i hleg j; simp only [hbpd, Auxiliary.construct_from_index_condition_parts]

  have hanti : ∀ τ : Equiv.Perm (Fin (n + 1)),
      MvPolynomial.rename τ g = Equiv.Perm.sign τ • g := by
    intro τ
    rw [hg, map_mul, RepresentationTheory.SymmetricPolynomials.Alternant.rename_det_alternantMatrix, (RepresentationTheory.SymmetricPolynomials.Alternant.psumPart_isSymmetric (n + 1) ν) τ, smul_mul_assoc]

  have hμrow : ∀ i : Fin (n + 1), (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).rowLen i.val = bpμ.parts i := by
    intro i; rw [hμ]; exact (Auxiliary.parts_eq_converted_partition_row_len bpμ i).symm
  have hμrow0 : ∀ k : ℕ, n + 1 ≤ k → (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).rowLen k = 0 := fun k hk =>
    partition_row_len_eq_zero_of_size_le μ (by omega)

  have hDval : ∀ i : Fin (n + 1), D i = bpμ.parts i + (n - i.val) := by
    intro i; rw [hD, Finsupp.coe_equivFunOnFinite_symm, Auxiliary.sequence_transform_apply]

  have hexp : ∀ (i : Fin (n + 1)) (hleg : Auxiliary.index_condition bpμ.parts i),
      D - Finsupp.single i 1
        = Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (n + 1) (bpd i hleg).parts) := by
    intro i hleg
    apply Finsupp.ext
    intro j
    have hL : (D - Finsupp.single i (1 : ℕ)) j
        = bpμ.parts j + (n - j.val) - (if i = j then 1 else 0) := by
      rw [Finsupp.tsub_apply, hDval, Finsupp.single_apply]
    have hR : (Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (n + 1) (bpd i hleg).parts)) j
        = (if j = i then bpμ.parts j - 1 else bpμ.parts j) + (n - j.val) := by
      rw [Finsupp.coe_equivFunOnFinite_symm, Auxiliary.sequence_transform_apply, hbpd_parts]
    rw [hL, hR]
    by_cases hj : j = i
    · rw [if_pos hj.symm, if_pos hj]
      have hpj : 1 ≤ bpμ.parts j := by rw [hj]; exact hleg.1
      omega
    · rw [if_neg (fun h => hj h.symm), if_neg hj]; omega

  have hval_coeff : ∀ (i : Fin (n + 1)) (hleg : Auxiliary.index_condition bpμ.parts i),
      MvPolynomial.coeff (D - Finsupp.single i (1 : ℕ)) g
        = RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (n + 1) (Auxiliary.construct_from_partition (partOf i hleg)) ν := by
    intro i hleg
    have hpe : (bpd i hleg).parts = (Auxiliary.construct_from_partition (partOf i hleg)).parts := by
      funext k
      change (bpd i hleg).parts k = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (partOf i hleg)).rowLen k.val
      simp only [hpartOf]; exact Auxiliary.parts_eq_converted_partition_row_len (bpd i hleg) k
    rw [hexp i hleg, hpe]; rfl

  have hsupp_of_legal : ∀ (i : Fin (n + 1)), Auxiliary.index_condition bpμ.parts i → i ∈ D.support := by
    intro i hleg
    rw [Finsupp.mem_support_iff, hDval]; have := hleg.1; omega
  set legalFinset := Finset.univ.filter (fun i : Fin (n + 1) => Auxiliary.index_condition bpμ.parts i) with hLF

  have hzero : ∀ i ∈ Finset.univ, i ∉ legalFinset →
      (if i ∈ D.support then MvPolynomial.coeff (D - Finsupp.single i (1 : ℕ)) g else 0) = 0 := by
    intro i _ hi
    have hnleg : ¬ Auxiliary.index_condition bpμ.parts i := by simpa [hLF] using hi
    by_cases hmem : i ∈ D.support
    · rw [if_pos hmem]
      have hsi : bpμ.parts i + (n - i.val) ≠ 0 := by
        have := hmem; rw [Finsupp.mem_support_iff, hDval] at this; exact this

      have hival : i.val < n := by
        by_contra hge
        have hie : i.val = n := by omega
        exact hnleg ⟨by rw [hie] at hsi; omega, fun j hj => by
          exact absurd hj (by rw [Fin.lt_def]; omega)⟩
      set j0 : Fin (n + 1) := ⟨i.val + 1, by omega⟩ with hj0
      have hj0v : j0.val = i.val + 1 := by rw [hj0]
      have hij0lt : i < j0 := by rw [Fin.lt_def]; omega
      have haj0le : bpμ.parts j0 ≤ bpμ.parts i := bpμ.parts_antitone (le_of_lt hij0lt)
      have haieq : bpμ.parts i = bpμ.parts j0 := by
        rcases eq_or_lt_of_le haj0le with h | h
        · exact h.symm
        · exfalso; apply hnleg
          refine ⟨by omega, fun j hj => ?_⟩
          have hjj0 : j0 ≤ j := by
            rw [Fin.le_iff_val_le_val]; rw [Fin.lt_def] at hj; omega
          have := bpμ.parts_antitone hjj0; omega
      have hij0 : i ≠ j0 := by rw [Ne, Fin.ext_iff]; omega
      have hdeq : (D - Finsupp.single i (1 : ℕ)) i = (D - Finsupp.single i (1 : ℕ)) j0 := by
        rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hDval, hDval, Finsupp.single_apply,
          Finsupp.single_apply, if_pos rfl, if_neg hij0, haieq]
        omega
      exact RepresentationTheory.SymmetricPolynomials.Alternant.coeff_eq_zero_of_alternating_of_eq (i := i) (j := j0) g hanti (D - Finsupp.single i (1 : ℕ))
        hij0 hdeq
    · rw [if_neg hmem]

  rw [show (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix (n + 1) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (n + 1))).det *
        ((∑ i, MvPolynomial.X i) * MvPolynomial.psumPart (Fin (n + 1)) ℚ ν)
        = (∑ i, MvPolynomial.X i) * g from by rw [hg]; ring,
    Finset.sum_mul, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_X_mul']
  rw [← Finset.sum_subset (Finset.subset_univ legalFinset) hzero]
  refine Finset.sum_bij (fun i hi => partOf i (Finset.mem_filter.mp hi).2) ?_ ?_ ?_ ?_
  ·
    intro i hi
    have hleg := (Finset.mem_filter.mp hi).2
    rw [Auxiliary.partition_finset_pred, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [YoungDiagram.le_iff_row_len_le]
    intro k
    rcases lt_or_ge k (n + 1) with hk | hk
    · rw [show (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (partOf i hleg)).rowLen k = (bpd i hleg).parts ⟨k, hk⟩ from by
          simp only [hpartOf]; exact (Auxiliary.parts_eq_converted_partition_row_len (bpd i hleg) ⟨k, hk⟩).symm,
        hμrow ⟨k, hk⟩, hbpd_parts i hleg ⟨k, hk⟩]
      split <;> omega
    · rw [partition_row_len_eq_zero_of_size_le (partOf i hleg) (by omega), hμrow0 k hk]
  ·
    intro i hi i' hi' heq
    have hleg := (Finset.mem_filter.mp hi).2
    have hleg' := (Finset.mem_filter.mp hi').2
    by_contra hne
    have h1 : (bpd i hleg).parts i = (bpd i' hleg').parts i := by
      rw [Auxiliary.parts_eq_converted_partition_row_len (bpd i hleg) i, Auxiliary.parts_eq_converted_partition_row_len (bpd i' hleg') i]
      change (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (partOf i hleg)).rowLen i.val
          = (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (partOf i' hleg')).rowLen i.val
      rw [heq]
    rw [hbpd_parts i hleg i, hbpd_parts i' hleg' i, if_pos rfl, if_neg hne] at h1
    have := hleg.1; omega
  ·
    intro la hla
    rw [Auxiliary.partition_finset_pred, Finset.mem_filter] at hla
    have hle := hla.2
    rw [YoungDiagram.le_iff_row_len_le] at hle
    have htermle : ∀ k : Fin (n + 1), (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val ≤ bpμ.parts k := by
      intro k; have := hle k.val; rwa [hμrow k] at this
    have hsumterm : ∑ k : Fin (n + 1), (bpμ.parts k - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val) = 1 := by
      have h1 : ∑ k : Fin (n + 1), (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val = n := partition_sum_row_len n la
      have h3 : ∑ k : Fin (n + 1),
          ((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val + (bpμ.parts k - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val))
          = ∑ k, bpμ.parts k :=
        Finset.sum_congr rfl fun k _ => by have := htermle k; omega
      rw [Finset.sum_add_distrib, h1, bpμ.sum_parts] at h3
      omega
    obtain ⟨i, hi1⟩ : ∃ i : Fin (n + 1), bpμ.parts i - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i.val = 1 := by
      by_contra hcon; push Not at hcon
      have hz : ∀ k, bpμ.parts k - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val = 0 := by
        intro k; by_contra hk0
        have hge : 2 ≤ bpμ.parts k - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val := by have := hcon k; omega
        have hle2 := Finset.single_le_sum
          (f := fun k => bpμ.parts k - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val)
          (fun k _ => Nat.zero_le _) (Finset.mem_univ k)
        rw [hsumterm] at hle2; omega
      rw [Finset.sum_eq_zero (fun k _ => hz k)] at hsumterm; omega
    have hother : ∀ j : Fin (n + 1), j ≠ i →
        bpμ.parts j - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen j.val = 0 := by
      intro j hj; by_contra hj0
      have hpair : (bpμ.parts i - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i.val)
          + (bpμ.parts j - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen j.val)
          ≤ ∑ k, (bpμ.parts k - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val) := by
        rw [← Finset.sum_pair (f := fun k => bpμ.parts k - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k.val)
          (Ne.symm hj)]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [hsumterm] at hpair; omega
    have hleg : Auxiliary.index_condition bpμ.parts i := by
      refine ⟨by omega, fun j hj => ?_⟩
      have hji : j ≠ i := Ne.symm (ne_of_lt hj)
      have h1 : bpμ.parts j - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen j.val = 0 := hother j hji
      have h1' : (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen j.val ≤ bpμ.parts j := htermle j
      have h2 : (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen j.val ≤ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen i.val :=
        (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen_anti i.val j.val (le_of_lt (by rwa [Fin.lt_def] at hj))
      omega
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hleg⟩, ?_⟩

    apply partition_eq_of_row_len_eq
    intro k
    rcases lt_or_ge k (n + 1) with hk | hk
    · rw [show (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (partOf i hleg)).rowLen k = (bpd i hleg).parts ⟨k, hk⟩ from by
          simp only [hpartOf]; exact (Auxiliary.parts_eq_converted_partition_row_len (bpd i hleg) ⟨k, hk⟩).symm,
        hbpd_parts i hleg ⟨k, hk⟩]
      by_cases hki : (⟨k, hk⟩ : Fin (n + 1)) = i
      · have hkv : k = i.val := congrArg Fin.val hki
        rw [if_pos hki, show (⟨k, hk⟩ : Fin (n + 1)) = i from hki, show k = i.val from hkv]
        omega
      · rw [if_neg hki]
        have h : bpμ.parts ⟨k, hk⟩ - (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k = 0 := hother ⟨k, hk⟩ hki
        have h' : (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).rowLen k ≤ bpμ.parts ⟨k, hk⟩ := htermle ⟨k, hk⟩
        omega
    · rw [partition_row_len_eq_zero_of_size_le (partOf i hleg) (by omega),
        partition_row_len_eq_zero_of_size_le la (by omega)]
  ·
    intro i hi
    have hleg := (Finset.mem_filter.mp hi).2
    rw [if_pos (hsupp_of_legal i hleg)]
    exact hval_coeff i hleg

/-- The auxiliary value of a successor-size partition on the image of a permutation is the sum of the corresponding values over its predecessor partition finset. -/
theorem Auxiliary.value_permutation_hom_succ_eq_sum_partition_finset_pred (n : ℕ) (μ : Nat.Partition (n + 1))
    (σ : Equiv.Perm (Fin n)) :
    RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) μ (Auxiliary.permutation_hom_succ n σ) =
      ∑ la ∈ Auxiliary.partition_finset_pred μ, RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la σ := by
  classical
  obtain ⟨bpμ, hbpμ⟩ := RepresentationTheory.YoungDiagram.PartitionFormulas.auxiliary_exists_preimage_for_partition (n + 1) μ

  have hLHS : RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) μ (Auxiliary.permutation_hom_succ n σ) =
      ((RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (n + 1) bpμ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType (Auxiliary.permutation_hom_succ n σ)) : ℚ) : ℂ) := by
    have key := RepresentationTheory.GeneralLinearGroup.WeightCharacter.Auxiliary.cast_characterValue_eq (n + 1) (n + 1) bpμ (Auxiliary.permutation_hom_succ n σ)
    rw [hbpμ] at key; exact key.symm

  have hRHS : ∀ la ∈ Auxiliary.partition_finset_pred μ, RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n la σ =
      ((RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (n + 1) (Auxiliary.construct_from_partition la) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType σ) : ℚ) : ℂ) := by
    intro la _
    have key := RepresentationTheory.GeneralLinearGroup.WeightCharacter.Auxiliary.cast_characterValue_eq (n + 1) n (Auxiliary.construct_from_partition la) σ
    rw [Auxiliary.convert_construct_from_partition] at key; exact key.symm

  have hQ : RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (n + 1) bpμ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType (Auxiliary.permutation_hom_succ n σ))
      = ∑ la ∈ Auxiliary.partition_finset_pred μ, RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (n + 1) (Auxiliary.construct_from_partition la) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType σ) := by
    have hdef : RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff (n + 1) bpμ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType (Auxiliary.permutation_hom_succ n σ))
        = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase (n + 1) bpμ.parts))
            ((RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix (n + 1) (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents (n + 1))).det
              * MvPolynomial.psumPart (Fin (n + 1)) ℚ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType (Auxiliary.permutation_hom_succ n σ))) := rfl
    rw [hdef, Auxiliary.psum_part_permutation_hom_succ n σ, ← hbpμ]
    exact Auxiliary.coeff_eq_sum_partition_finset_pred n bpμ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.cycleType σ)
  rw [hLHS, Finset.sum_congr rfl hRHS]
  exact_mod_cast hQ

/-- The auxiliary operation on the two specified permutation functions is one when the first partition diagram is at most the second and zero otherwise. -/
theorem Auxiliary.complex_function_operation_eq_indicator_le (n : ℕ) (μ : Nat.Partition n)
    (la : Nat.Partition (n + 1)) :
    Auxiliary.complex_function_operation n (RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n μ)
        (fun σ => RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) la (Auxiliary.permutation_hom_succ n σ)) =
      if (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ) ≤ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la) then 1 else 0 := by
  classical
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) = (Nat.factorial n : ℂ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hne : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

  have hexpand :
      ∑ σ : Equiv.Perm (Fin n),
        RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n μ σ *
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) la (Auxiliary.permutation_hom_succ n σ⁻¹)
        = (Nat.factorial n : ℂ) *
            ∑ ρ ∈ Auxiliary.partition_finset_pred la, (if μ = ρ then (1 : ℂ) else 0) := by

    have e1 : ∑ σ : Equiv.Perm (Fin n),
        RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n μ σ *
          RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue (n + 1) la (Auxiliary.permutation_hom_succ n σ⁻¹)
        = ∑ σ : Equiv.Perm (Fin n),
            ∑ ρ ∈ Auxiliary.partition_finset_pred la,
              RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n μ σ * RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue n ρ σ⁻¹ := by
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [Auxiliary.value_permutation_hom_succ_eq_sum_partition_finset_pred n la σ⁻¹, Finset.mul_sum]
    rw [e1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.sum_auxiliaryPartitionPermutationValue_mul_inv n μ ρ]
  unfold Auxiliary.complex_function_operation
  dsimp only
  rw [hexpand, hcard, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  simp only [Finset.sum_ite_eq, Auxiliary.partition_finset_pred, Finset.mem_filter, Finset.mem_univ, true_and]

end RepresentationTheory.Auxiliary.PartitionPermutationRelations

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.statement017516 := _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.parts_eq_converted_partition_row_len

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.statement022649 := _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.coeff_eq_sum_partition_finset_pred

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.statement024504 := _root_.RepresentationTheory.Auxiliary.PartitionPermutationRelations.Auxiliary.convert_construct_from_partition

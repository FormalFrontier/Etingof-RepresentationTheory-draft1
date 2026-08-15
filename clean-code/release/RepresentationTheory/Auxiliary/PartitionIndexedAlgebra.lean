/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.YoungDiagram.PartitionConstructions
import RepresentationTheory.Combinatorics.PartitionPermutation
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Auxiliary.PartitionIndexedAlgebra

open scoped Classical

/-- Provides a coercion from a monoid algebra over a semiring to functions from its indexing type to the semiring. -/
local instance monoidAlgebraCoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

/-- Returns an auxiliary element indexed by a natural number. -/
@[source_ref "Chapter5/Problem5.16.2" (role := supporting)]
noncomputable def auxiliaryElement (n : ℕ) : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2)

/-- Associates an auxiliary integer to each partition. -/
@[source_ref "Chapter5/Problem5.16.2" (role := supporting)]
noncomputable def partitionAuxiliaryInt {n : ℕ} (la : Nat.Partition n) : ℤ :=
  ∑ c ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition la).cells, ((c.2 : ℤ) - (c.1 : ℤ))

private lemma sumTranspositions_reindex (n : ℕ) (h : Equiv.Perm (Fin n)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap (h p.1) (h p.2)) : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n)
      = auxiliaryElement n := by
  rw [auxiliaryElement]
  refine Finset.sum_nbij'
    (i := fun p => if h p.1 < h p.2 then (h p.1, h p.2) else (h p.2, h p.1))
    (j := fun p => if h⁻¹ p.1 < h⁻¹ p.2 then (h⁻¹ p.1, h⁻¹ p.2) else (h⁻¹ p.2, h⁻¹ p.1))
    ?_ ?_ ?_ ?_ ?_
  ·
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hne : h p.1 ≠ h p.2 := fun e => (ne_of_lt hp) (h.injective e)
    split_ifs with hc
    · exact hc
    · exact lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
  ·
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hne : h⁻¹ p.1 ≠ h⁻¹ p.2 := fun e => (ne_of_lt hp) (h⁻¹.injective e)
    split_ifs with hc
    · exact hc
    · exact lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
  ·
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hc : h p.1 < h p.2
    · simp only [if_pos hc, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, if_pos hp, Prod.mk.eta]
    · simp only [if_neg hc, Equiv.Perm.coe_inv, Equiv.symm_apply_apply,
        if_neg (not_lt.mpr hp.le), Prod.mk.eta]
  ·
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hc : h⁻¹ p.1 < h⁻¹ p.2
    · simp only [if_pos hc]
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, if_pos hp, Prod.mk.eta]
    · simp only [if_neg hc]
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, if_neg (not_lt.mpr hp.le), Prod.mk.eta]
  ·
    intro p hp
    by_cases hc : h p.1 < h p.2
    · simp only [if_pos hc]
    · simp only [if_neg hc]
      rw [Equiv.swap_comm]

/-- The auxiliary element commutes with every element of the indexed family. -/
@[source_ref "Chapter5/Problem5.16.2" (role := supporting)]
lemma auxiliaryElement_commutes (n : ℕ) (y : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) :
    auxiliaryElement n * y = y * auxiliaryElement n := by

  induction y using MonoidAlgebra.induction_on with
  | hM g =>

    have e1 : auxiliaryElement n * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
        = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
            MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (g * Equiv.swap (g⁻¹ p.1) (g⁻¹ p.2)) := by
      rw [auxiliaryElement, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [← map_mul, Equiv.swap_mul_eq_mul_swap]

    have e2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (g * Equiv.swap (g⁻¹ p.1) (g⁻¹ p.2))
        = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
            * ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
                MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap (g⁻¹ p.1) (g⁻¹ p.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [map_mul]
    rw [e1, e2, sumTranspositions_reindex n g⁻¹]
  | hadd f₁ f₂ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
  | hsmul r f h => rw [mul_smul_comm, smul_mul_assoc, h]

/-- For distinct finite indices, the coefficient of an auxiliary partition-indexed element at their swap equals the first equality indicator minus the second, where the indicators compare the values of two auxiliary maps on the corresponding sorted parts. -/
lemma coeff_auxiliaryPartitionElement_swap_eq_indicator_sub (n : ℕ) (la : Nat.Partition n) {i j : Fin n} (hij : i ≠ j) :
    (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) (Equiv.swap i j)
      = (if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val then (1 : ℂ) else 0)
        - (if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val then (1 : ℂ)
            else 0) := by
  classical
  have hsum : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := _root_.RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la
  have hbounds : ∀ k : Fin n, k.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := fun k => by rw [hsum]; exact k.isLt
  by_cases hrow : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val
  ·
    have hswapP : Equiv.swap i j ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.swap_mem_of_row_eq hrow
    have hcoeff : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) (Equiv.swap i j) = 1 := by
      have h := _root_.RepresentationTheory.Combinatorics.PartitionPermutation.coeff_mul_eq_sign_of_mem n la 1 (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).one_mem
        (Equiv.swap i j) hswapP
      simpa [Equiv.Perm.sign_one] using h
    have hcolne : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val ≠ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val := by
      intro hc
      exact hij (Fin.ext (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val j.val
        (hbounds i) (hbounds j) hrow hc))
    rw [hcoeff, if_pos hrow, if_neg hcolne]; ring
  · by_cases hcol : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val
    ·
      have hswapQ : Equiv.swap i j ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.swap_mem_of_column_eq hcol
      have hcoeff : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) (Equiv.swap i j)
          = ((Equiv.Perm.sign (Equiv.swap i j) : ℤ) : ℂ) := by
        have h := _root_.RepresentationTheory.Combinatorics.PartitionPermutation.coeff_mul_eq_sign_of_mem n la (Equiv.swap i j) hswapQ 1
          (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n la).one_mem
        simpa using h
      rw [hcoeff, Equiv.Perm.sign_swap hij, if_neg hrow, if_pos hcol]; norm_num
    ·
      have hzero : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) (Equiv.swap i j) = 0 := by
        by_contra hne
        obtain ⟨q, hq, p, hp, hqp⟩ := _root_.RepresentationTheory.Combinatorics.PartitionPermutation.exists_mem_mul_mem_eq_of_coeff_ne_zero n la (Equiv.swap i j) hne

        have hpfix : ∀ k : Fin n, k ≠ i → k ≠ j → p k = k := by
          intro k hki hkj
          have hsk : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
          have hqpk : q (p k) = k := by
            have hcompose : (q * p) k = k := by rw [← hqp]; exact hsk
            rwa [Equiv.Perm.mul_apply] at hcompose
          have hpk_eq : p k = q⁻¹ k := by
            have h2 := congrArg (fun x => q⁻¹ x) hqpk
            simpa using h2
          have hrowpk : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (p k).val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val := hp k
          have hcolpk : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (p k).val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val := by
            rw [hpk_eq]; exact (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n la).inv_mem hq k
          exact Fin.ext (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (p k).val k.val
            (hbounds _) (hbounds k) hrowpk hcolpk)

        have hpi : p i = i ∨ p i = j := by
          by_contra hcon
          push Not at hcon
          obtain ⟨hpi_i, hpi_j⟩ := hcon
          exact hpi_i (p.injective (hpfix (p i) hpi_i hpi_j))
        rcases hpi with h | h
        ·
          have hqi : q i = j := by
            have h1 : (q * p) i = j := by rw [← hqp, Equiv.swap_apply_left]
            rwa [Equiv.Perm.mul_apply, h] at h1
          have hcc : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (q i).val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val := hq i
          rw [hqi] at hcc
          exact hcol hcc.symm
        ·
          have hrr : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) (p i).val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val := hp i
          rw [h] at hrr
          exact hrow hrr.symm
      rw [hzero, if_neg hrow, if_neg hcol]; ring

private lemma pos_decomp_list (parts : List ℕ) (m : ℕ) (hm : m < parts.sum) :
    m = (parts.take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts m)).sum + _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts m := by
  have hrlen : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts m < parts.length := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_length parts m hm
  have hclt : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts m < parts[_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts m] := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.columnIndex_lt_rowLength parts m hm
  obtain ⟨hcr, hcc⟩ := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowColumnIndex_sum_take_add parts (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts m) (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts m)
    hrlen hclt
  have hlt := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.List.sum_take_add_lt_sum parts (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts m) (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts m) hrlen hclt
  exact (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq parts
    ((parts.take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts m)).sum + _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn parts m) m hlt hm hcr hcc).symm

private lemma card_val_Ico (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => a ≤ i.val ∧ i.val < b)).card = b - a := by
  have hsub : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < a)
      ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < b) := by
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hdiff : (Finset.univ : Finset (Fin n)).filter (fun i => a ≤ i.val ∧ i.val < b)
      = (Finset.univ.filter (fun i => i.val < b)) \ (Finset.univ.filter (fun i => i.val < a)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]; omega
  rw [hdiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Fin.card_filter_val_lt n b hb,
    _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Fin.card_filter_val_lt n a (le_trans hab hb)]

private lemma card_before_sameRow (n : ℕ) (la : Nat.Partition n) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i =>
      i < j ∧ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val)).card
      = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val := by
  have hsum : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := _root_.RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la
  set r := _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val with hr
  have hjdecomp : j.val = ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take r).sum + _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val := by
    have h := pos_decomp_list (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val (by rw [hsum]; exact j.isLt)
    rw [← hr] at h; exact h
  have hset : (Finset.univ : Finset (Fin n)).filter (fun i =>
        i < j ∧ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = r)
      = (Finset.univ : Finset (Fin n)).filter (fun i =>
          ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take r).sum ≤ i.val ∧ i.val < j.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    have hib : i.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by rw [hsum]; exact i.isLt
    have hjb : j.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by rw [hsum]; exact j.isLt
    constructor
    · rintro ⟨hij, hri⟩
      refine ⟨?_, hij⟩
      by_contra hlt
      push Not at hlt
      have : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val < r :=
        (_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val r hib).mpr hlt
      omega
    · rintro ⟨hge, hij⟩
      refine ⟨hij, ?_⟩
      have hnlt : ¬ (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val < r) := by
        rw [_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val r hib]; omega
      have hjr1 : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val < r + 1 := by rw [← hr]; omega
      have hjr1' : j.val < ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take (r+1)).sum :=
        (_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val (r+1) hjb).mp hjr1
      have hir1 : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val < r + 1 :=
        (_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val (r+1) hib).mpr (by omega)
      omega
  rw [hset, card_val_Ico n (((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take r).sum) j.val (by omega) (le_of_lt j.isLt)]
  omega

private lemma card_before_sameCol (n : ℕ) (la : Nat.Partition n) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i =>
      i < j ∧ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val)).card
      = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val := by
  have hsum : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := _root_.RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la
  have hsorted : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).Pairwise (· ≥ ·) := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.sortedParts_pairwise_ge la
  have hjb : j.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by rw [hsum]; exact j.isLt
  have hrlen : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length :=
    _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_length (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val hjb
  have hclt : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)[_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val] :=
    _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.columnIndex_lt_rowLength (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val hjb
  have hjdecomp := pos_decomp_list (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val hjb
  set r := _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val with hr
  set c := _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val with hc
  have hmono : ∀ a b : ℕ, a ≤ b → ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take a).sum ≤ ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).sum := by
    intro a b hab
    have he : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take a = ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).take a := by
      rw [List.take_take, min_eq_left hab]
    rw [he]
    exact List.Sublist.sum_le_sum (List.take_sublist a ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b))
      (fun _ _ => Nat.zero_le _)
  rw [← Finset.card_range r]
  refine Finset.card_bij (fun i _ => _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val) ?_ ?_ ?_
  ·
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, hij, hcoli⟩ := hi
    rw [Fin.lt_def] at hij
    have hib : i.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by rw [hsum]; exact i.isLt
    have hidecomp : i.val = ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val)).sum + c := by
      have h := pos_decomp_list (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val hib
      rw [hcoli] at h; exact h
    rw [Finset.mem_range]
    by_contra hle
    push Not at hle
    have : ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take r).sum ≤ ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val)).sum :=
      hmono r _ hle
    omega
  ·
    intro i₁ hi₁ i₂ hi₂ heq
    rw [Finset.mem_filter] at hi₁ hi₂
    obtain ⟨-, -, hcoli₁⟩ := hi₁
    obtain ⟨-, -, hcoli₂⟩ := hi₂
    have hb₁ : i₁.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by rw [hsum]; exact i₁.isLt
    have hb₂ : i₂.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := by rw [hsum]; exact i₂.isLt
    exact Fin.ext (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i₁.val i₂.val hb₁ hb₂ heq
      (by rw [hcoli₁, hcoli₂]))
  ·
    intro b hb
    rw [Finset.mem_range] at hb
    have hblen : b < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).length := lt_trans hb hrlen
    have hcb : c < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)[b] :=
      _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.List.lt_getElem_of_le_index (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) hsorted r b c hrlen hblen (le_of_lt hb) hclt
    obtain ⟨hcr', hcc'⟩ := _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowColumnIndex_sum_take_add (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) b c hblen hcb
    have hmlt : ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).sum + c < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum :=
      _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.List.sum_take_add_lt_sum (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) b c hblen hcb
    have hmn : ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).sum + c < n := lt_of_lt_of_eq hmlt hsum

    have hstep : ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take (b+1)).sum = ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).sum
        + (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)[b] := List.sum_take_succ (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) b hblen
    have hpos : 0 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la)[b] := lt_of_le_of_lt (Nat.zero_le c) hcb
    have hstrict : ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).sum < ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take r).sum := by
      have h1 : ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take (b+1)).sum ≤ ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take r).sum := hmono _ _ hb
      omega
    refine ⟨⟨((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).sum + c, hmn⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hcc'⟩
      rw [Fin.lt_def]
      exact (by omega : ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).take b).sum + c < j.val)
    · exact hcr'

private lemma content_eq_sum (n : ℕ) (la : Nat.Partition n) :
    (partitionAuxiliaryInt la : ℤ)
      = ∑ k : Fin n, ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val : ℤ) - _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val) := by
  have hsum : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum = n := _root_.RepresentationTheory.Partition.YoungDiagram.sum_sortedParts n la
  have hbounds : ∀ k : Fin n, k.val < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).sum := fun k => by rw [hsum]; exact k.isLt
  rw [partitionAuxiliaryInt]
  refine (Finset.sum_bij (fun (k : Fin n) _ =>
    ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val, _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val) : ℕ × ℕ)) ?_ ?_ ?_ ?_).symm
  ·
    intro k _
    simp only [YoungDiagram.mem_cells, _root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition, YoungDiagram.mem_ofRowLens]
    exact ⟨_root_.RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_length (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val (hbounds k),
      _root_.RepresentationTheory.SymmetricGroup.PartitionDominance.columnIndex_lt_rowLength (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val (hbounds k)⟩
  ·
    intro k₁ _ k₂ _ heq
    rw [Prod.mk.injEq] at heq
    exact Fin.ext (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.eq_of_flatIndexRow_eq_and_column_eq (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k₁.val k₂.val
      (hbounds k₁) (hbounds k₂) heq.1 heq.2)
  ·
    intro cell hcell
    simp only [YoungDiagram.mem_cells, _root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition,
      YoungDiagram.mem_ofRowLens] at hcell
    obtain ⟨hr, hc⟩ := hcell
    have hcgetD : cell.2 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la).getD cell.1 0 := by
      rw [List.getD_eq_getElem (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) 0 hr]; exact hc
    obtain ⟨m, hmlt, hmr, hmc⟩ := _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.exists_flatIndex_of_column_lt_rowLength (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) cell.1 cell.2 hcgetD
    refine ⟨⟨m, lt_of_lt_of_eq hmlt hsum⟩, Finset.mem_univ _, ?_⟩
    simp only [hmr, hmc]
  ·
    intro k _
    rfl

private lemma inner_transposition_sum (n : ℕ) (la : Nat.Partition n) (j : Fin n) :
    ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i < j),
      ((if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val then (1 : ℂ) else 0)
        - (if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val then (1 : ℂ) else 0))
      = (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val : ℂ) - (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val : ℂ) := by
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, Finset.filter_filter,
    Finset.filter_filter, card_before_sameRow n la j, card_before_sameCol n la j]

private lemma youngSymmetrizer_transposition_sum_eq_content (n : ℕ) (la : Nat.Partition n) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) (Equiv.swap p.1 p.2) = (partitionAuxiliaryInt la : ℂ) := by
  classical
  have key : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) (Equiv.swap p.1 p.2) =
        (if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p.1.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p.2.val then (1 : ℂ) else 0)
        - (if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p.1.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) p.2.val then (1 : ℂ)
            else 0) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact coeff_auxiliaryPartitionElement_swap_eq_indicator_sub n la (ne_of_lt hp.2)
  rw [Finset.sum_congr rfl key, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hstep : ∀ j : Fin n,
      (∑ i : Fin n, if i < j then
          ((if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val then (1 : ℂ) else 0)
           - (if _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) i.val = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val then (1 : ℂ)
              else 0))
        else 0)
      = (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val : ℂ) - (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val : ℂ) := by
    intro j
    rw [← Finset.sum_filter]
    exact inner_transposition_sum n la j
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_sub_distrib]
  have hcast : (partitionAuxiliaryInt la : ℂ) = (∑ j : Fin n, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val : ℂ))
      - (∑ j : Fin n, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) j.val : ℂ)) := by
    have h2 : ((partitionAuxiliaryInt la : ℤ) : ℂ)
        = ((∑ k : Fin n, ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val : ℤ) - _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList la) k.val)) : ℂ)
        := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (content_eq_sum n la)
    rw [h2]; push_cast; rw [Finset.sum_sub_distrib]
  rw [hcast]

set_option backward.isDefEq.respectTransparency false in

private lemma sumTranspositions_youngSymmetrizer_coeff_one (n : ℕ) (la : Nat.Partition n) :
    (auxiliaryElement n * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) 1 = (partitionAuxiliaryInt la : ℂ) := by
  rw [← youngSymmetrizer_transposition_sum_eq_content n la, auxiliaryElement, Finset.sum_mul,
    MonoidAlgebra.coeff_sum]
  change (Finsupp.applyAddHom 1)
    (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2) :
        _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la).coeff) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  change (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2) *
    _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la).coeff 1 = _
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply]
  simp [Equiv.swap_inv]

set_option backward.isDefEq.respectTransparency false in

/-- On the auxiliary element indexed by the partition, left multiplication by the natural-number-indexed auxiliary element equals scalar multiplication by the cast of the partition’s auxiliary integer. -/
@[source_ref "Chapter5/Problem5.16.2" (role := supporting)]
lemma auxiliaryElement_mul_eq_smul_at_partition (n : ℕ) (la : Nat.Partition n) :
    auxiliaryElement n * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = (partitionAuxiliaryInt la : ℂ) • _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
  set A := _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n with hA
  set V := _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la with hV

  let LC : A →ₗ[A] A :=
    { toFun := fun x => auxiliaryElement n * x
      map_add' := fun x y => mul_add _ _ _
      map_smul' := fun a x => by
        simp only [smul_eq_mul, RingHom.id_apply]
        rw [← mul_assoc, auxiliaryElement_commutes n a, mul_assoc] }
  have hmaps : ∀ x ∈ V, LC x ∈ V := by
    intro x hx
    change auxiliaryElement n * x ∈ V
    rw [← smul_eq_mul]
    exact V.smul_mem _ hx

  let L : Module.End A V := LC.restrict hmaps

  haveI : IsSimpleModule A V := _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule n la
  obtain ⟨μ, hμ⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
    (k := ℂ) (A := A) (V := V)).surjective L

  have hcl : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la ∈ V := Submodule.subset_span rfl
  have hLc : (L ⟨_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, hcl⟩ : A) = auxiliaryElement n * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la :=
    LinearMap.coe_restrict_apply hmaps _
  have hscal : (L ⟨_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la, hcl⟩ : A) = μ • (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : A) := by
    rw [← hμ]
    simp [Module.algebraMap_end_apply]
  have hCeq : auxiliaryElement n * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = μ • _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la := by
    rw [← hLc, hscal]

  have hμval : μ = (partitionAuxiliaryInt la : ℂ) := by
    have h1 : (auxiliaryElement n * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) 1
        = (μ • _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) 1 := by rw [hCeq]
    rw [sumTranspositions_youngSymmetrizer_coeff_one] at h1
    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      _root_.RepresentationTheory.PartitionAuxiliary.coeff_one_eq_one, mul_one] at h1
    exact h1.symm
  rw [hCeq, hμval]

/-- If an element belongs to an auxiliary collection indexed by a partition, left multiplication by the auxiliary element equals scalar multiplication by the cast of the partition’s auxiliary integer. -/
@[source_ref "Chapter5/Problem5.16.2" (role := primary)]
theorem auxiliaryElement_mul_eq_smul_of_mem
    (n : ℕ) (la : Nat.Partition n)
    (x : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) (hx : x ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :
    auxiliaryElement n * x = (partitionAuxiliaryInt la : ℂ) • x := by

  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [smul_eq_mul, ← mul_assoc, auxiliaryElement_commutes, mul_assoc,
    auxiliaryElement_mul_eq_smul_at_partition, mul_smul_comm]

end RepresentationTheory.Auxiliary.PartitionIndexedAlgebra

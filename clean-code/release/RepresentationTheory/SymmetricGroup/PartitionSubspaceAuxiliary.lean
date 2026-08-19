/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.YoungDiagram.PartitionFormulas
import RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics
import RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra
import RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
import RepresentationTheory.SymmetricGroupAlgebra.SignTwist
import RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# Partition subspace auxiliary results

This module records auxiliary computations for partition-indexed subspaces and their actions.
-/

namespace RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary

/-! ## Computable hook-length formulas -/

/-- A column length equals the number of sorted row lengths strictly exceeding the column index. -/
theorem YoungDiagram.colLen_eq_card_filter_sortedParts {m : ℕ} (μ : Nat.Partition m) (c : ℕ) :
    (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).colLen c
      = ((Finset.range (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).length).filter
          (fun i => c < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).getD i 0)).card := by
  rw [← Finset.card_range ((_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).colLen c)]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen,
      _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD]
  constructor
  · intro h
    refine ⟨?_, h⟩
    by_contra hge
    push Not at hge
    rw [List.getD_eq_default _ _ hge] at h
    exact absurd h (Nat.not_lt_zero c)
  · intro h; exact h.2

/-- The hook-length product is the product over cells of the expression computed from sorted row lengths and taller rows. -/
theorem hookLengthProduct_eq_prod_sortedParts {m : ℕ} (μ : Nat.Partition m) :
    _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ)
      = ∏ x ∈ (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).cells,
          ((_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).getD x.1 0
            + ((Finset.range (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).length).filter
                (fun r => x.2 < (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ).getD r 0)).card - x.1 - x.2 - 1) := by
  unfold _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic
  refine Finset.prod_congr rfl (fun x _ => ?_)
  rw [_root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryCellStatistic, _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD,
      YoungDiagram.colLen_eq_card_filter_sortedParts]

/-- A weakly decreasing list representing the parts of a partition is its sorted-parts list. -/
theorem sortedParts_eq_of_parts_eq_of_pairwise_ge {m : ℕ} (μ : Nat.Partition m) (L : List ℕ)
    (hμ : μ.parts = (↑L : Multiset ℕ)) (hL : L.Pairwise (· ≥ ·)) :
    (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ) = L := by
  unfold _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
  rw [hμ, Multiset.coe_sort]
  exact List.mergeSort_eq_self (r := (· ≥ ·)) hL

/-- A product formula computed from a partition's sorted row lengths determines its hook-length product. -/
theorem hookLengthProduct_eq_of_sortedParts_prod_eq {m : ℕ} (μ : Nat.Partition m) (L : List ℕ) (v : ℕ)
    (hL : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ) = L)
    (hv : ∏ x ∈ YoungDiagram.cellsOfRowLens L,
            (L.getD x.1 0
              + ((Finset.range L.length).filter
                  (fun r => x.2 < L.getD r 0)).card - x.1 - x.2 - 1) = v) :
    _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ) = v := by
  rw [hookLengthProduct_eq_prod_sortedParts]
  have hcells : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition μ).cells = YoungDiagram.cellsOfRowLens (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList μ) := rfl
  rw [hcells, hL]
  exact hv

/-- The product of the differences `n - k` for `k` in `range n` equals `n!`. -/
theorem prod_range_sub_eq_factorial (n : ℕ) : ∏ k ∈ Finset.range n, (n - k) = n.factorial := by
  rw [← Finset.prod_range_reflect (fun k => n - k) n]
  rw [show (∏ j ∈ Finset.range n, (n - (n - 1 - j))) = ∏ j ∈ Finset.range n, (j + 1) from
    Finset.prod_congr rfl (fun i hi => by rw [Finset.mem_range] at hi; omega)]
  exact Finset.prod_range_add_one_eq_factorial n

/-! ## The one-row partition `(n)`: the trivial representation -/

/-- An alternate auxiliary partition associated with a positive natural number. -/
def positivePartitionAuxiliaryAlt (n : ℕ) (hn : 0 < n) : Nat.Partition n where
  parts := {n}
  parts_pos := fun {i} hi => by rw [Multiset.mem_singleton] at hi; omega
  parts_sum := by simp

/-- The sorted-parts list of the alternate positive-size partition is the singleton containing its size. -/
theorem positivePartitionAuxiliaryAlt_sortedParts (n : ℕ) (hn : 0 < n) :
    (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (positivePartitionAuxiliaryAlt n hn)) = [n] :=
  sortedParts_eq_of_parts_eq_of_pairwise_ge _ [n] rfl (by simp)

/-- The hook-length product of the alternate auxiliary positive-size partition equals the factorial of its size. -/
theorem positivePartitionAuxiliaryAlt_hookLengthProduct_eq_factorial (n : ℕ) (hn : 0 < n) :
    _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (positivePartitionAuxiliaryAlt n hn)) = n.factorial := by
  refine hookLengthProduct_eq_of_sortedParts_prod_eq _ [n] _ (positivePartitionAuxiliaryAlt_sortedParts n hn) ?_
  have hcells : YoungDiagram.cellsOfRowLens [n] = ({0} : Finset ℕ) ×ˢ Finset.range n := by
    simp [YoungDiagram.cellsOfRowLens]
  rw [hcells, Finset.prod_product, Finset.prod_singleton, ← prod_range_sub_eq_factorial n]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hfil : ((Finset.range [n].length).filter
      (fun r => j < [n].getD r 0)).card = 1 := by
    rw [List.length_singleton, Finset.range_one, Finset.filter_singleton]
    simp [hj']
  rw [hfil]
  simp only [List.getD_cons_zero]
  omega

/-! ## The one-column partition `(1ⁿ)`: the sign representation -/

/-- An auxiliary partition associated with a positive natural number. -/
def positivePartitionAuxiliary (n : ℕ) (_hn : 0 < n) : Nat.Partition n where
  parts := Multiset.replicate n 1
  parts_pos := fun {i} hi => by have := Multiset.eq_of_mem_replicate hi; omega
  parts_sum := by rw [Multiset.sum_replicate]; simp

/-- The sorted parts of the auxiliary partition of positive size are a list of that many ones. -/
theorem positivePartitionAuxiliary_sortedParts_eq_replicate_one (n : ℕ) (hn : 0 < n) :
    (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList (positivePartitionAuxiliary n hn)) = List.replicate n 1 :=
  sortedParts_eq_of_parts_eq_of_pairwise_ge _ (List.replicate n 1) (Multiset.coe_replicate n 1).symm
    (List.pairwise_replicate_of_refl)

/-- The hook-length product of the auxiliary positive-size partition equals the factorial of its size. -/
theorem positivePartitionAuxiliary_hookLengthProduct_eq_factorial (n : ℕ) (hn : 0 < n) :
    _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition (positivePartitionAuxiliary n hn)) = n.factorial := by
  refine hookLengthProduct_eq_of_sortedParts_prod_eq _ (List.replicate n 1) _
    (positivePartitionAuxiliary_sortedParts_eq_replicate_one n hn) ?_
  have hcells : YoungDiagram.cellsOfRowLens (List.replicate n 1)
      = (Finset.range n) ×ˢ ({0} : Finset ℕ) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cellsOfRowLens, List.length_replicate, List.getElem_replicate,
      Nat.lt_one_iff, Finset.mem_product, Finset.mem_range, Finset.mem_singleton, exists_prop]
  rw [hcells, Finset.prod_product, ← prod_range_sub_eq_factorial n]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  rw [Finset.prod_singleton]
  have hget : (List.replicate n 1).getD i 0 = 1 := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi'),
        List.getElem_replicate]
  have hall : ∀ r ∈ Finset.range n,
      (0 : ℕ) < (List.replicate n 1).getD r 0 := by
    intro r hr
    rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact Finset.mem_range.mp hr),
        List.getElem_replicate]
    omega
  have hfil : ((Finset.range (List.replicate n 1).length).filter
      (fun r => (0 : ℕ) < (List.replicate n 1).getD r 0)).card = n := by
    rw [List.length_replicate, Finset.filter_true_of_mem hall, Finset.card_range]
  rw [hfil, hget]
  omega

/-! ## The headline theorems -/

/-- For positive size, the complex subspace attached to the alternate auxiliary partition has dimension one. -/
theorem finrank_positivePartitionAuxiliaryAlt_eq_one (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (positivePartitionAuxiliaryAlt n hn)) = 1 := by
  rw [_root_.RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct,
      positivePartitionAuxiliaryAlt_hookLengthProduct_eq_factorial n hn]
  exact Nat.div_self (Nat.factorial_pos n)

/-- For positive size, the complex subspace attached to the auxiliary partition has dimension one. -/
theorem finrank_positivePartitionAuxiliary_eq_one (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (positivePartitionAuxiliary n hn)) = 1 := by
  rw [_root_.RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct,
      positivePartitionAuxiliary_hookLengthProduct_eq_factorial n hn]
  exact Nat.div_self (Nat.factorial_pos n)

/-! ### The four small explicit partitions -/

/-- An auxiliary partition of three. -/
def partitionThreeAuxiliary : Nat.Partition 3 where
  parts := {2, 1}
  parts_pos := by decide
  parts_sum := by decide

/-- A second auxiliary partition of four. -/
def partitionFourAuxiliaryTwo : Nat.Partition 4 where
  parts := {2, 2}
  parts_pos := by decide
  parts_sum := by decide

/-- A third auxiliary partition of four. -/
def partitionFourAuxiliaryThree : Nat.Partition 4 where
  parts := {3, 1}
  parts_pos := by decide
  parts_sum := by decide

/-- A first auxiliary partition of four. -/
def partitionFourAuxiliaryOne : Nat.Partition 4 where
  parts := {2, 1, 1}
  parts_pos := by decide
  parts_sum := by decide

/-- The complex subspace associated with the auxiliary partition of three has dimension two. -/
@[source_ref "Chapter5/Example5.12.3" (role := supporting)]
theorem finrank_partitionThreeAuxiliary_eq_two :
    Module.finrank ℂ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 3 partitionThreeAuxiliary) = 2 := by
  rw [_root_.RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct,
      hookLengthProduct_eq_of_sortedParts_prod_eq partitionThreeAuxiliary [2, 1] 3 (sortedParts_eq_of_parts_eq_of_pairwise_ge _ [2, 1] rfl (by decide))
        (by decide)]
  rfl

/-- The complex subspace associated with the second auxiliary partition of four has dimension two. -/
@[source_ref "Chapter5/Example5.12.3" (role := supporting)]
theorem finrank_partitionFourAuxiliaryTwo_eq_two :
    Module.finrank ℂ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryTwo) = 2 := by
  rw [_root_.RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct,
      hookLengthProduct_eq_of_sortedParts_prod_eq partitionFourAuxiliaryTwo [2, 2] 12 (sortedParts_eq_of_parts_eq_of_pairwise_ge _ [2, 2] rfl (by decide))
        (by decide)]
  rfl

/-- The complex subspace associated with the third auxiliary partition of four has dimension three. -/
theorem finrank_partitionFourAuxiliaryThree_eq_three :
    Module.finrank ℂ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryThree) = 3 := by
  rw [_root_.RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct,
      hookLengthProduct_eq_of_sortedParts_prod_eq partitionFourAuxiliaryThree [3, 1] 8 (sortedParts_eq_of_parts_eq_of_pairwise_ge _ [3, 1] rfl (by decide))
        (by decide)]
  rfl

/-- The complex subspace associated with the first auxiliary partition of four has dimension three. -/
theorem finrank_partitionFourAuxiliaryOne_eq_three :
    Module.finrank ℂ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryOne) = 3 := by
  rw [_root_.RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card, _root_.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct,
      hookLengthProduct_eq_of_sortedParts_prod_eq partitionFourAuxiliaryOne [2, 1, 1] 8 (sortedParts_eq_of_parts_eq_of_pairwise_ge _ [2, 1, 1] rfl (by decide))
        (by decide)]
  rfl

/-! ### Two auxiliary three-dimensional cases -/

/-- The displayed auxiliary map sends the third auxiliary partition of four to the first one. -/
theorem partitionFourAuxiliaryThree_auxiliaryMap_eq_partitionFourAuxiliaryOne : _root_.RepresentationTheory.SymmetricGroupAlgebra.SignTwist.Partition.selfMap partitionFourAuxiliaryThree = partitionFourAuxiliaryOne := by
  apply Nat.Partition.ext
  change (↑((_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition partitionFourAuxiliaryThree).transpose.rowLens) : Multiset ℕ) = ({2, 1, 1} : Multiset ℕ)
  have hsp : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList partitionFourAuxiliaryThree) = [3, 1] := sortedParts_eq_of_parts_eq_of_pairwise_ge _ [3, 1] rfl (by decide)
  have hc0 : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition partitionFourAuxiliaryThree).colLen 0 = 2 := by
    rw [YoungDiagram.colLen_eq_card_filter_sortedParts, hsp]; decide
  have hc1 : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition partitionFourAuxiliaryThree).colLen 1 = 1 := by
    rw [YoungDiagram.colLen_eq_card_filter_sortedParts, hsp]; decide
  have hc2 : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition partitionFourAuxiliaryThree).colLen 2 = 1 := by
    rw [YoungDiagram.colLen_eq_card_filter_sortedParts, hsp]; decide
  have hlen : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition partitionFourAuxiliaryThree).transpose.colLen 0 = 3 := by
    rw [YoungDiagram.colLen_transpose, _root_.RepresentationTheory.YoungDiagram.PartitionFormulas.Partition.toYoungDiagram_rowLen_eq_getD, hsp]; rfl
  have hrl : (_root_.RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition partitionFourAuxiliaryThree).transpose.rowLens = [2, 1, 1] := by
    simp only [YoungDiagram.rowLens, hlen]
    rw [show List.range 3 = [0, 1, 2] by decide]
    simp only [List.map_cons, List.map_nil, YoungDiagram.rowLen_transpose, hc0, hc1, hc2]
  rw [hrl]; rfl

/-- There exists an auxiliary map satisfying the displayed sign-twisted action equation. -/
theorem exists_auxiliaryMap_signTwist :
    ∃ e : ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryThree) ≃ₗ[ℂ] ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryOne),
      ∀ (g : Equiv.Perm (Fin 4)) (x : ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryThree)),
        e ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin 4)) g) • x)
          = ((Equiv.Perm.sign g : ℤ) : ℂ)
              • ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin 4)) g) • e x) := by
  have h := _root_.RepresentationTheory.SymmetricGroupAlgebra.SignTwist.exists_signTwistedEquivariantMap 4 partitionFourAuxiliaryThree
  rw [partitionFourAuxiliaryThree_auxiliaryMap_eq_partitionFourAuxiliaryOne] at h
  exact h

/-- There is no linear equivalence between the subspaces attached to the third and first auxiliary partitions of four. -/
theorem isEmpty_linearEquiv_partitionFourAuxiliaryThree_one :
    IsEmpty (↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryThree) ≃ₗ[_root_.RepresentationTheory.PartitionAuxiliary.natIndexedType 4] ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryOne)) :=
  _root_.RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra.isEmpty_linearEquiv_of_ne_partition 4 partitionFourAuxiliaryThree partitionFourAuxiliaryOne (by decide)

/-! ## One-dimensional auxiliary actions -/

/-- The indicated auxiliary quantity applied to a list of repeated ones equals zero. -/
theorem replicate_one_auxiliary_eq_zero (n k : ℕ) : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (List.replicate n 1) k = 0 := by
  induction n generalizing k with
  | zero => simp [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn]
    split_ifs with h
    · omega
    · exact ih (k - 1)

/-- Below the list length, the indicated auxiliary quantity of a repeated-one list equals its index. -/
theorem replicate_one_auxiliary_eq_index (n : ℕ) :
    ∀ k, k < n → _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (List.replicate n 1) k = k := by
  induction n with
  | zero => intro k hk; omega
  | succ m ih =>
    intro k hk
    rw [List.replicate_succ]
    simp only [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow]
    split_ifs with h
    · omega
    · rw [ih (k - 1) (by omega)]; omega

/-! ### The one-row partition `(n)`: trivial action -/

/-- Every permutation satisfies the displayed membership condition for the alternate auxiliary partition. -/
theorem perm_mem_positivePartitionAuxiliaryAlt (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n (positivePartitionAuxiliaryAlt n hn) := by
  have hrow : ∀ j : Fin n, _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow [n] j.val = 0 := fun j => by
    simp only [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow]; exact if_pos j.isLt
  intro k
  rw [positivePartitionAuxiliaryAlt_sortedParts n hn, hrow (σ k), hrow k]

/-- A permutation satisfying the displayed membership condition for the alternate auxiliary partition is the identity. -/
theorem mem_positivePartitionAuxiliaryAlt_imp_eq_one (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n (positivePartitionAuxiliaryAlt n hn)) : σ = 1 := by
  have hcol : ∀ j : Fin n, _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn [n] j.val = j.val := fun j => by
    simp only [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn]; exact if_pos j.isLt
  apply Equiv.Perm.ext
  intro k
  have h := hσ k
  rw [positivePartitionAuxiliaryAlt_sortedParts n hn, hcol (σ k), hcol k] at h
  rw [Equiv.Perm.one_apply]
  exact Fin.ext h

/-- The indicated auxiliary quantity of the alternate positive-size partition equals one. -/
theorem positivePartitionAuxiliaryAlt_auxiliary_eq_one (n : ℕ) (hn : 0 < n) :
    _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n (positivePartitionAuxiliaryAlt n hn) = 1 := by
  classical
  have htriv : ∀ g : ↥(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n (positivePartitionAuxiliaryAlt n hn)), (g : Equiv.Perm (Fin n)) = 1 :=
    fun g => mem_positivePartitionAuxiliaryAlt_imp_eq_one n hn g.val g.prop
  haveI : Unique ↥(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n (positivePartitionAuxiliaryAlt n hn)) :=
    ⟨⟨⟨1, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n (positivePartitionAuxiliaryAlt n hn)).one_mem⟩⟩, fun g => Subtype.ext (htriv g)⟩
  simp only [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA, htriv, Units.val_one, Int.cast_one,
    one_smul, map_one, Finset.sum_const, Finset.card_univ, Fintype.card_unique]

/-- Left multiplication by any permutation fixes the indicated element for the alternate auxiliary partition. -/
theorem perm_mul_positivePartitionAuxiliaryAlt_element_eq_self (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n (positivePartitionAuxiliaryAlt n hn)
      = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n (positivePartitionAuxiliaryAlt n hn) := by
  rw [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, positivePartitionAuxiliaryAlt_auxiliary_eq_one n hn, one_mul]
  exact _root_.RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.perm_mul_eq_self_of_mem σ (perm_mem_positivePartitionAuxiliaryAlt n hn σ)

/-! ### The one-column partition `(1ⁿ)`: sign action -/

/-- Every permutation satisfies the displayed membership condition for the auxiliary positive-size partition. -/
theorem perm_mem_positivePartitionAuxiliary (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n (positivePartitionAuxiliary n hn) := by
  intro k
  rw [positivePartitionAuxiliary_sortedParts_eq_replicate_one n hn, replicate_one_auxiliary_eq_zero, replicate_one_auxiliary_eq_zero]

/-- A permutation satisfying the displayed membership condition for the auxiliary positive-size partition is the identity. -/
theorem mem_positivePartitionAuxiliary_imp_eq_one (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n (positivePartitionAuxiliary n hn)) : σ = 1 := by
  apply Equiv.Perm.ext
  intro k
  have h := hσ k
  rw [positivePartitionAuxiliary_sortedParts_eq_replicate_one n hn,
    replicate_one_auxiliary_eq_index n (σ k).val (σ k).isLt,
    replicate_one_auxiliary_eq_index n k.val k.isLt] at h
  rw [Equiv.Perm.one_apply]
  exact Fin.ext h

/-- The indicated auxiliary quantity of the positive-size partition equals one. -/
theorem positivePartitionAuxiliary_auxiliary_eq_one (n : ℕ) (hn : 0 < n) :
    _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n (positivePartitionAuxiliary n hn) = 1 := by
  classical
  have htriv : ∀ g : ↥(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n (positivePartitionAuxiliary n hn)), (g : Equiv.Perm (Fin n)) = 1 :=
    fun g => mem_positivePartitionAuxiliary_imp_eq_one n hn g.val g.prop
  haveI : Unique ↥(_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n (positivePartitionAuxiliary n hn)) :=
    ⟨⟨⟨1, (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n (positivePartitionAuxiliary n hn)).one_mem⟩⟩, fun g => Subtype.ext (htriv g)⟩
  simp only [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB, htriv, map_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_nsmul]

/-- Left multiplication by a permutation scales the indicated auxiliary element by the permutation's sign. -/
theorem perm_mul_positivePartitionAuxiliary_element_eq_sign_smul (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n (positivePartitionAuxiliary n hn)
      = ((↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) • _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n (positivePartitionAuxiliary n hn) := by
  rw [_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC, positivePartitionAuxiliary_auxiliary_eq_one n hn, mul_one]
  exact _root_.RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.perm_mul_eq_sign_smul_of_mem σ (perm_mem_positivePartitionAuxiliary n hn σ)

/-! ### From the generator to the whole module -/

/-- If the displayed subtype has complex dimension one and a permutation acts on the indicated auxiliary element by a scalar, then it acts on every element by that scalar. -/
theorem smul_eq_scalar_smul_of_finrank_one_of_auxiliary_eq (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) (χ : ℂ)
    (hdim : Module.finrank ℂ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) = 1)
    (hgen : (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n)
        * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = χ • _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la)
    (v : _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) :
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) • v = χ • v := by
  classical
  have hcne : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la ≠ 0 := by
    intro h0
    have hbot : _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la = ⊥ := by
      rw [_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule, h0]; exact Submodule.span_singleton_eq_bot.mpr rfl
    rw [hbot, Module.finrank_zero_of_subsingleton] at hdim
    exact one_ne_zero hdim.symm
  have hmem_c : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la ∈ _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la := Submodule.subset_span rfl
  have hspan_le : Submodule.span ℂ {_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la}
      ≤ (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ := by
    rw [Submodule.span_singleton_le_iff_mem]; exact hmem_c
  have hfin : Module.finrank ℂ ((_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ) = 1 := hdim
  have hspaneq : Submodule.span ℂ {_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la}
      = (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la).restrictScalars ℂ :=
    Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hfin, finrank_span_singleton hcne])
  have hv_mem : (v : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) ∈ Submodule.span ℂ {_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la} := by
    rw [hspaneq]; exact v.2
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hv_mem
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_eq_mul, ← hz,
    Algebra.mul_smul_comm, hgen, smul_comm]

/-- Every permutation fixes each vector in the subspace associated with the alternate auxiliary partition. -/
@[source_ref "Chapter5/Example5.12.3" (role := primary)]
theorem perm_smul_positivePartitionAuxiliaryAlt_eq_self (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (v : _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (positivePartitionAuxiliaryAlt n hn)) :
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) • v = v := by
  have h := smul_eq_scalar_smul_of_finrank_one_of_auxiliary_eq n (positivePartitionAuxiliaryAlt n hn) σ 1 (finrank_positivePartitionAuxiliaryAlt_eq_one n hn)
    (by rw [one_smul]; exact perm_mul_positivePartitionAuxiliaryAlt_element_eq_self n hn σ) v
  rwa [one_smul] at h

/-- A permutation acts on the auxiliary subtype by multiplication by its sign. -/
@[source_ref "Chapter5/Example5.12.3" (role := primary)]
theorem perm_smul_positivePartitionAuxiliary_eq_sign_smul (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (v : _root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule n (positivePartitionAuxiliary n hn)) :
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : _root_.RepresentationTheory.PartitionAuxiliary.natIndexedType n) • v
      = ((↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) • v :=
  smul_eq_scalar_smul_of_finrank_one_of_auxiliary_eq n (positivePartitionAuxiliary n hn) σ _ (finrank_positivePartitionAuxiliary_eq_one n hn)
    (perm_mul_positivePartitionAuxiliary_element_eq_sign_smul n hn σ) v

/-! ## Auxiliary isomorphism orientation -/

section Orientation

open _root_.RepresentationTheory.PermutationDegreeFour

/-- For every partition, the indicated auxiliary product is nonzero. -/
theorem partition_auxiliaryProduct_ne_zero (n : ℕ) (la : Nat.Partition n) :
    _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la ≠ 0 := by
  intro h
  apply _root_.RepresentationTheory.PartitionAuxiliary.self_mul_ne_zero n la
  have hy : _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n la = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n la * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n la := rfl
  nth_rewrite 1 [hy]
  rw [mul_assoc, h, mul_zero]

/-- The sorted parts of the third auxiliary partition of four are three and one. -/
theorem partitionFourAuxiliaryThree_sortedParts : (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList partitionFourAuxiliaryThree) = [3, 1] :=
  sortedParts_eq_of_parts_eq_of_pairwise_ge _ [3, 1] rfl (by decide)

/-- The transposition swapping zero and one satisfies the displayed membership condition for the third auxiliary partition of four. -/
theorem swap_zero_one_mem_partitionFourAuxiliaryThree :
    Equiv.swap (0 : Fin 4) 1 ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB 4 partitionFourAuxiliaryThree := by
  intro k
  rw [partitionFourAuxiliaryThree_sortedParts]
  revert k
  decide

/-- The transposition swapping one and two satisfies the displayed membership condition for the third auxiliary partition of four. -/
theorem swap_one_two_mem_partitionFourAuxiliaryThree :
    Equiv.swap (1 : Fin 4) 2 ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB 4 partitionFourAuxiliaryThree := by
  intro k
  rw [partitionFourAuxiliaryThree_sortedParts]
  revert k
  decide

/-- An auxiliary element of the displayed subtype associated with the third auxiliary partition of four. -/
noncomputable def partitionFourAuxiliaryThree_auxiliaryElement : ↥(_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryThree) :=
  ⟨_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB 4 partitionFourAuxiliaryThree * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC 4 partitionFourAuxiliaryThree,
    (_root_.RepresentationTheory.PartitionAuxiliary.partitionSubmodule 4 partitionFourAuxiliaryThree).smul_mem (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB 4 partitionFourAuxiliaryThree) (Submodule.subset_span rfl)⟩

/-- The auxiliary element of the displayed subtype for the third auxiliary partition of four is nonzero. -/
theorem partitionFourAuxiliaryThree_auxiliaryElement_ne_zero : partitionFourAuxiliaryThree_auxiliaryElement ≠ 0 := by
  intro h
  exact partition_auxiliaryProduct_ne_zero 4 partitionFourAuxiliaryThree (congrArg Subtype.val h)

/-- A permutation satisfying the displayed membership condition fixes the auxiliary element of the third auxiliary partition. -/
theorem partitionFourAuxiliaryThree_auxiliaryElement_fixed_of_mem (σ : Equiv.Perm (Fin 4)) (hσ : σ ∈ _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB 4 partitionFourAuxiliaryThree) :
    _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionSubspaceRepresentation 4 partitionFourAuxiliaryThree σ partitionFourAuxiliaryThree_auxiliaryElement = partitionFourAuxiliaryThree_auxiliaryElement := by
  apply Subtype.ext
  change MonoidAlgebra.of ℂ (Equiv.Perm (Fin 4)) σ
        * (_root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB 4 partitionFourAuxiliaryThree * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC 4 partitionFourAuxiliaryThree)
      = _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB 4 partitionFourAuxiliaryThree * _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC 4 partitionFourAuxiliaryThree
  rw [← mul_assoc, _root_.RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.perm_mul_eq_self_of_mem σ hσ]

/-- For distinct indices, acting by their swap evaluates as the negative of the original vector at the swapped coordinate. -/
theorem swap_action_apply_eq_neg_apply_swap (a b : Fin 4) (hab : a ≠ b) (v : ↥(_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryCoordinateSubrepresentationFinFour.toSubmodule)) (i : Fin 4) :
    (_root_.RepresentationTheory.PermutationDegreeFour.twistRepresentationByCharacter _root_.RepresentationTheory.PermutationDegreeFour.signCharacter _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryCoordinateSubrepresentationFinFour.toRepresentation (Equiv.swap a b) v).1 i
      = -(v.1 (Equiv.swap a b i)) := by
  rw [_root_.RepresentationTheory.PermutationDegreeFour.twistRepresentationByCharacter_apply, _root_.RepresentationTheory.PermutationDegreeFour.coe_signCharacter, Equiv.Perm.sign_swap hab]
  change ((-1 : ℤ) : ℂ) * (_root_.RepresentationTheory.PermutationDegreeFour.coordinatePermutationRepresentationFinFour (Equiv.swap a b) v.1 i) = _
  rw [_root_.RepresentationTheory.PermutationDegreeFour.coordinatePermutationRepresentationFinFour_apply, Equiv.swap_inv]
  ring

/-- A vector in the indicated subrepresentation fixed by the swaps of zero with one and one with two is zero. -/
theorem eq_zero_of_swap_zero_one_fixed_of_swap_one_two_fixed (v : ↥(_root_.RepresentationTheory.PermutationDegreeFour.auxiliaryCoordinateSubrepresentationFinFour.toSubmodule))
    (h1 : _root_.RepresentationTheory.PermutationDegreeFour.twistRepresentationByCharacter _root_.RepresentationTheory.PermutationDegreeFour.signCharacter _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryCoordinateSubrepresentationFinFour.toRepresentation (Equiv.swap (0 : Fin 4) 1) v = v)
    (h2 : _root_.RepresentationTheory.PermutationDegreeFour.twistRepresentationByCharacter _root_.RepresentationTheory.PermutationDegreeFour.signCharacter _root_.RepresentationTheory.PermutationDegreeFour.auxiliaryCoordinateSubrepresentationFinFour.toRepresentation (Equiv.swap (1 : Fin 4) 2) v = v) :
    v = 0 := by
  have e1 : ∀ i, -(v.1 (Equiv.swap (0 : Fin 4) 1 i)) = v.1 i := fun i => by
    rw [← swap_action_apply_eq_neg_apply_swap 0 1 (by decide) v i, h1]
  have e2 : ∀ i, -(v.1 (Equiv.swap (1 : Fin 4) 2 i)) = v.1 i := fun i => by
    rw [← swap_action_apply_eq_neg_apply_swap 1 2 (by decide) v i, h2]
  have h2' := e1 2
  rw [show Equiv.swap (0 : Fin 4) 1 2 = 2 by decide] at h2'
  have hv2 : v.1 2 = 0 := by linear_combination -h2' / 2
  have h3' := e1 3
  rw [show Equiv.swap (0 : Fin 4) 1 3 = 3 by decide] at h3'
  have hv3 : v.1 3 = 0 := by linear_combination -h3' / 2
  have h0' := e2 0
  rw [show Equiv.swap (1 : Fin 4) 2 0 = 0 by decide] at h0'
  have hv0 : v.1 0 = 0 := by linear_combination -h0' / 2
  have h1' := e1 0
  rw [show Equiv.swap (0 : Fin 4) 1 0 = 1 by decide] at h1'
  have hv1 : v.1 1 = 0 := by linear_combination -h1' - hv0
  apply Subtype.ext
  funext i
  fin_cases i <;> assumption

/-- A representation isomorphism sends a vector fixed by an element to a vector fixed by that element. -/
theorem isoToLinearEquiv_map_eq_self_of_eq_self {V W : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType} (e : V ≅ W) (g : _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) (v : V)
    (hv : V.ρ g v = v) : W.ρ g (FDRep.isoToLinearEquiv e v) = FDRep.isoToLinearEquiv e v := by
  rw [FDRep.Iso.conj_ρ e g, LinearEquiv.conj_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [hv]

/-- The displayed complex module built from the third auxiliary partition of four has dimension three. -/
theorem finrank_auxiliaryObject_partitionFourAuxiliaryThree_eq_three :
    Module.finrank ℂ ((_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep 4 partitionFourAuxiliaryThree : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) : Type) = 3 :=
  finrank_partitionFourAuxiliaryThree_eq_three

/-- The displayed complex module built from the first auxiliary partition of four has dimension three. -/
theorem finrank_auxiliaryObject_partitionFourAuxiliaryOne_eq_three :
    Module.finrank ℂ ((_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep 4 partitionFourAuxiliaryOne : FDRep ℂ _root_.RepresentationTheory.PermutationDegreeFour.AuxiliaryType) : Type) = 3 :=
  finrank_partitionFourAuxiliaryOne_eq_three

/-- The displayed isomorphism type involving the third auxiliary partition of four is nonempty. -/
@[source_ref "Chapter5/Example5.12.3" (role := supporting)]
theorem nonempty_auxiliaryIso_partitionFourAuxiliaryThree :
    Nonempty (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep 4 partitionFourAuxiliaryThree ≅ _root_.RepresentationTheory.PermutationDegreeFour.reducedCoordinateRepresentation) := by
  rcases _root_.RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary.simple_iso_auxiliary_cases (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep 4 partitionFourAuxiliaryThree) with h | h | h | h | h
  · exact absurd (((FDRep.isoToLinearEquiv h.some).finrank_eq).symm.trans
      finrank_auxiliaryObject_partitionFourAuxiliaryThree_eq_three) (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationTwo]; decide)
  · exact absurd (((FDRep.isoToLinearEquiv h.some).finrank_eq).symm.trans
      finrank_auxiliaryObject_partitionFourAuxiliaryThree_eq_three) (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationOne]; decide)
  · exact absurd (((FDRep.isoToLinearEquiv h.some).finrank_eq).symm.trans
      finrank_auxiliaryObject_partitionFourAuxiliaryThree_eq_three) (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_inducedReducedCoordinateRepresentation]; decide)
  · exact h
  · -- `V_{(3,1)}` has a vector fixed by `(0 1)` and `(1 2)`; `ℂ³₊` has none.
    exfalso
    obtain ⟨e⟩ := h
    set u := FDRep.isoToLinearEquiv e partitionFourAuxiliaryThree_auxiliaryElement with hu
    have hu0 : u ≠ 0 := fun h0 => partitionFourAuxiliaryThree_auxiliaryElement_ne_zero
      ((FDRep.isoToLinearEquiv e).injective (by rw [← hu, h0, map_zero]))
    refine hu0 (eq_zero_of_swap_zero_one_fixed_of_swap_one_two_fixed u ?_ ?_)
    · exact isoToLinearEquiv_map_eq_self_of_eq_self e _ partitionFourAuxiliaryThree_auxiliaryElement
        (partitionFourAuxiliaryThree_auxiliaryElement_fixed_of_mem _ swap_zero_one_mem_partitionFourAuxiliaryThree)
    · exact isoToLinearEquiv_map_eq_self_of_eq_self e _ partitionFourAuxiliaryThree_auxiliaryElement
        (partitionFourAuxiliaryThree_auxiliaryElement_fixed_of_mem _ swap_one_two_mem_partitionFourAuxiliaryThree)

/-- The displayed isomorphism type involving the first auxiliary partition of four is nonempty. -/
@[source_ref "Chapter5/Example5.12.3" (role := supporting)]
theorem nonempty_auxiliaryIso_partitionFourAuxiliaryOne :
    Nonempty (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep 4 partitionFourAuxiliaryOne ≅ _root_.RepresentationTheory.PermutationDegreeFour.signTwistedReducedCoordinateRepresentation) := by
  rcases _root_.RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary.simple_iso_auxiliary_cases (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep 4 partitionFourAuxiliaryOne) with h | h | h | h | h
  · exact absurd (((FDRep.isoToLinearEquiv h.some).finrank_eq).symm.trans
      finrank_auxiliaryObject_partitionFourAuxiliaryOne_eq_three) (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationTwo]; decide)
  · exact absurd (((FDRep.isoToLinearEquiv h.some).finrank_eq).symm.trans
      finrank_auxiliaryObject_partitionFourAuxiliaryOne_eq_three) (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_auxiliaryRepresentationOne]; decide)
  · exact absurd (((FDRep.isoToLinearEquiv h.some).finrank_eq).symm.trans
      finrank_auxiliaryObject_partitionFourAuxiliaryOne_eq_three) (by rw [_root_.RepresentationTheory.PermutationDegreeFour.finrank_inducedReducedCoordinateRepresentation]; decide)
  · -- `V_{(2,1,1)} ≅ ℂ³₋ ≅ V_{(3,1)}` would force `(2,1,1) = (3,1)`.
    exfalso
    obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := nonempty_auxiliaryIso_partitionFourAuxiliaryThree
    have hchar : ∀ σ, _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue 4 partitionFourAuxiliaryOne σ = _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPartitionPermutationValue 4 partitionFourAuxiliaryThree σ := by
      intro σ
      rw [← _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep_character_eq_auxiliary, ← _root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.partitionFDRep_character_eq_auxiliary,
        congrFun (FDRep.char_iso e) σ, congrFun (FDRep.char_iso e') σ]
    exact absurd (_root_.RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.eq_of_auxiliaryPartitionPermutationValue_eq 4 hchar) (by decide)
  · exact h

end Orientation

end RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary

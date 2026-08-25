/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionSubmodules










namespace RepresentationTheory.AuxiliaryPartitionIndexMaps

noncomputable section



private def KostkaOrderedCell {n : ℕ} {nu mu : Nat.Partition n}
    (_T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) := RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu

private noncomputable instance kostkaOrderedCellFintype
    {n : ℕ} {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    Fintype (KostkaOrderedCell T) :=
  RepresentationTheory.Partition.YoungDiagram.cellsFintype n nu

private def kostkaOrderedCellOfCell {n : ℕ} {nu mu : Nat.Partition n}
    (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) : KostkaOrderedCell T :=
  ⟨c.1, c.2⟩

private def kostkaCellKey {n : ℕ} {nu mu : Nat.Partition n}
    (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c : KostkaOrderedCell T) :
    ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (T.1 c.1.1 c.1.2, toLex (c.1.1, c.1.2))

private theorem kostkaCellKey_injective {n : ℕ} {nu mu : Nat.Partition n}
    (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) : Function.Injective (kostkaCellKey T) := by
  intro c d h
  apply Subtype.ext
  have hpair : (c.1.1, c.1.2) = (d.1.1, d.1.2) := by
    exact congrArg (fun x : ℕ ×ₗ (ℕ ×ₗ ℕ) => ofLex (ofLex x).2) h
  exact hpair

private noncomputable instance kostkaOrderedCellLinearOrder
    {n : ℕ} {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    LinearOrder (KostkaOrderedCell T) :=
  LinearOrder.lift' (kostkaCellKey T) (kostkaCellKey_injective T)

private theorem card_kostkaOrderedCell {n : ℕ} {nu mu : Nat.Partition n}
    (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) : Fintype.card (KostkaOrderedCell T) = n := by
  simpa only [KostkaOrderedCell, Fintype.card_fin] using
    (Fintype.card_congr (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu)).symm


private theorem cell_mem_partitionDiagram {n : ℕ} {nu : Nat.Partition n}
    (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) : c.1 ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) := by
  change c.1 ∈ YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) _
  rw [YoungDiagram.mem_ofRowLens]
  refine ⟨c.2.1, ?_⟩
  have hc := c.2.2
  rw [List.getD_eq_getElem _ _ c.2.1] at hc
  exact hc



private noncomputable def kostkaCellOrderIso {n : ℕ} {nu mu : Nat.Partition n}
    (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) : Fin n ≃o KostkaOrderedCell T :=
  Fintype.orderIsoFinOfCardEq (KostkaOrderedCell T) (card_kostkaOrderedCell T)



/-- Maps a partition-indexed object to the displayed auxiliary type. -/
noncomputable def _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.toAuxiliaryObject {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu := by
  let e := kostkaCellOrderIso T
  let rank : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu → Fin n := fun c =>
    e.symm (kostkaOrderedCellOfCell T c)
  refine ⟨rank, ?_, ?_, ?_⟩
  · exact e.symm.bijective
  · intro c₁ c₂ hrow hcol
    change e.symm (kostkaOrderedCellOfCell T c₁) <
      e.symm (kostkaOrderedCellOfCell T c₂)
    apply e.symm.lt_iff_lt.mpr
    change kostkaCellKey T (kostkaOrderedCellOfCell T c₁) <
      kostkaCellKey T (kostkaOrderedCellOfCell T c₂)
    simp only [kostkaCellKey, kostkaOrderedCellOfCell]
    rw [Prod.Lex.toLex_lt_toLex]
    have hweak : T.1 c₁.1.1 c₁.1.2 ≤ T.1 c₂.1.1 c₂.1.2 := by
      simpa [hrow] using T.1.row_weak hcol (cell_mem_partitionDiagram c₂)
    rcases hweak.eq_or_lt with heq | hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨hrow, hcol⟩
    · exact Or.inl hlt
  · intro c₁ c₂ hcol hrow
    change e.symm (kostkaOrderedCellOfCell T c₁) <
      e.symm (kostkaOrderedCellOfCell T c₂)
    apply e.symm.lt_iff_lt.mpr
    change kostkaCellKey T (kostkaOrderedCellOfCell T c₁) <
      kostkaCellKey T (kostkaOrderedCellOfCell T c₂)
    simp only [kostkaCellKey, kostkaOrderedCellOfCell]
    rw [Prod.Lex.toLex_lt_toLex]
    refine Or.inl ?_
    simpa [hcol] using T.1.col_strict hrow (cell_mem_partitionDiagram c₂)

private theorem KostkaTableau.standardization_lt_iff_key_lt {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    T.toAuxiliaryObject.1 c < T.toAuxiliaryObject.1 d ↔
      kostkaCellKey T (kostkaOrderedCellOfCell T c) <
        kostkaCellKey T (kostkaOrderedCellOfCell T d) := by
  change (kostkaCellOrderIso T).symm (kostkaOrderedCellOfCell T c) <
      (kostkaCellOrderIso T).symm (kostkaOrderedCellOfCell T d) ↔ _
  exact (kostkaCellOrderIso T).symm.lt_iff_lt


/-- A strict inequality between two entries implies the corresponding strict inequality between auxiliary indices. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_lt_of_entry_lt {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)
    (h : T.1 c.1.1 c.1.2 < T.1 d.1.1 d.1.2) :
    T.toAuxiliaryObject.1 c < T.toAuxiliaryObject.1 d := by
  rw [KostkaTableau.standardization_lt_iff_key_lt T]
  simp only [kostkaCellKey, kostkaOrderedCellOfCell, Prod.Lex.toLex_lt_toLex]
  exact Or.inl h



/-- Ordering the displayed auxiliary indices orders the corresponding natural-number entries. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_le_entry_of_auxiliary_le {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)
    (h : T.toAuxiliaryObject.1 c ≤ T.toAuxiliaryObject.1 d) :
    T.1 c.1.1 c.1.2 ≤ T.1 d.1.1 d.1.2 := by
  by_contra hnot
  have hdc : T.1 d.1.1 d.1.2 < T.1 c.1.1 c.1.2 := Nat.lt_of_not_ge hnot
  exact (not_lt_of_ge h) (RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_lt_of_entry_lt T d c hdc)

private theorem mem_partitionDiagram_iff_cell_condition {n : ℕ}
    {nu : Nat.Partition n} (c : ℕ × ℕ) :
    c ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) ↔
      c.1 < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu).length ∧ c.2 < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu).getD c.1 0 := by
  change c ∈ YoungDiagram.ofRowLens (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) _ ↔ _
  rw [YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨hrow, hcol⟩
    refine ⟨hrow, ?_⟩
    rw [List.getD_eq_getElem _ _ hrow]
    exact hcol
  · rintro ⟨hrow, hcol⟩
    refine ⟨hrow, ?_⟩
    rw [List.getD_eq_getElem _ _ hrow] at hcol
    exact hcol

private theorem KostkaTableau.card_cells_entry_lt {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (k : ℕ) :
    ((Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter
      (fun c => T.1 c.1.1 c.1.2 < k)).card =
      ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take k).sum := by
  rw [← RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_card_filter_lt_eq_sum_take T k]
  let s := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter
    (fun c => T.1 c.1.1 c.1.2 < k)
  calc
    s.card = (s.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = ((RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu).cells.filter (fun c => T.1 c.1 c.2 < k)).card := by
      congr 1
      ext c
      simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, YoungDiagram.mem_cells]
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨cell_mem_partitionDiagram d, hd⟩
      · rintro ⟨hc, hentry⟩
        exact ⟨⟨c, (mem_partitionDiagram_iff_cell_condition c).mp hc⟩,
          hentry, rfl⟩

private theorem KostkaTableau.prefix_le_standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take (T.1 c.1.1 c.1.2)).sum ≤
      (T.toAuxiliaryObject.1 c).val := by
  let s := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter
    (fun d => T.1 d.1.1 d.1.2 < T.1 c.1.1 c.1.2)
  have hmaps : Set.MapsTo (fun d => T.toAuxiliaryObject.1 d)
      (↑s : Set (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)) (↑(Finset.Iio (T.toAuxiliaryObject.1 c)) : Set (Fin n)) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    rw [Finset.mem_coe, Finset.mem_Iio]
    exact RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_lt_of_entry_lt T d c hd.2
  have hinj : Set.InjOn (fun d => T.toAuxiliaryObject.1 d) (↑s : Set (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)) :=
    T.toAuxiliaryObject.2.1.1.injOn
  have hcard := Finset.card_le_card_of_injOn
    (fun d => T.toAuxiliaryObject.1 d) hmaps hinj
  rw [show s.card = ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take (T.1 c.1.1 c.1.2)).sum by
      exact KostkaTableau.card_cells_entry_lt T _, Fin.card_Iio] at hcard
  exact hcard

private theorem KostkaTableau.standardization_lt_nextPrefix {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    (T.toAuxiliaryObject.1 c).val <
      ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take (T.1 c.1.1 c.1.2 + 1)).sum := by
  let s := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter
    (fun d => T.toAuxiliaryObject.1 d ≤ T.toAuxiliaryObject.1 c)
  let u := (Finset.univ : Finset (RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu)).filter
    (fun d => T.1 d.1.1 d.1.2 < T.1 c.1.1 c.1.2 + 1)
  have hsubset : s ⊆ u := by
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hentry := RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_le_entry_of_auxiliary_le T d c hd.2
    omega
  have himage : s.image (fun d => T.toAuxiliaryObject.1 d) =
      Finset.Iic (T.toAuxiliaryObject.1 c) := by
    ext i
    constructor
    · intro hi
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_Iic.mpr (Finset.mem_filter.mp hd).2
    · intro hi
      obtain ⟨d, hd⟩ := T.toAuxiliaryObject.2.1.2 i
      apply Finset.mem_image.mpr
      refine ⟨d, ?_, hd⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hd ▸ Finset.mem_Iic.mp hi⟩
  have hscard : s.card = (T.toAuxiliaryObject.1 c).val + 1 := by
    calc
      s.card = (s.image (fun d => T.toAuxiliaryObject.1 d)).card :=
        (Finset.card_image_of_injective _ T.toAuxiliaryObject.2.1.1).symm
      _ = (Finset.Iic (T.toAuxiliaryObject.1 c)).card := congrArg Finset.card himage
      _ = (T.toAuxiliaryObject.1 c).val + 1 := Fin.card_Iic _
  have hcard := Finset.card_le_card hsubset
  rw [hscard, show u.card =
      ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take (T.1 c.1.1 c.1.2 + 1)).sum by
        exact KostkaTableau.card_cells_entry_lt T _] at hcard
  omega



/-- An entry of the partition-indexed object equals the displayed value obtained from the sorted parts. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (T.toAuxiliaryObject.1 c).val =
      T.1 c.1.1 c.1.2 := by
  let k := T.1 c.1.1 c.1.2
  have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = n := by
    have hsort : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  have hj : (T.toAuxiliaryObject.1 c).val < (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum := by
    rw [hsum]
    exact (T.toAuxiliaryObject.1 c).isLt
  have hbelowNext : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (T.toAuxiliaryObject.1 c).val < k + 1 :=
    (RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) _ _ hj).mpr
      (KostkaTableau.standardization_lt_nextPrefix T c)
  have hnotBelow : ¬RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (T.toAuxiliaryObject.1 c).val < k := by
    rw [RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) _ _ hj]
    exact Nat.not_lt_of_ge (KostkaTableau.prefix_le_standardization T c)
  omega

private theorem card_positions_rowOfPos_lt {n : ℕ} (mu : Nat.Partition n) (k : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun i => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) i.val < k)).card =
      ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take k).sum := by
  have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = n := by
    have hsort : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  have hfilter : (Finset.univ : Finset (Fin n)).filter
      (fun i => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) i.val < k) =
      Finset.univ.filter (fun i : Fin n => i.val < ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take k).sum) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) i.val k (by rw [hsum]; exact i.isLt)
  rw [hfilter]
  apply RepresentationTheory.SymmetricGroup.PartitionDominance.Fin.card_filter_val_lt
  have hle : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take k).sum ≤ (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum :=
    List.Sublist.sum_le_sum (List.take_sublist k (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu)) (fun _ _ => Nat.zero_le _)
  omega

private theorem take_succ_sum (l : List ℕ) (k : ℕ) :
    (l.take (k + 1)).sum = (l.take k).sum + l.getD k 0 := by
  rw [List.take_add_one, List.sum_append]
  cases h : l[k]? <;> simp [List.getD_eq_getElem?_getD, h]


/-- The number of finite indices with the displayed value equals the corresponding sorted part, with default value zero. -/
theorem card_filter_auxiliary_nat_value_eq_getD {n : ℕ} (mu : Nat.Partition n) (k : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun i => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) i.val = k)).card =
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).getD k 0 := by
  let below := (Finset.univ : Finset (Fin n)).filter
    (fun i => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) i.val < k)
  let fiber := (Finset.univ : Finset (Fin n)).filter
    (fun i => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) i.val = k)
  let belowNext := (Finset.univ : Finset (Fin n)).filter
    (fun i => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) i.val < k + 1)
  have hdisjoint : Disjoint below fiber := by
    rw [Finset.disjoint_left]
    intro i hi hEq
    simp only [below, fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hi hEq
    omega
  have hunion : below ∪ fiber = belowNext := by
    ext i
    simp only [below, fiber, belowNext, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  have hcard : below.card + fiber.card = belowNext.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  rw [show below.card = ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take k).sum by
      exact card_positions_rowOfPos_lt mu k,
    show belowNext.card = ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).take (k + 1)).sum by
      exact card_positions_rowOfPos_lt mu (k + 1), take_succ_sum] at hcard
  change fiber.card = _
  exact Nat.add_left_cancel hcard

private theorem rowOfPos_mono_valid (parts : List ℕ) (a b : ℕ)
    (ha : a < parts.sum) (hb : b < parts.sum) (hab : a ≤ b) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts a ≤ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts b := by
  by_contra hnot
  have hlt : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts b < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts a := Nat.lt_of_not_ge hnot
  let k := RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts b + 1
  have hbPrefix : b < (parts.take k).sum :=
    (RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take parts b k hb).mp (by simp [k])
  have haPrefix : a < (parts.take k).sum := hab.trans_lt hbPrefix
  have haRow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow parts a < k :=
    (RepresentationTheory.SymmetricGroup.PartitionDominance.rowIndex_lt_iff_lt_sum_take parts a k ha).mpr haPrefix
  omega

private def partitionCellOfMem {n : ℕ} {nu : Nat.Partition n}
    (c : ℕ × ℕ) (hc : c ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu)) : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu :=
  ⟨c, (mem_partitionDiagram_iff_cell_condition c).mp hc⟩



/-- An auxiliary natural-number function associated with a partition and a partition-indexed object. -/
noncomputable def _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.auxiliaryNatFunction {n : ℕ}
    {nu : Nat.Partition n} (mu : Nat.Partition n) (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    (i j : ℕ) : ℕ :=
  if h : (i, j) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) then
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (S.1 (partitionCellOfMem (i, j) h)).val
  else 0

/-- At a cell of the displayed diagram, the auxiliary natural-number function equals the indicated sorted-part value. -/
@[simp] theorem _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.auxiliaryNatFunction_eq {n : ℕ}
    {nu : Nat.Partition n} (mu : Nat.Partition n) (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    {i j : ℕ} (h : (i, j) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu)) :
    S.auxiliaryNatFunction mu i j =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (S.1 (partitionCellOfMem (i, j) h)).val := by
  simp only [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.auxiliaryNatFunction, dif_pos h]



/-- An auxiliary predicate on a partition and a partition-indexed object. -/
def _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.AuxiliaryProperty {n : ℕ}
    {nu : Nat.Partition n} (mu : Nat.Partition n) (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu) : Prop :=
  ∀ c₁ c₂ : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu, c₁.1.2 = c₂.1.2 → c₁.1.1 < c₂.1.1 →
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (S.1 c₁).val < RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (S.1 c₂).val



/-- Builds an object of the displayed auxiliary family from an object satisfying the auxiliary predicate. -/
noncomputable def _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.toAuxiliaryFamily
    {n : ℕ} {nu mu : Nat.Partition n} (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    (hstrict : S.AuxiliaryProperty mu) : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu := by
  let entry := S.auxiliaryNatFunction mu
  have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = n := by
    have hsort : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  let T : SemistandardYoungTableau (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu) := {
    entry := entry
    row_weak' := by
      intro i j₁ j₂ hj hcell₂
      have hcell₁ := (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu).up_left_mem le_rfl (Nat.le_of_lt hj) hcell₂
      rw [show entry i j₁ = S.auxiliaryNatFunction mu i j₁ from rfl,
        S.auxiliaryNatFunction_eq mu hcell₁,
        show entry i j₂ = S.auxiliaryNatFunction mu i j₂ from rfl,
        S.auxiliaryNatFunction_eq mu hcell₂]
      apply rowOfPos_mono_valid (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu)
      · rw [hsum]; exact (S.1 _).isLt
      · rw [hsum]; exact (S.1 _).isLt
      · exact le_of_lt (S.2.2.1 _ _ rfl hj)
    col_strict' := by
      intro i₁ i₂ j hi hcell₂
      have hcell₁ := (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu).up_left_mem (Nat.le_of_lt hi) le_rfl hcell₂
      rw [show entry i₁ j = S.auxiliaryNatFunction mu i₁ j from rfl,
        S.auxiliaryNatFunction_eq mu hcell₁,
        show entry i₂ j = S.auxiliaryNatFunction mu i₂ j from rfl,
        S.auxiliaryNatFunction_eq mu hcell₂]
      exact hstrict _ _ rfl hi
    zeros' := by
      intro i j hcell
      simp only [entry, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.auxiliaryNatFunction, dif_neg hcell]
  }
  refine ⟨T, ?_⟩
  intro k
  let source := (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu).cells.filter (fun c => T c.1 c.2 = k)
  let target := (Finset.univ : Finset (Fin n)).filter
    (fun x => RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) x.val = k)
  calc
    source.card = target.card := by
      apply Finset.card_bij
        (fun c hc => S.1 (partitionCellOfMem c (Finset.mem_filter.mp hc).1))
      · intro c hc
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hc' := (Finset.mem_filter.mp hc).1
        have hvalue := (Finset.mem_filter.mp hc).2
        change entry c.1 c.2 = k at hvalue
        rw [show entry c.1 c.2 = S.auxiliaryNatFunction mu c.1 c.2 from rfl,
          S.auxiliaryNatFunction_eq mu hc'] at hvalue
        exact hvalue
      · intro c₁ hc₁ c₂ hc₂ heq
        have hcells := S.2.1.1 heq
        exact congrArg Subtype.val hcells
      · intro x hx
        obtain ⟨c, hc⟩ := S.2.1.2 x
        refine ⟨c.1, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨by simpa only [YoungDiagram.mem_cells] using
            (cell_mem_partitionDiagram c), ?_⟩
          change entry c.1.1 c.1.2 = k
          rw [show entry c.1.1 c.1.2 = S.auxiliaryNatFunction mu c.1.1 c.1.2 from rfl,
            S.auxiliaryNatFunction_eq mu (cell_mem_partitionDiagram c)]
          have hcellEq : partitionCellOfMem c.1 (cell_mem_partitionDiagram c) = c :=
            Subtype.ext rfl
          rw [hcellEq, hc]
          have hx' := (Finset.mem_filter.mp hx).2
          exact hx'
        · simpa only [partitionCellOfMem] using hc
    _ = (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).getD k 0 := card_filter_auxiliary_nat_value_eq_getD mu k

/-- Each entry of the constructed auxiliary object is the displayed sorted-part value at the associated index. -/
@[simp] theorem _root_.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.toAuxiliaryFamily_entry
    {n : ℕ} {nu mu : Nat.Partition n} (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    (hstrict : S.AuxiliaryProperty mu) (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    (S.toAuxiliaryFamily hstrict).1.1 c.1.1 c.1.2 =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (S.1 c).val := by
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.toAuxiliaryFamily]
  change S.auxiliaryNatFunction mu c.1.1 c.1.2 = _
  rw [S.auxiliaryNatFunction_eq mu (cell_mem_partitionDiagram c)]
  congr 1



/-- Evaluating the displayed auxiliary map at the indicated value agrees with the inverse equivalence. -/
theorem auxiliary_map_apply_eq_equiv_symm {n : ℕ} {nu : Nat.Partition n}
    (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu) (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S (S.1 c) = (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c := by
  let e : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu ≃ Fin n := Equiv.ofBijective S.1 S.2.1
  change (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm (e.symm (e c)) = _
  rw [e.symm_apply_apply]

private theorem sytPerm_inv_apply_canonical {n : ℕ} {nu : Nat.Partition n}
    (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu) (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹ ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c) = S.1 c := by
  rw [← auxiliary_map_apply_eq_equiv_symm S c]
  exact (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S).symm_apply_apply (S.1 c)

private theorem contentCollapse_relabel_mem_rowSubgroup {n : ℕ}
    {nu mu : Nat.Partition n} (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    (hstrict : S.AuxiliaryProperty mu) :
    (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu
        (S.toAuxiliaryFamily hstrict).toAuxiliaryObject)⁻¹ *
        RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu := by
  let U := S.toAuxiliaryFamily hstrict
  let V := U.toAuxiliaryObject
  let p := (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu V)⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S
  change p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu
  intro x
  let eS : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu ≃ Fin n := Equiv.ofBijective S.1 S.2.1
  let c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu := eS.symm x
  have hS : S.1 c = x := eS.apply_symm_apply x
  change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (p x).val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) x.val
  simp only [p, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [← hS, auxiliary_map_apply_eq_equiv_symm S c,
    sytPerm_inv_apply_canonical V c]
  change RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (U.toAuxiliaryObject.1 c).val = _
  rw [RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value U c]
  change (S.toAuxiliaryFamily hstrict).1.1 c.1.1 c.1.2 = _
  rw [S.toAuxiliaryFamily_entry hstrict c, hS]


/-- Maps each object of an auxiliary partition-indexed family into the displayed submodule. -/
noncomputable def auxiliaryFamilyMap (n : ℕ)
    (mu nu : Nat.Partition n) (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliarySubmodule n mu nu :=
  RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryGenerator n mu nu T.toAuxiliaryObject



/-- When the auxiliary predicate holds, the two displayed submodule-valued maps agree after the indicated conversion. -/
theorem auxiliary_maps_eq_of_property
    (n : ℕ) (mu nu : Nat.Partition n) (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    (hstrict : S.AuxiliaryProperty mu) :
    RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryGenerator n mu nu S =
      auxiliaryFamilyMap n mu nu
        (S.toAuxiliaryFamily hstrict) := by
  let U := S.toAuxiliaryFamily hstrict
  let V := U.toAuxiliaryObject
  let p := (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu V)⁻¹ * RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S
  have hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu :=
    contentCollapse_relabel_mem_rowSubgroup S hstrict
  have hpEq : p * (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹ = (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu V)⁻¹ := by
    simp only [p]
    group
  have hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
        MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹ =
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu V)⁻¹ := by
    calc
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹ =
          (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ p) *
            MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹ := by
              rw [RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.mul_perm_eq_self_of_mem p hp]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
          (MonoidAlgebra.of ℂ _ p * MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹) := by
            rw [mul_assoc]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _
          (p * (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹) := by
            congr 1
            exact ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))).map_mul
              p (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹).symm
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu V)⁻¹ := by
        rw [hpEq]
  apply Subtype.ext
  change (RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryEndomorphism n mu nu (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype S) :
      RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) = RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryEndomorphism n mu nu (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype V)
  apply Subtype.ext
  change (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
        ((Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n nu)) : ℂ)⁻¹ •
          MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S)⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu)) =
    (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
        ((Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n nu)) : ℂ)⁻¹ •
          MonoidAlgebra.of ℂ _ (RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu V)⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu))
  simp only [Algebra.mul_smul_comm, smul_mul_assoc]
  rw [← mul_assoc, ← mul_assoc, hrow]

private theorem swap_mem_rowSubgroup_of_same_row {n : ℕ} {mu : Nat.Partition n}
    {a b : Fin n}
    (hrow : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) a.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) b.val) :
    Equiv.swap a b ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu := by
  intro x
  simp only [Equiv.swap_apply_def]
  split_ifs with ha hb
  · subst ha; exact hrow.symm
  · subst hb; exact hrow
  · rfl

private theorem swap_mem_columnSubgroup_of_same_col {n : ℕ} {nu : Nat.Partition n}
    {a b : Fin n}
    (hcol : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) a.val = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) b.val) :
    Equiv.swap a b ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n nu := by
  intro x
  simp only [Equiv.swap_apply_def]
  split_ifs with ha hb
  · subst ha; exact hcol.symm
  · subst hb; exact hcol
  · rfl

private theorem colOfPos_canonical_symm {n : ℕ} {nu : Nat.Partition n}
    (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexColumn (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c).val = c.1.2 := by
  have h := (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).apply_symm_apply c
  have hval := congrArg (fun d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu => d.1.2) h
  simpa only [RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex, RepresentationTheory.Combinatorics.PartitionPermutation.partitionIndexOfFin, Equiv.ofBijective_apply] using hval


/-- The displayed natural-number value at the inverse image of an index equals its first coordinate. -/
theorem auxiliary_nat_value_equiv_symm_eq_fst {n : ℕ} {nu : Nat.Partition n}
    (c : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList nu) ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c).val = c.1.1 := by
  have h := (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).apply_symm_apply c
  have hval := congrArg (fun d : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu => d.1.1) h
  simpa only [RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex, RepresentationTheory.Combinatorics.PartitionPermutation.partitionIndexOfFin, Equiv.ofBijective_apply] using hval

private theorem of_col_mul_youngSymmetrizer {n : ℕ} {nu : Nat.Partition n}
    (q : Equiv.Perm (Fin n)) (hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n nu) :
    MonoidAlgebra.of ℂ _ q * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu := by
  change MonoidAlgebra.of ℂ _ q *
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n nu * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n nu) =
    _ • (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementA n nu * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n nu)
  rw [← mul_assoc, RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.perm_mul_eq_sign_smul_of_mem q hq,
    Algebra.smul_mul_assoc]

private theorem contentCollapse_not_columnStrict_data {n : ℕ}
    {nu mu : Nat.Partition n} (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    (hnot : ¬S.AuxiliaryProperty mu) :
    ∃ c₁ c₂ : RepresentationTheory.Combinatorics.PartitionPermutation.PartitionIndex n nu,
      c₁.1.2 = c₂.1.2 ∧ c₁.1.1 < c₂.1.1 ∧
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (S.1 c₁).val =
        RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.flatIndexRow (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) (S.1 c₂).val := by
  rw [RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource.AuxiliaryProperty] at hnot
  push Not at hnot
  obtain ⟨c₁, c₂, hcol, hrow, hnotlt⟩ := hnot
  refine ⟨c₁, c₂, hcol, hrow, ?_⟩
  have hsum : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = n := by
    have hsort : ((RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu) : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu).sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  have hlabel : S.1 c₁ < S.1 c₂ := S.2.2.2 c₁ c₂ hcol hrow
  have hle := rowOfPos_mono_valid (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList mu)
    (S.1 c₁).val (S.1 c₂).val
    (by rw [hsum]; exact (S.1 c₁).isLt)
    (by rw [hsum]; exact (S.1 c₂).isLt) (le_of_lt hlabel)
  exact le_antisymm hle hnotlt



/-- The displayed submodule-valued map is zero when the auxiliary predicate fails. -/
theorem auxiliary_map_eq_zero_of_not_property
    (n : ℕ) (mu nu : Nat.Partition n) (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu)
    (hnot : ¬S.AuxiliaryProperty mu) :
    RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryGenerator n mu nu S = 0 := by
  obtain ⟨c₁, c₂, hcol, hrow, hblock⟩ :=
    contentCollapse_not_columnStrict_data S hnot
  let σ := RepresentationTheory.Combinatorics.PartitionPermutation.associatedPermutation n nu S
  let a := S.1 c₁
  let b := S.1 c₂
  let p := Equiv.swap a b
  let q := σ * p * σ⁻¹
  have hab : a ≠ b := ne_of_lt (S.2.2.2 c₁ c₂ hcol hrow)
  have hp : p ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu :=
    swap_mem_rowSubgroup_of_same_row hblock
  have hcell : c₁ ≠ c₂ := by
    intro heq
    rw [heq] at hrow
    omega
  have hpos : (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c₁ ≠
      (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c₂ := by
    intro heq
    exact hcell ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm.injective heq)
  have hqEq : q = Equiv.swap ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c₁)
      ((RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c₂) := by
    calc
      q = Equiv.swap (σ a) (σ b) := by
        have h := Equiv.trans_swap_trans_symm a b σ.symm
        change σ * Equiv.swap a b * σ⁻¹ = Equiv.swap (σ a) (σ b) at h
        exact h
      _ = _ := by
        rw [show σ a = (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c₁ by
              exact auxiliary_map_apply_eq_equiv_symm S c₁,
          show σ b = (RepresentationTheory.Combinatorics.PartitionPermutation.finEquivPartitionIndex n nu).symm c₂ by
              exact auxiliary_map_apply_eq_equiv_symm S c₂]
  have hq : q ∈ RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupA n nu := by
    rw [hqEq]
    apply swap_mem_columnSubgroup_of_same_col
    rw [colOfPos_canonical_symm c₁, colOfPos_canonical_symm c₂]
    exact hcol
  have hsign : Equiv.Perm.sign q = -1 := by
    rw [hqEq, Equiv.Perm.sign_swap hpos]
  have hqAction : MonoidAlgebra.of ℂ _ q * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu =
      (-1 : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu := by
    rw [of_col_mul_youngSymmetrizer q hq, hsign]
    norm_num
  have hpEq : p * σ⁻¹ = σ⁻¹ * q := by
    simp only [q]
    group
  let A : RepresentationTheory.PartitionAuxiliary.natIndexedType n :=
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ σ⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu
  have hAneg : A = -A := by
    calc
      A = (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ p) *
          MonoidAlgebra.of ℂ _ σ⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu := by
            rw [RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.mul_perm_eq_self_of_mem p hp]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
          (MonoidAlgebra.of ℂ _ p * MonoidAlgebra.of ℂ _ σ⁻¹) *
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu := by simp only [mul_assoc]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ (p * σ⁻¹) *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu := by
            congr 2
            exact ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))).map_mul p σ⁻¹).symm
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ (σ⁻¹ * q) *
          RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu := by rw [hpEq]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
          (MonoidAlgebra.of ℂ _ σ⁻¹ * MonoidAlgebra.of ℂ _ q) *
            RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu := by
              congr 2
              exact (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))).map_mul σ⁻¹ q
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ σ⁻¹ *
          (MonoidAlgebra.of ℂ _ q * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu) := by
            simp only [mul_assoc]
      _ = RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu * MonoidAlgebra.of ℂ _ σ⁻¹ *
          ((-1 : ℂ) • RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu) := by rw [hqAction]
      _ = -A := by
        simp only [neg_smul, one_smul, A]
        rw [mul_neg]
  have hA : A = 0 := by
    have htwo : (2 : ℂ) • A = 0 := by
      calc
        (2 : ℂ) • A = A + A := two_smul ℂ A
        _ = -A + A := congrArg (fun z => z + A) hAneg
        _ = 0 := neg_add_cancel A
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  apply Subtype.ext
  change (RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryEndomorphism n mu nu (RepresentationTheory.Auxiliary.MembershipSubtypes.to_membershipSubtype S) :
      RepresentationTheory.PartitionAuxiliary.partitionSubmodule n nu) = 0
  apply Subtype.ext
  change (Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n mu)) : ℂ)⁻¹ •
      (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementB n mu *
        ((Nat.card (↥(RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionPermutationSubgroupB n nu)) : ℂ)⁻¹ •
          MonoidAlgebra.of ℂ _ σ⁻¹ * RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementC n nu)) = 0
  simp only [Algebra.mul_smul_comm, smul_mul_assoc, ← mul_assoc, A, hA, smul_zero]



/-- Every value of the displayed auxiliary map belongs to the span of the auxiliary family map's range. -/
theorem auxiliary_map_mem_span_range
    (n : ℕ) (mu nu : Nat.Partition n) (S : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu) :
    RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliaryGenerator n mu nu S ∈
      Submodule.span ℂ (Set.range (auxiliaryFamilyMap n mu nu)) := by
  by_cases hstrict : S.AuxiliaryProperty mu
  · rw [auxiliary_maps_eq_of_property
      n mu nu S hstrict]
    apply Submodule.subset_span
    exact ⟨S.toAuxiliaryFamily hstrict, rfl⟩
  · rw [auxiliary_map_eq_zero_of_not_property
      n mu nu S hstrict]
    exact Submodule.zero_mem _


/-- The range of the auxiliary family map spans the entire displayed submodule. -/
theorem span_range_auxiliaryFamilyMap_eq_top (n : ℕ)
    (mu nu : Nat.Partition n) :
    Submodule.span ℂ (Set.range (auxiliaryFamilyMap n mu nu)) = ⊤ := by
  rw [eq_top_iff, ← RepresentationTheory.AuxiliaryPartitionSubmodules.auxiliary_span_range_eq_top n mu nu]
  apply Submodule.span_le.mpr
  rintro _ ⟨S, rfl⟩
  exact auxiliary_map_mem_span_range n mu nu S


/-- The converted auxiliary object satisfies the displayed predicate for the target partition. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.toAuxiliaryObject_property {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    T.toAuxiliaryObject.AuxiliaryProperty mu := by
  intro c₁ c₂ hcol hrow
  rw [RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value T c₁,
    RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value T c₂]
  simpa [hcol] using T.1.col_strict hrow (cell_mem_partitionDiagram c₂)



/-- The displayed round trip on a partition-indexed object recovers that object. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_roundTrip {n : ℕ}
    {nu mu : Nat.Partition n} (T : RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu) :
    T.toAuxiliaryObject.toAuxiliaryFamily
      T.toAuxiliaryObject_property = T := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hcell : (i, j) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu)
  · let c := partitionCellOfMem (i, j) hcell
    change (T.toAuxiliaryObject.toAuxiliaryFamily
      T.toAuxiliaryObject_property).1.1 c.1.1 c.1.2 =
        T.1 c.1.1 c.1.2
    rw [T.toAuxiliaryObject.toAuxiliaryFamily_entry
      T.toAuxiliaryObject_property c,
      RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value T c]
  · rw [(T.toAuxiliaryObject.toAuxiliaryFamily
      T.toAuxiliaryObject_property).1.zeros hcell, T.1.zeros hcell]



/-- The conversion to the displayed auxiliary type is injective. -/
theorem _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.toAuxiliaryObject_injective {n : ℕ}
    {nu mu : Nat.Partition n} :
    Function.Injective (RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.toAuxiliaryObject :
      RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily n nu mu → RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n nu) := by
  intro T U h
  have hfun : T.toAuxiliaryObject.1 = U.toAuxiliaryObject.1 :=
    congrArg Subtype.val h
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hcell : (i, j) ∈ (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition nu)
  · let c := partitionCellOfMem (i, j) hcell
    change T.1 c.1.1 c.1.2 = U.1 c.1.1 c.1.2
    rw [← RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value T c,
      ← RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.entry_eq_auxiliary_nat_value U c, hfun]
  · rw [T.1.zeros hcell, U.1.zeros hcell]

end

end RepresentationTheory.AuxiliaryPartitionIndexMaps

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.Auxiliary.statement005406 := _root_.RepresentationTheory.AuxiliaryPartitionCardinality.auxiliaryFamily.auxiliary_roundTrip

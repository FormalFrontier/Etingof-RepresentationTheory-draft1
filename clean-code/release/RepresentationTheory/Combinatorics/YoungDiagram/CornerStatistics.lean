/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.YoungDiagram.PartitionConstructions
import RepresentationTheory.Partition.YoungDiagram

namespace RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics

/-- An auxiliary natural-number statistic of a Young diagram at two indices. -/
def YoungDiagram.auxiliaryCellStatistic (μ : YoungDiagram) (i j : ℕ) : ℕ :=
  μ.rowLen i + μ.colLen j - i - j - 1


/-- An auxiliary natural-number statistic of a Young diagram. -/
noncomputable def YoungDiagram.auxiliaryDiagramStatistic (μ : YoungDiagram) : ℕ :=
  μ.cells.prod (fun c => μ.auxiliaryCellStatistic c.1 c.2)




/-- The auxiliary cell statistic is positive at every cell of a Young diagram. -/
lemma YoungDiagram.auxiliaryCellStatistic_pos (μ : YoungDiagram) (i j : ℕ) (h : (i, j) ∈ μ.cells) :
    0 < μ.auxiliaryCellStatistic i j := by
  simp [YoungDiagram.auxiliaryCellStatistic]
  rw [YoungDiagram.mem_cells] at h
  have hi := YoungDiagram.mem_iff_lt_colLen.mp h
  have hj := YoungDiagram.mem_iff_lt_rowLen.mp h
  omega


/-- The auxiliary natural-number statistic of a Young diagram is positive. -/
lemma YoungDiagram.auxiliaryDiagramStatistic_pos (μ : YoungDiagram) :
    0 < μ.auxiliaryDiagramStatistic := by
  unfold YoungDiagram.auxiliaryDiagramStatistic
  apply Finset.prod_pos
  intro c hc
  exact YoungDiagram.auxiliaryCellStatistic_pos μ c.1 c.2 hc





/-- An auxiliary predicate on a Young diagram and two natural-number indices. -/
def YoungDiagram.auxiliaryCellPredicate (μ : YoungDiagram) (i j : ℕ) : Prop :=
  (i, j) ∈ μ.cells ∧ (i + 1, j) ∉ μ.cells ∧ (i, j + 1) ∉ μ.cells


/-- An auxiliary finite set of pairs associated with a Young diagram. -/
noncomputable def YoungDiagram.auxiliaryCellPairFinset (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => (c.1 + 1, c.2) ∉ μ.cells ∧ (c.1, c.2 + 1) ∉ μ.cells

/-- Membership in the auxiliary finite set of cell pairs is equivalent to the corresponding auxiliary corner predicate. -/
theorem YoungDiagram.mem_auxiliaryCellPairFinset_iff {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ μ.auxiliaryCellPairFinset ↔ μ.auxiliaryCellPredicate c.1 c.2 := by
  simp [auxiliaryCellPairFinset, auxiliaryCellPredicate, Finset.mem_filter]


/-- A Young diagram with at least one cell has a nonempty auxiliary finite set of pairs. -/
theorem YoungDiagram.auxiliaryCellPairFinset_nonempty (μ : YoungDiagram) (h : μ.cells.Nonempty) :
    μ.auxiliaryCellPairFinset.Nonempty := by

  obtain ⟨c, hc_mem, hc_max⟩ := Finset.exists_max_image μ.cells
    (fun c : ℕ × ℕ => c.1 + c.2) h
  refine ⟨c, mem_auxiliaryCellPairFinset_iff.mpr ⟨hc_mem, ?_, ?_⟩⟩
  · intro h1
    have := hc_max _ h1
    simp at this
  · intro h1
    have := hc_max _ h1
    simp at this






/-- An auxiliary Young-diagram transformation determined by two indices satisfying the auxiliary corner predicate. -/
noncomputable def YoungDiagram.auxiliaryCornerTransform (μ : YoungDiagram) (i j : ℕ)
    (hc : μ.auxiliaryCellPredicate i j) : YoungDiagram where
  cells := μ.cells.erase (i, j)
  isLowerSet := by

    intro a b hle hmem
    simp only [Finset.mem_coe, Finset.mem_erase] at hmem ⊢

    have hle' := Prod.mk_le_mk.mp hle
    have ha_μ : a ∈ μ := hmem.2
    have hb_μ : b ∈ μ := μ.up_left_mem hle'.1 hle'.2 ha_μ
    refine ⟨?_, hb_μ⟩
    intro heq

    rw [heq] at hle'
    obtain ⟨_, hbelow, hright⟩ := hc
    have hne := hmem.1
    rcases Nat.lt_or_eq_of_le hle'.1 with h | h
    · exact hbelow (μ.up_left_mem (Nat.succ_le_of_lt h) hle'.2 ha_μ)
    · rcases Nat.lt_or_eq_of_le hle'.2 with h' | h'
      · exact hright (μ.up_left_mem (le_of_eq h) (Nat.succ_le_of_lt h') ha_μ)
      · exact absurd (show a = (i, j) from Prod.ext h.symm h'.symm) hne

/-- The auxiliary corner transformation decreases the number of cells by one. -/
theorem YoungDiagram.card_auxiliaryCornerTransform_cells (μ : YoungDiagram) (i j : ℕ)
    (hc : μ.auxiliaryCellPredicate i j) :
    (μ.auxiliaryCornerTransform i j hc).cells.card = μ.cells.card - 1 := by
  simp only [auxiliaryCornerTransform]
  exact Finset.card_erase_of_mem hc.1




private theorem cellsOfRowLens_card : ∀ w : List ℕ,
    (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  intro w
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a as ih =>
    rw [YoungDiagram.cellsOfRowLens, List.sum_cons]
    rw [Finset.card_union_of_disjoint]
    · simp [ih]
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hx
      rw [Finset.mem_map] at hx'
      obtain ⟨y, _, hy⟩ := hx'
      have : x.1 = 0 := hx.1
      have : x.1 = y.1 + 1 := by
        have := congr_arg Prod.fst hy
        simp [Function.Embedding.prodMap] at this
        omega
      omega


/-- The Young diagram of a partition has as many cells as the partition's indexed size. -/
theorem Partition.card_toYoungDiagram_cells {n : ℕ} (la : Nat.Partition n) :
    la.auxiliaryYoungDiagramOfPartition.cells.card = n := by
  unfold RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition YoungDiagram.ofRowLens
  rw [cellsOfRowLens_card]
  have : (la.parts.sort (· ≥ ·) : Multiset ℕ).sum = la.parts.sum :=
    congrArg Multiset.sum (Multiset.sort_eq la.parts (· ≥ ·))
  rw [Multiset.sum_coe] at this
  rw [this, la.parts_sum]




private lemma YoungDiagram.rowLens_sum (μ : YoungDiagram) :
    μ.rowLens.sum = μ.cells.card := by
  have h := cellsOfRowLens_card μ.rowLens
  have : YoungDiagram.cellsOfRowLens μ.rowLens =
    (YoungDiagram.ofRowLens μ.rowLens μ.rowLens_sorted).cells := rfl
  rw [this] at h
  rw [show YoungDiagram.ofRowLens μ.rowLens μ.rowLens_sorted = μ from
    YoungDiagram.ofRowLens_to_rowLens_eq_self] at h
  linarith








/-- An auxiliary partition of the preceding size determined by a partition and one of its outer corners. -/
noncomputable def Partition.auxiliaryAtOuterCorner {n : ℕ} (la : Nat.Partition (n + 1))
    (c : ℕ × ℕ) (hc : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPredicate c.1 c.2) : Nat.Partition n where
  parts := ((la.auxiliaryYoungDiagramOfPartition.auxiliaryCornerTransform c.1 c.2 hc).rowLens : List ℕ)
  parts_pos := fun {i} hi => YoungDiagram.pos_of_mem_rowLens _ _ hi
  parts_sum := by
    rw [Multiset.sum_coe]
    rw [YoungDiagram.rowLens_sum]
    rw [YoungDiagram.card_auxiliaryCornerTransform_cells]
    rw [Partition.card_toYoungDiagram_cells]
    omega



/-- The Young diagram of the auxiliary partition at an outer corner is obtained by removing that corner from the original Young diagram. -/
theorem Partition.toYoungDiagram_auxiliaryAtOuterCorner {n : ℕ} (la : Nat.Partition (n + 1))
    (c : ℕ × ℕ) (hc : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPredicate c.1 c.2) :
    (la.auxiliaryAtOuterCorner c hc).auxiliaryYoungDiagramOfPartition =
      la.auxiliaryYoungDiagramOfPartition.auxiliaryCornerTransform c.1 c.2 hc := by
  set μ' := la.auxiliaryYoungDiagramOfPartition.auxiliaryCornerTransform c.1 c.2 hc
  unfold RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition Partition.auxiliaryAtOuterCorner
  convert YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ') using 2

  change (μ'.rowLens : Multiset ℕ).sort (· ≥ ·) = μ'.rowLens
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (List.sortedGE_iff_pairwise.mp μ'.rowLens_sorted)


noncomputable section

private lemma partition_zero_sortedParts (la : Nat.Partition 0) : la.auxiliaryPartitionNatList = [] := by
  unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList
  rw [Nat.Partition.partition_zero_parts la]
  simp

/-- The auxiliary factorial identity holds for partitions of zero. -/
theorem Partition.auxiliaryFactorialIdentity_zero (la : Nat.Partition 0) :
    Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource 0 la) *
      la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic = Nat.factorial 0 := by
  have h_empty : la.auxiliaryYoungDiagramOfPartition.cells = ∅ :=
    Finset.card_eq_zero.mp la.card_toYoungDiagram_cells
  have h_hook : la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic = 1 := by
    simp [YoungDiagram.auxiliaryDiagramStatistic, h_empty]
  have h_sorted := partition_zero_sortedParts la
  haveI : Unique (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource 0 la) := by
    unfold RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource
    rw [h_sorted]
    simp only [List.length_nil, List.getD_nil]
    haveI : IsEmpty { c : ℕ × ℕ // c.1 < 0 ∧ c.2 < 0 } :=
      ⟨fun c => absurd c.2.1 (by omega)⟩
    exact {
      toInhabited := ⟨⟨isEmptyElim, ⟨fun a => isEmptyElim a, fun b => Fin.elim0 b⟩,
               fun c₁ _ _ _ => isEmptyElim c₁, fun c₁ _ _ _ => isEmptyElim c₁⟩⟩
      uniq := fun ⟨f, _⟩ => by congr 1; exact funext fun c => isEmptyElim c
    }
  simp [h_hook, Nat.factorial]




private lemma sytCell_iff_mem_toYoungDiagram {n : ℕ} (la : Nat.Partition n)
    (c : ℕ × ℕ) :
    (c.1 < la.auxiliaryPartitionNatList.length ∧ c.2 < la.auxiliaryPartitionNatList.getD c.1 0) ↔
    c ∈ la.auxiliaryYoungDiagramOfPartition.cells := by
  simp only [RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition, RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionNatList,
    YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have heq := List.getD_eq_getElem _ 0 h1
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have heq := List.getD_eq_getElem _ 0 h1
    omega


private noncomputable def sytCellEquiv {n : ℕ} (la : Nat.Partition n) :
    { c : ℕ × ℕ // c.1 < la.auxiliaryPartitionNatList.length ∧ c.2 < la.auxiliaryPartitionNatList.getD c.1 0 } ≃
    { c : ℕ × ℕ // c ∈ la.auxiliaryYoungDiagramOfPartition.cells } where
  toFun := fun ⟨c, h⟩ => ⟨c, (sytCell_iff_mem_toYoungDiagram la c).mp h⟩
  invFun := fun ⟨c, h⟩ => ⟨c, (sytCell_iff_mem_toYoungDiagram la c).mpr h⟩
  left_inv := fun ⟨_, _⟩ => by simp
  right_inv := fun ⟨_, _⟩ => by simp



private lemma syt_maxCell_isOuterCorner {n : ℕ} {la : Nat.Partition (n + 1)}
    (f : { c : ℕ × ℕ // c.1 < la.auxiliaryPartitionNatList.length ∧
      c.2 < la.auxiliaryPartitionNatList.getD c.1 0 } → Fin (n + 1))
    (_hbij : Function.Bijective f)
    (hrow : ∀ c₁ c₂, c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → f c₁ < f c₂)
    (hcol : ∀ c₁ c₂, c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → f c₁ < f c₂)
    (c₀ : { c : ℕ × ℕ // c.1 < la.auxiliaryPartitionNatList.length ∧
      c.2 < la.auxiliaryPartitionNatList.getD c.1 0 })
    (hc₀ : f c₀ = Fin.last n) :
    la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPredicate c₀.val.1 c₀.val.2 := by
  refine ⟨(sytCell_iff_mem_toYoungDiagram la c₀.val).mp c₀.property, ?_, ?_⟩
  ·
    intro hmem
    have hmem' := (sytCell_iff_mem_toYoungDiagram la (c₀.val.1 + 1, c₀.val.2)).mpr hmem
    have h := hcol c₀ ⟨(c₀.val.1 + 1, c₀.val.2), hmem'⟩ rfl
      (show c₀.val.1 < c₀.val.1 + 1 by omega)
    rw [hc₀] at h
    exact absurd h (not_lt.mpr (Fin.le_last _))
  ·
    intro hmem
    have hmem' := (sytCell_iff_mem_toYoungDiagram la (c₀.val.1, c₀.val.2 + 1)).mpr hmem
    have h := hrow c₀ ⟨(c₀.val.1, c₀.val.2 + 1), hmem'⟩ rfl
      (show c₀.val.2 < c₀.val.2 + 1 by omega)
    rw [hc₀] at h
    exact absurd h (not_lt.mpr (Fin.le_last _))


private lemma reducedCell_mem_original {n : ℕ} {la : Nat.Partition (n + 1)}
    {corner : ℕ × ℕ} {hcorner : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPredicate corner.1 corner.2}
    {x : ℕ × ℕ}
    (hx : x.1 < (la.auxiliaryAtOuterCorner corner hcorner).auxiliaryPartitionNatList.length ∧
      x.2 < (la.auxiliaryAtOuterCorner corner hcorner).auxiliaryPartitionNatList.getD x.1 0) :
    x.1 < la.auxiliaryPartitionNatList.length ∧ x.2 < la.auxiliaryPartitionNatList.getD x.1 0 := by
  have hmem := (sytCell_iff_mem_toYoungDiagram _ x).mp hx
  rw [Partition.toYoungDiagram_auxiliaryAtOuterCorner] at hmem

  have hmem' : x ∈ la.auxiliaryYoungDiagramOfPartition.cells :=
    (Finset.mem_erase.mp hmem).2
  exact (sytCell_iff_mem_toYoungDiagram la x).mpr hmem'


private lemma reducedCell_ne_corner {n : ℕ} {la : Nat.Partition (n + 1)}
    {corner : ℕ × ℕ} {hcorner : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPredicate corner.1 corner.2}
    {x : ℕ × ℕ}
    (hx : x.1 < (la.auxiliaryAtOuterCorner corner hcorner).auxiliaryPartitionNatList.length ∧
      x.2 < (la.auxiliaryAtOuterCorner corner hcorner).auxiliaryPartitionNatList.getD x.1 0) :
    x ≠ corner := by
  have hmem := (sytCell_iff_mem_toYoungDiagram _ x).mp hx
  rw [Partition.toYoungDiagram_auxiliaryAtOuterCorner] at hmem
  exact (Finset.mem_erase.mp hmem).1


private lemma originalCell_mem_reduced {n : ℕ} {la : Nat.Partition (n + 1)}
    {corner : ℕ × ℕ} {hcorner : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPredicate corner.1 corner.2}
    {x : ℕ × ℕ}
    (hx : x.1 < la.auxiliaryPartitionNatList.length ∧ x.2 < la.auxiliaryPartitionNatList.getD x.1 0)
    (hne : x ≠ corner) :
    x.1 < (la.auxiliaryAtOuterCorner corner hcorner).auxiliaryPartitionNatList.length ∧
      x.2 < (la.auxiliaryAtOuterCorner corner hcorner).auxiliaryPartitionNatList.getD x.1 0 := by
  have hmem := (sytCell_iff_mem_toYoungDiagram la x).mp hx
  have hmem' : x ∈ (la.auxiliaryAtOuterCorner corner hcorner).auxiliaryYoungDiagramOfPartition.cells := by
    rw [Partition.toYoungDiagram_auxiliaryAtOuterCorner]
    exact Finset.mem_erase.mpr ⟨hne, hmem⟩
  exact (sytCell_iff_mem_toYoungDiagram _ x).mpr hmem'



private noncomputable def sytBranchingToFun (n : ℕ) (la : Nat.Partition (n + 1))
    (t : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource (n + 1) la) :
    (c : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset) ×
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n (la.auxiliaryAtOuterCorner c.val
        (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property)) := by
  classical
  have hbij := t.property.1
  have hrow := t.property.2.1
  have hcol := t.property.2.2
  let c₀ := (hbij.surjective (Fin.last n)).choose
  have hc₀ : t.val c₀ = Fin.last n := (hbij.surjective (Fin.last n)).choose_spec
  have hoc := syt_maxCell_isOuterCorner t.val hbij hrow hcol c₀ hc₀
  let corner : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset :=
    ⟨c₀.val, YoungDiagram.mem_auxiliaryCellPairFinset_iff.mpr hoc⟩
  let la' := la.auxiliaryAtOuterCorner corner.val (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp corner.property)
  have hcorner_oc := YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp corner.property
  let g : { x : ℕ × ℕ // x.1 < la'.auxiliaryPartitionNatList.length ∧
      x.2 < la'.auxiliaryPartitionNatList.getD x.1 0 } → Fin n := fun c' =>
    let cell_la : { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
        x.2 < la.auxiliaryPartitionNatList.getD x.1 0 } :=
      ⟨c'.val, reducedCell_mem_original (hcorner := hcorner_oc) c'.property⟩
    let v := t.val cell_la
    have hne : c'.val ≠ c₀.val :=
      reducedCell_ne_corner (hcorner := hcorner_oc) c'.property
    have hv_ne : v ≠ Fin.last n := by
      intro heq
      have heq' : t.val cell_la = t.val c₀ := heq.trans hc₀.symm
      exact hne (congr_arg Subtype.val (hbij.injective heq'))
    ⟨v.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp v.isLt)
      (Fin.val_ne_of_ne hv_ne)⟩
  have g_bij : Function.Bijective g := by
    constructor
    · intro c₁ c₂ heq
      have hval := congr_arg Fin.val heq
      have h_eq := hbij.injective (Fin.ext hval)
      have h_val_eq : c₁.val = c₂.val :=
        congrArg (fun (x : { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
          x.2 < la.auxiliaryPartitionNatList.getD x.1 0 }) => x.val) h_eq
      exact Subtype.ext h_val_eq
    · intro v
      obtain ⟨cell, hcell⟩ := hbij.surjective (Fin.castSucc v)
      have hne : cell.val ≠ c₀.val := by
        intro heq
        have := congr_arg t.val (Subtype.ext heq : cell = c₀)
        rw [hcell, hc₀] at this
        exact absurd this (Fin.castSucc_ne_last v)
      refine ⟨⟨cell.val, originalCell_mem_reduced (hcorner := hcorner_oc)
        cell.property hne⟩, ?_⟩
      ext
      change (t.val ⟨cell.val, _⟩).val = v.val
      have : (⟨cell.val, reducedCell_mem_original (hcorner := hcorner_oc)
        (originalCell_mem_reduced (hcorner := hcorner_oc)
          cell.property hne)⟩ :
        { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
          x.2 < la.auxiliaryPartitionNatList.getD x.1 0 }) = cell := Subtype.ext rfl
      rw [this, hcell]
      rfl
  have g_row : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la'.auxiliaryPartitionNatList.length ∧
      x.2 < la'.auxiliaryPartitionNatList.getD x.1 0 },
      c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → g c₁ < g c₂ := by
    intro c₁ c₂ hr hc
    exact hrow ⟨c₁.val, reducedCell_mem_original (hcorner := hcorner_oc) c₁.property⟩
           ⟨c₂.val, reducedCell_mem_original (hcorner := hcorner_oc) c₂.property⟩ hr hc
  have g_col : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la'.auxiliaryPartitionNatList.length ∧
      x.2 < la'.auxiliaryPartitionNatList.getD x.1 0 },
      c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → g c₁ < g c₂ := by
    intro c₁ c₂ hr hc
    exact hcol ⟨c₁.val, reducedCell_mem_original (hcorner := hcorner_oc) c₁.property⟩
           ⟨c₂.val, reducedCell_mem_original (hcorner := hcorner_oc) c₂.property⟩ hr hc
  exact ⟨corner, g, g_bij, g_row, g_col⟩



private noncomputable def sytBranchingInvFun (n : ℕ) (la : Nat.Partition (n + 1))
    (x : (c : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset) ×
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n (la.auxiliaryAtOuterCorner c.val
        (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property))) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource (n + 1) la := by
  classical
  obtain ⟨corner, t'⟩ := x
  let hcorner := YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp corner.property
  let la' := la.auxiliaryAtOuterCorner corner.val hcorner
  let f : { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
      x.2 < la.auxiliaryPartitionNatList.getD x.1 0 } → Fin (n + 1) := fun cell =>
    if h : cell.val = corner.val then Fin.last n
    else Fin.castSucc (t'.val ⟨cell.val,
      originalCell_mem_reduced (hcorner := hcorner) cell.property h⟩)
  have corner_no_right : ∀ cell : { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
      x.2 < la.auxiliaryPartitionNatList.getD x.1 0 },
      cell.val.1 = corner.val.1 → cell.val.2 > corner.val.2 → False := by
    intro cell hr hc
    have hcell_yd := (sytCell_iff_mem_toYoungDiagram la cell.val).mp cell.property
    have hmem : (cell.val.1, cell.val.2) ∈ la.auxiliaryYoungDiagramOfPartition.cells := by
      convert hcell_yd using 1
    have := la.auxiliaryYoungDiagramOfPartition.up_left_mem (le_of_eq hr.symm) (Nat.succ_le_of_lt hc) hmem
    exact hcorner.2.2 this
  have corner_no_below : ∀ cell : { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
      x.2 < la.auxiliaryPartitionNatList.getD x.1 0 },
      cell.val.2 = corner.val.2 → cell.val.1 > corner.val.1 → False := by
    intro cell hc hr
    have hcell_yd := (sytCell_iff_mem_toYoungDiagram la cell.val).mp cell.property
    have hmem : (cell.val.1, cell.val.2) ∈ la.auxiliaryYoungDiagramOfPartition.cells := by
      convert hcell_yd using 1
    have := la.auxiliaryYoungDiagramOfPartition.up_left_mem
      (Nat.succ_le_of_lt hr) (le_of_eq hc.symm) hmem
    exact hcorner.2.1 this
  have f_bij : Function.Bijective f := by
    constructor
    · intro c₁ c₂ heq
      simp only [f] at heq
      split_ifs at heq with h₁ h₂ h₂
      · exact Subtype.ext (h₁.trans h₂.symm)
      · exact absurd heq (Fin.castSucc_ne_last _).symm
      · exact absurd heq (Fin.castSucc_ne_last _)
      · have := Fin.castSucc_injective _ heq
        have h_eq := t'.property.1.injective this
        have h_val_eq : c₁.val = c₂.val :=
          congrArg (fun (x : { x : ℕ × ℕ // x.1 < la'.auxiliaryPartitionNatList.length ∧
            x.2 < la'.auxiliaryPartitionNatList.getD x.1 0 }) => x.val) h_eq
        exact Subtype.ext h_val_eq
    · intro v
      by_cases hv : v = Fin.last n
      · have hcorner_cell := (sytCell_iff_mem_toYoungDiagram la corner.val).mpr hcorner.1
        exact ⟨⟨corner.val, hcorner_cell⟩, by simp [f, dif_pos, hv]⟩
      · have hv_lt : v.val < n := Nat.lt_of_le_of_ne
          (Nat.lt_succ_iff.mp v.isLt) (Fin.val_ne_of_ne hv)
        obtain ⟨cell', hcell'⟩ := t'.property.1.surjective ⟨v.val, hv_lt⟩
        refine ⟨⟨cell'.val, reducedCell_mem_original (hcorner := hcorner)
          cell'.property⟩, ?_⟩
        simp only [f, dif_neg (reducedCell_ne_corner (hcorner := hcorner) cell'.property)]
        ext
        have : (⟨cell'.val, originalCell_mem_reduced (hcorner := hcorner)
            (reducedCell_mem_original (hcorner := hcorner) cell'.property)
            (reducedCell_ne_corner (hcorner := hcorner) cell'.property)⟩ :
          { x : ℕ × ℕ // x.1 < la'.auxiliaryPartitionNatList.length ∧
            x.2 < la'.auxiliaryPartitionNatList.getD x.1 0 }) = cell' := Subtype.ext rfl
        simp [this, hcell']
  have f_row : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
      x.2 < la.auxiliaryPartitionNatList.getD x.1 0 },
      c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → f c₁ < f c₂ := by
    intro c₁ c₂ hr hc
    simp only [f]
    split_ifs with h₁ h₂ h₂
    · exfalso; rw [h₁] at hc; rw [h₂] at hc; exact Nat.lt_irrefl _ hc
    · exfalso; exact corner_no_right c₂
        (by have := congr_arg Prod.fst h₁; omega)
        (by have := congr_arg Prod.snd h₁; omega)
    · rw [h₂] at hr hc
      exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_castSucc_iff.mpr (t'.property.2.1
        ⟨c₁.val, originalCell_mem_reduced (hcorner := hcorner) c₁.property h₁⟩
        ⟨c₂.val, originalCell_mem_reduced (hcorner := hcorner) c₂.property h₂⟩ hr hc)
  have f_col : ∀ c₁ c₂ : { x : ℕ × ℕ // x.1 < la.auxiliaryPartitionNatList.length ∧
      x.2 < la.auxiliaryPartitionNatList.getD x.1 0 },
      c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → f c₁ < f c₂ := by
    intro c₁ c₂ hc hr
    simp only [f]
    split_ifs with h₁ h₂ h₂
    · exfalso; rw [h₁] at hr; rw [h₂] at hr; exact Nat.lt_irrefl _ hr
    · exfalso; exact corner_no_below c₂
        (by have := congr_arg Prod.snd h₁; omega)
        (by have := congr_arg Prod.fst h₁; omega)
    · exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_castSucc_iff.mpr (t'.property.2.2
        ⟨c₁.val, originalCell_mem_reduced (hcorner := hcorner) c₁.property h₁⟩
        ⟨c₂.val, originalCell_mem_reduced (hcorner := hcorner) c₂.property h₂⟩ hc hr)
  exact ⟨f, f_bij, f_row, f_col⟩


private theorem sytBranching_leftInv (n : ℕ) (la : Nat.Partition (n + 1))
    (t : RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource (n + 1) la) :
    sytBranchingInvFun n la (sytBranchingToFun n la t) = t := by
  apply Subtype.ext
  funext cell
  simp only [sytBranchingInvFun, sytBranchingToFun]
  split_ifs with h
  · have hc₀_spec := (t.property.1.surjective (Fin.last n)).choose_spec
    have h_eq : cell = (t.property.1.surjective (Fin.last n)).choose := Subtype.ext h
    rw [h_eq, hc₀_spec]
  · apply Fin.ext
    rfl



private theorem sytBranching_invFun_injective (n : ℕ) (la : Nat.Partition (n + 1)) :
    Function.Injective (sytBranchingInvFun n la) := by
  intro ⟨c₁, t₁⟩ ⟨c₂, t₂⟩ heq



  have hfun := congrArg Subtype.val heq






  have hcorner_eq : c₁.val = c₂.val := by
    have hc₁_cell := (sytCell_iff_mem_toYoungDiagram la c₁.val).mpr
      (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c₁.property).1


    by_contra hne

    have hval₁ : (sytBranchingInvFun n la ⟨c₁, t₁⟩).val ⟨c₁.val, hc₁_cell⟩ = Fin.last n := by
      simp only [sytBranchingInvFun]; simp

    have hval₂ : (sytBranchingInvFun n la ⟨c₂, t₂⟩).val ⟨c₁.val, hc₁_cell⟩ ≠ Fin.last n := by
      simp only [sytBranchingInvFun]
      simp only [dif_neg hne]
      exact Fin.castSucc_ne_last _

    exact hval₂ (by rw [← hval₁]; exact (congrFun hfun ⟨c₁.val, hc₁_cell⟩).symm)
  have hc_eq : c₁ = c₂ := Subtype.ext hcorner_eq
  subst hc_eq

  congr 1

  apply Subtype.ext
  funext c'



  have hne : c'.val ≠ c₁.val :=
    reducedCell_ne_corner (hcorner := YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c₁.property) c'.property
  have hc'_la := reducedCell_mem_original
    (hcorner := YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c₁.property) c'.property
  have h₁ : (sytBranchingInvFun n la ⟨c₁, t₁⟩).val ⟨c'.val, hc'_la⟩ =
    Fin.castSucc (t₁.val c') := by
    simp only [sytBranchingInvFun, dif_neg hne]
  have h₂ : (sytBranchingInvFun n la ⟨c₁, t₂⟩).val ⟨c'.val, hc'_la⟩ =
    Fin.castSucc (t₂.val c') := by
    simp only [sytBranchingInvFun, dif_neg hne]
  have := congrFun hfun ⟨c'.val, hc'_la⟩
  rw [h₁, h₂] at this
  exact Fin.castSucc_injective _ this




private noncomputable def sytBranchingEquiv (n : ℕ) (la : Nat.Partition (n + 1)) :
    RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource (n + 1) la ≃
    (c : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset) ×
      RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n (la.auxiliaryAtOuterCorner c.val
        (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property)) :=
  haveI : Fintype (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource (n + 1) la) := RepresentationTheory.Partition.YoungDiagram.auxiliaryFintype (n + 1) la
  haveI : ∀ c : la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset,
    Fintype (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n (la.auxiliaryAtOuterCorner c.val
      (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property))) :=
    fun _c => RepresentationTheory.Partition.YoungDiagram.auxiliaryFintype n _

  have h_surj : Function.Surjective (sytBranchingInvFun n la) :=
    Function.LeftInverse.surjective (sytBranching_leftInv n la)
  have h_inj : Function.Injective (sytBranchingInvFun n la) :=
    sytBranching_invFun_injective n la
  (Equiv.ofBijective (sytBranchingInvFun n la) ⟨h_inj, h_surj⟩).symm






/-- The auxiliary cardinality for a partition of successor size equals the sum of the corresponding auxiliary cardinalities over its outer-corner reductions. -/
theorem Partition.auxiliaryCard_eq_sum_removeOuterCorner (n : ℕ) (la : Nat.Partition (n + 1)) :
    Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource (n + 1) la) =
      la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset.attach.sum (fun c =>
        Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n
          (la.auxiliaryAtOuterCorner c.val
            (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property)))) := by
  rw [Nat.card_congr (sytBranchingEquiv n la), Nat.card_sigma]
  rfl




/-- A cell belongs to the diagram obtained by removing an outer corner exactly when it belonged to the original diagram and is not the removed cell. -/
lemma YoungDiagram.mem_removeCorner_iff {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {a b : ℕ} :
    (a, b) ∈ (μ.auxiliaryCornerTransform i j hc) ↔
      (a, b) ∈ μ ∧ (a, b) ≠ (i, j) := by
  change (a, b) ∈ μ.cells.erase (i, j) ↔ (a, b) ∈ μ.cells ∧ _
  simp [Finset.mem_erase]
  tauto


/-- At an outer corner, the row length is one more than the column index. -/
lemma YoungDiagram.rowLen_eq_succ_of_isOuterCorner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) : μ.rowLen i = j + 1 := by
  have h1 : j < μ.rowLen i :=
    YoungDiagram.mem_iff_lt_rowLen.mp hc.1
  have h2 : ¬(j + 1 < μ.rowLen i) := by
    intro h
    exact hc.2.2 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
  omega


/-- At an outer corner, the column length is one more than the row index. -/
lemma YoungDiagram.colLen_eq_succ_of_isOuterCorner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) : μ.colLen j = i + 1 := by
  have h1 : i < μ.colLen j :=
    YoungDiagram.mem_iff_lt_colLen.mp hc.1
  have h2 : ¬(i + 1 < μ.colLen j) := by
    intro h
    exact hc.2.1 (YoungDiagram.mem_iff_lt_colLen.mpr h)
  omega


/-- The hook length at an outer corner is one. -/
lemma YoungDiagram.hookLength_eq_one_of_isOuterCorner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) :
    μ.auxiliaryCellStatistic i j = 1 := by
  unfold YoungDiagram.auxiliaryCellStatistic
  rw [YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc,
      YoungDiagram.colLen_eq_succ_of_isOuterCorner hc]
  omega


private lemma YoungDiagram.removeCorner_mem_row
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {a : ℕ} (ha : a ≠ i)
    (b : ℕ) :
    (a, b) ∈ (μ.auxiliaryCornerTransform i j hc) ↔ (a, b) ∈ μ := by
  rw [mem_removeCorner_iff hc]
  constructor
  · exact And.left
  · exact fun h => ⟨h, by simp [Prod.ext_iff, ha]⟩


/-- Removing an outer corner leaves every other row length unchanged. -/
lemma YoungDiagram.removeCorner_rowLen_eq_of_ne
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {a : ℕ} (ha : a ≠ i) :
    (μ.auxiliaryCornerTransform i j hc).rowLen a = μ.rowLen a := by
  apply le_antisymm
  · by_contra h; push Not at h
    have := (removeCorner_mem_row hc ha (μ.rowLen a)).mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this)
      (lt_irrefl _)
  · by_contra h; push Not at h
    have := (removeCorner_mem_row hc ha _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this)
      (lt_irrefl _)


/-- After removing an outer corner, its row has length equal to the corner's column index. -/
lemma YoungDiagram.removeCorner_rowLen_eq
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) :
    (μ.auxiliaryCornerTransform i j hc).rowLen i = j := by
  apply le_antisymm
  ·
    by_contra h; push Not at h
    have : (i, j) ∈ (μ.auxiliaryCornerTransform i j hc) :=
      YoungDiagram.mem_iff_lt_rowLen.mpr h
    rw [mem_removeCorner_iff hc] at this
    exact this.2 rfl
  ·
    by_contra h; push Not at h
    have hr := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
    have : (i, (μ.auxiliaryCornerTransform i j hc).rowLen i) ∈ μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hne : (i, (μ.auxiliaryCornerTransform i j hc).rowLen i) ≠ (i, j) :=
      by simp [Prod.ext_iff]; omega
    have : (i, (μ.auxiliaryCornerTransform i j hc).rowLen i) ∈
        (μ.auxiliaryCornerTransform i j hc) :=
      (mem_removeCorner_iff hc).mpr ⟨this, hne⟩
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this)
      (lt_irrefl _)


private lemma YoungDiagram.removeCorner_mem_col
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {b : ℕ} (hb : b ≠ j)
    (a : ℕ) :
    (a, b) ∈ (μ.auxiliaryCornerTransform i j hc) ↔ (a, b) ∈ μ := by
  rw [mem_removeCorner_iff hc]
  constructor
  · exact And.left
  · exact fun h => ⟨h, fun heq => by cases heq; exact hb rfl⟩


/-- Removing an outer corner leaves every other column length unchanged. -/
lemma YoungDiagram.removeCorner_colLen_eq_of_ne
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {b : ℕ} (hb : b ≠ j) :
    (μ.auxiliaryCornerTransform i j hc).colLen b = μ.colLen b := by
  apply le_antisymm
  · by_contra h; push Not at h
    have := (removeCorner_mem_col hc hb (μ.colLen b)).mp
      (YoungDiagram.mem_iff_lt_colLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this)
      (lt_irrefl _)
  · by_contra h; push Not at h
    have := (removeCorner_mem_col hc hb _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr h)
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this)
      (lt_irrefl _)


/-- After removing an outer corner, its column has length equal to the corner's row index. -/
lemma YoungDiagram.removeCorner_colLen_eq
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) :
    (μ.auxiliaryCornerTransform i j hc).colLen j = i := by
  apply le_antisymm
  · by_contra h; push Not at h
    have : (i, j) ∈ (μ.auxiliaryCornerTransform i j hc) :=
      YoungDiagram.mem_iff_lt_colLen.mpr h
    rw [mem_removeCorner_iff hc] at this
    exact this.2 rfl
  · by_contra h; push Not at h
    have hc_col := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc
    have : ((μ.auxiliaryCornerTransform i j hc).colLen j, j) ∈ μ :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hne :
        ((μ.auxiliaryCornerTransform i j hc).colLen j, j) ≠ (i, j) :=
      by simp [Prod.ext_iff]; omega
    have : ((μ.auxiliaryCornerTransform i j hc).colLen j, j) ∈
        (μ.auxiliaryCornerTransform i j hc) :=
      (mem_removeCorner_iff hc).mpr ⟨this, hne⟩
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp this)
      (lt_irrefl _)


/-- Removing an outer corner decreases by one the hook length of a cell to its left in the same row. -/
lemma YoungDiagram.removeCorner_hookLength_eq_sub_one_of_lt_col
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {b : ℕ} (hb : b < j) :
    (μ.auxiliaryCornerTransform i j hc).auxiliaryCellStatistic i b =
      μ.auxiliaryCellStatistic i b - 1 := by
  unfold YoungDiagram.auxiliaryCellStatistic
  rw [removeCorner_rowLen_eq hc, removeCorner_colLen_eq_of_ne hc
    (by omega : b ≠ j)]
  have := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
  omega


/-- Removing an outer corner decreases by one the hook length of a cell above it in the same column. -/
lemma YoungDiagram.removeCorner_hookLength_eq_sub_one_of_lt_row
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {a : ℕ} (ha : a < i) :
    (μ.auxiliaryCornerTransform i j hc).auxiliaryCellStatistic a j =
      μ.auxiliaryCellStatistic a j - 1 := by
  unfold YoungDiagram.auxiliaryCellStatistic
  rw [removeCorner_rowLen_eq_of_ne hc (by omega : a ≠ i),
      removeCorner_colLen_eq hc]
  have := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc
  omega


/-- Removing an outer corner preserves the hook length of a cell in a different row and column. -/
lemma YoungDiagram.removeCorner_hookLength_eq_of_row_ne_of_col_ne
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) {a b : ℕ}
    (ha : a ≠ i) (hb : b ≠ j) :
    (μ.auxiliaryCornerTransform i j hc).auxiliaryCellStatistic a b =
      μ.auxiliaryCellStatistic a b := by
  unfold YoungDiagram.auxiliaryCellStatistic
  rw [removeCorner_rowLen_eq_of_ne hc ha,
      removeCorner_colLen_eq_of_ne hc hb]














private lemma YoungDiagram.hookLengthProduct_erase_corner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) :
    μ.auxiliaryDiagramStatistic =
      (μ.cells.erase (i, j)).prod
        (fun c => μ.auxiliaryCellStatistic c.1 c.2) := by
  unfold YoungDiagram.auxiliaryDiagramStatistic
  rw [← Finset.mul_prod_erase _ _ hc.1,
      YoungDiagram.hookLength_eq_one_of_isOuterCorner hc, one_mul]

private lemma YoungDiagram.hookLengthProduct_removeCorner
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) :
    (μ.auxiliaryCornerTransform i j hc).auxiliaryDiagramStatistic =
      (μ.cells.erase (i, j)).prod
        (fun c => (μ.auxiliaryCornerTransform i j hc).auxiliaryCellStatistic
          c.1 c.2) := by
  unfold YoungDiagram.auxiliaryDiagramStatistic
  rfl


/-- The quotient of hook-length products before and after removing an outer corner equals the product of the corresponding cellwise quotients. -/
lemma YoungDiagram.hookLengthProduct_div_removeCorner_eq_prod
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j) :
    (μ.auxiliaryDiagramStatistic : ℚ) /
      ((μ.auxiliaryCornerTransform i j hc).auxiliaryDiagramStatistic : ℚ) =
    (μ.cells.erase (i, j)).prod (fun c =>
      (μ.auxiliaryCellStatistic c.1 c.2 : ℚ) /
        ((μ.auxiliaryCornerTransform i j hc).auxiliaryCellStatistic c.1 c.2 : ℚ)) := by
  rw [hookLengthProduct_erase_corner hc, hookLengthProduct_removeCorner hc]
  push_cast
  rw [Finset.prod_div_distrib]


private lemma YoungDiagram.outerCorners_eq_empty_of_cells_eq_empty
    {μ : YoungDiagram} (h : μ.cells = ∅) : μ.auxiliaryCellPairFinset = ∅ := by
  simp only [_root_.YoungDiagram.auxiliaryCellPairFinset, h]
  simp



private lemma YoungDiagram.auxiliaryCellPredicate.persist_removeCorner
    {μ : YoungDiagram} {i₀ j₀ i j : ℕ}
    (hc₀ : μ.auxiliaryCellPredicate i₀ j₀) (hc : μ.auxiliaryCellPredicate i j)
    (hne : (i, j) ≠ (i₀, j₀)) :
    (μ.auxiliaryCornerTransform i₀ j₀ hc₀).auxiliaryCellPredicate i j := by
  refine ⟨(mem_removeCorner_iff hc₀).mpr ⟨hc.1, hne⟩, ?_, ?_⟩
  ·
    intro hmem
    have : (i + 1, j) ∈ μ.cells := by
      rw [_root_.YoungDiagram.auxiliaryCornerTransform] at hmem
      exact (Finset.mem_erase.mp hmem).2
    exact hc.2.1 this
  ·
    intro hmem
    have : (i, j + 1) ∈ μ.cells := by
      rw [_root_.YoungDiagram.auxiliaryCornerTransform] at hmem
      exact (Finset.mem_erase.mp hmem).2
    exact hc.2.2 this


private lemma YoungDiagram.outerCorner_of_removeCorner
    {μ : YoungDiagram} {i₀ j₀ : ℕ}
    (hc₀ : μ.auxiliaryCellPredicate i₀ j₀)
    {c : ℕ × ℕ} (hc_oc : c ∈ μ.auxiliaryCellPairFinset) (hne : c ≠ (i₀, j₀)) :
    c ∈ (μ.auxiliaryCornerTransform i₀ j₀ hc₀).auxiliaryCellPairFinset := by
  have hc := YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp hc_oc
  exact YoungDiagram.mem_auxiliaryCellPairFinset_iff.mpr
    (YoungDiagram.auxiliaryCellPredicate.persist_removeCorner hc₀ hc hne)


private lemma YoungDiagram.hookLength_lt_of_right
    {μ : YoungDiagram} {a b b' : ℕ}
    (hb : (a, b) ∈ μ.cells) (hb' : (a, b') ∈ μ.cells)
    (hlt : b < b') :
    μ.auxiliaryCellStatistic a b' < μ.auxiliaryCellStatistic a b := by
  have h1 := YoungDiagram.auxiliaryCellStatistic_pos μ a b hb
  have h2 := YoungDiagram.auxiliaryCellStatistic_pos μ a b' hb'
  unfold YoungDiagram.auxiliaryCellStatistic at h1 h2 ⊢
  have hanti := μ.colLen_anti b b' (Nat.le_of_lt hlt)
  omega


private lemma YoungDiagram.hookLength_lt_of_down
    {μ : YoungDiagram} {a a' b : ℕ}
    (ha : (a, b) ∈ μ.cells) (ha' : (a', b) ∈ μ.cells)
    (hlt : a < a') :
    μ.auxiliaryCellStatistic a' b < μ.auxiliaryCellStatistic a b := by
  have h1 := YoungDiagram.auxiliaryCellStatistic_pos μ a b ha
  have h2 := YoungDiagram.auxiliaryCellStatistic_pos μ a' b ha'
  unfold YoungDiagram.auxiliaryCellStatistic at h1 h2 ⊢
  have hanti := μ.rowLen_anti a a' (Nat.le_of_lt hlt)
  omega



private lemma YoungDiagram.hookLength_eq_one_iff_outerCorner
    {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ.cells) :
    μ.auxiliaryCellStatistic i j = 1 ↔ μ.auxiliaryCellPredicate i j := by
  constructor
  · intro heq
    refine ⟨h, ?_, ?_⟩
    · intro hmem
      have h1 := YoungDiagram.hookLength_lt_of_down h hmem (Nat.lt_succ_of_le le_rfl)
      have h2 := YoungDiagram.auxiliaryCellStatistic_pos μ (i + 1) j hmem
      omega
    · intro hmem
      have h1 := YoungDiagram.hookLength_lt_of_right h hmem (Nat.lt_succ_of_le le_rfl)
      have h2 := YoungDiagram.auxiliaryCellStatistic_pos μ i (j + 1) hmem
      omega
  · exact fun hc => YoungDiagram.hookLength_eq_one_of_isOuterCorner hc

end






/-- An auxiliary finite set of pairs associated with a Young diagram and two indices. -/
def YoungDiagram.auxiliaryCellFinset (μ : YoungDiagram) (i j : ℕ) :
    Finset (ℕ × ℕ) :=
  ((Finset.Ico (j + 1) (μ.rowLen i)).image (fun b' => (i, b'))) ∪
  ((Finset.Ico (i + 1) (μ.colLen j)).image (fun a' => (a', j)))


private lemma YoungDiagram.hookLength_lt_of_hookCellsExcl
    {μ : YoungDiagram} {i j : ℕ} (hmem : (i, j) ∈ μ.cells)
    {v : ℕ × ℕ} (hv : v ∈ μ.auxiliaryCellFinset i j) :
    μ.auxiliaryCellStatistic v.1 v.2 < μ.auxiliaryCellStatistic i j := by
  simp only [YoungDiagram.auxiliaryCellFinset, Finset.mem_union, Finset.mem_image,
    Finset.mem_Ico] at hv
  rcases hv with ⟨b', ⟨hlo, hhi⟩, rfl⟩ | ⟨a', ⟨hlo, hhi⟩, rfl⟩
  · exact YoungDiagram.hookLength_lt_of_right hmem
      (YoungDiagram.mem_iff_lt_rowLen.mpr hhi) (by omega)
  · exact YoungDiagram.hookLength_lt_of_down hmem
      (YoungDiagram.mem_iff_lt_colLen.mpr hhi) (by omega)








/-- An auxiliary rational weight depending on a Young diagram, two indices, and a pair of indices. -/
noncomputable def YoungDiagram.auxiliaryCellWeight
    (μ : YoungDiagram) (i j : ℕ) (c : ℕ × ℕ) : ℚ :=
  if hmem : (i, j) ∈ μ.cells then
    if μ.auxiliaryCellStatistic i j = 1 then
      if (i, j) = c then 1 else 0
    else
      ((μ.auxiliaryCellFinset i j).attach.sum fun ⟨v, hv⟩ =>
        have : μ.auxiliaryCellStatistic v.1 v.2 < μ.auxiliaryCellStatistic i j :=
          YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv
        YoungDiagram.auxiliaryCellWeight μ v.1 v.2 c) /
        (μ.auxiliaryCellStatistic i j - 1 : ℚ)
  else 0
termination_by μ.auxiliaryCellStatistic i j


/-- The auxiliary weight from an outer corner to itself is one. -/
lemma YoungDiagram.auxiliaryCellWeight_self_eq_one
    {μ : YoungDiagram} {i j : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) :
    μ.auxiliaryCellWeight i j (i, j) = 1 := by
  unfold YoungDiagram.auxiliaryCellWeight
  rw [dif_pos hc.1, if_pos (YoungDiagram.hookLength_eq_one_of_isOuterCorner hc), if_pos rfl]


/-- The auxiliary weight from an outer corner to a distinct pair of indices is zero. -/
lemma YoungDiagram.auxiliaryCellWeight_eq_zero_of_ne
    {μ : YoungDiagram} {i j i' j' : ℕ}
    (hc : μ.auxiliaryCellPredicate i j) (hne : (i, j) ≠ (i', j')) :
    μ.auxiliaryCellWeight i j (i', j') = 0 := by
  unfold YoungDiagram.auxiliaryCellWeight
  rw [dif_pos hc.1, if_pos (YoungDiagram.hookLength_eq_one_of_isOuterCorner hc), if_neg hne]


/-- If a pair of indices is not a cell, every auxiliary weight originating at those indices is zero. -/
lemma YoungDiagram.auxiliaryCellWeight_eq_zero_of_not_mem
    {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∉ μ.cells)
    (c : ℕ × ℕ) : μ.auxiliaryCellWeight i j c = 0 := by
  rw [YoungDiagram.auxiliaryCellWeight, dif_neg h]




/-- For indices specifying a cell, every pair in the associated auxiliary finite set is a cell of the diagram. -/
lemma YoungDiagram.auxiliaryCellFinset_subset_cells
    {μ : YoungDiagram} {i j : ℕ} (_ : (i, j) ∈ μ.cells)
    {v : ℕ × ℕ} (hv : v ∈ μ.auxiliaryCellFinset i j) :
    v ∈ μ.cells := by
  simp only [YoungDiagram.auxiliaryCellFinset, Finset.mem_union, Finset.mem_image,
    Finset.mem_Ico] at hv
  rcases hv with ⟨b', ⟨_, hhi⟩, rfl⟩ | ⟨a', ⟨_, hhi⟩, rfl⟩
  · exact YoungDiagram.mem_iff_lt_rowLen.mpr hhi
  · exact YoungDiagram.mem_iff_lt_colLen.mpr hhi


private lemma YoungDiagram.hookCellsExcl_disjoint
    (μ : YoungDiagram) (i j : ℕ) :
    Disjoint
      ((Finset.Ico (j + 1) (μ.rowLen i)).image (fun b' => (i, b')))
      ((Finset.Ico (i + 1) (μ.colLen j)).image (fun a' => (a', j))) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_image, Finset.mem_Ico] at hx1 hx2
  obtain ⟨b', _, rfl⟩ := hx1
  obtain ⟨a', ⟨ha', _⟩, h⟩ := hx2
  simp [Prod.ext_iff] at h
  omega


/-- For a cell of a Young diagram, the associated hook cells excluding that cell have cardinality one less than its hook length. -/
lemma YoungDiagram.card_hookCellsExcl_eq_hookLength_sub_one
    {μ : YoungDiagram} {i j : ℕ} (hmem : (i, j) ∈ μ.cells) :
    (μ.auxiliaryCellFinset i j).card = μ.auxiliaryCellStatistic i j - 1 := by
  unfold YoungDiagram.auxiliaryCellFinset
  rw [Finset.card_union_of_disjoint (hookCellsExcl_disjoint μ i j)]
  have hrl := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hcl := YoungDiagram.mem_iff_lt_colLen.mp hmem
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa [Prod.ext_iff] using h),
      Finset.card_image_of_injective _ (fun a b h => by simpa [Prod.ext_iff] using h),
      Nat.card_Ico, Nat.card_Ico]
  unfold YoungDiagram.auxiliaryCellStatistic
  omega









/-- For a cell of a Young diagram, its auxiliary weights over all outer corners sum to one. -/
theorem YoungDiagram.sum_outerCorners_auxiliaryCellWeight_eq_one
    (μ : YoungDiagram) (i j : ℕ) (hmem : (i, j) ∈ μ.cells) :
    μ.auxiliaryCellPairFinset.sum (fun c => μ.auxiliaryCellWeight i j c) = 1 := by

  suffices h : ∀ (n : ℕ) (i j : ℕ), (i, j) ∈ μ.cells → μ.auxiliaryCellStatistic i j = n →
      μ.auxiliaryCellPairFinset.sum (fun c => μ.auxiliaryCellWeight i j c) = 1 from
    h _ i j hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro i j hmem h_wf
  by_cases hone : μ.auxiliaryCellStatistic i j = 1
  ·
    have hoc := (YoungDiagram.hookLength_eq_one_iff_outerCorner hmem).mp hone
    have hcorner : (i, j) ∈ μ.auxiliaryCellPairFinset := by
      rw [YoungDiagram.mem_auxiliaryCellPairFinset_iff]; exact hoc

    have hsummand : ∀ c ∈ μ.auxiliaryCellPairFinset,
        μ.auxiliaryCellWeight i j c = if (i, j) = c then 1 else 0 := by
      intro c _
      rw [YoungDiagram.auxiliaryCellWeight, dif_pos hmem, if_pos hone]
    rw [Finset.sum_congr rfl hsummand]
    rw [Finset.sum_eq_single (i, j)
      (fun b _ hne => if_neg (Ne.symm hne))
      (fun h => absurd hcorner h),
      if_pos rfl]
  ·

    have hsummand : ∀ c ∈ μ.auxiliaryCellPairFinset,
        μ.auxiliaryCellWeight i j c =
          ((μ.auxiliaryCellFinset i j).attach.sum fun ⟨v, hv⟩ =>
            YoungDiagram.auxiliaryCellWeight μ v.1 v.2 c) /
            (μ.auxiliaryCellStatistic i j - 1 : ℚ) := by
      intro c _
      rw [YoungDiagram.auxiliaryCellWeight, dif_pos hmem, if_neg hone]
    rw [Finset.sum_congr rfl hsummand]

    rw [← Finset.sum_div]

    rw [Finset.sum_comm]

    have hinner : ∀ (w : { v // v ∈ μ.auxiliaryCellFinset i j }),
        w ∈ (μ.auxiliaryCellFinset i j).attach →
        (μ.auxiliaryCellPairFinset.sum fun c =>
          YoungDiagram.auxiliaryCellWeight μ w.val.1 w.val.2 c) = 1 := by
      intro ⟨v, hv⟩ _
      exact ih (μ.auxiliaryCellStatistic v.1 v.2)
        (h_wf ▸ YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv)
        _ _ (auxiliaryCellFinset_subset_cells hmem hv) rfl
    rw [Finset.sum_congr rfl hinner]

    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_attach, card_hookCellsExcl_eq_hookLength_sub_one hmem]
    have hh_ge2 : 2 ≤ μ.auxiliaryCellStatistic i j := by
      have := YoungDiagram.auxiliaryCellStatistic_pos μ i j hmem; omega
    rw [Nat.cast_sub (by omega : 1 ≤ μ.auxiliaryCellStatistic i j)]
    have hne : (↑(μ.auxiliaryCellStatistic i j) : ℚ) - ↑1 ≠ 0 := by
      have : (2 : ℚ) ≤ μ.auxiliaryCellStatistic i j := by exact_mod_cast hh_ge2
      linarith
    exact div_self hne





private lemma YoungDiagram.hookWalkWeight_unfold_noncorner
    {μ : YoungDiagram} {a b : ℕ} (hmem : (a, b) ∈ μ.cells)
    (hne : μ.auxiliaryCellStatistic a b ≠ 1) (c : ℕ × ℕ) :
    μ.auxiliaryCellWeight a b c =
      ((μ.auxiliaryCellFinset a b).attach.sum fun ⟨v, hv⟩ =>
        μ.auxiliaryCellWeight v.1 v.2 c) /
        (μ.auxiliaryCellStatistic a b - 1 : ℚ) := by
  rw [YoungDiagram.auxiliaryCellWeight, dif_pos hmem, if_neg hne]



private lemma YoungDiagram.hookWalkWeight_other_corner
    {μ : YoungDiagram} {a b i j : ℕ}
    (hoc : μ.auxiliaryCellPredicate a b) (hne : (a, b) ≠ (i, j)) :
    μ.auxiliaryCellWeight a b (i, j) = 0 := by
  rw [YoungDiagram.auxiliaryCellWeight, dif_pos hoc.1,
      if_pos (YoungDiagram.hookLength_eq_one_of_isOuterCorner hoc), if_neg hne]


private lemma YoungDiagram.hookWalkWeight_zero_of_not_mem
    {μ : YoungDiagram} {u : ℕ × ℕ} (h : u ∉ μ.cells) (c : ℕ × ℕ) :
    μ.auxiliaryCellWeight u.1 u.2 c = 0 :=
  YoungDiagram.auxiliaryCellWeight_eq_zero_of_not_mem h c





private lemma YoungDiagram.hookRatio_arm_leg_decomp
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j) :
    (μ.cells.erase (i, j)).prod (fun c =>
      (μ.auxiliaryCellStatistic c.1 c.2 : ℚ) /
        ((μ.auxiliaryCornerTransform i j hc).auxiliaryCellStatistic c.1 c.2 : ℚ)) =
    (μ.cells.erase (i, j)).prod (fun c =>
      if c.1 = i ∧ c.2 < j then
        (μ.auxiliaryCellStatistic c.1 c.2 : ℚ) / (μ.auxiliaryCellStatistic c.1 c.2 - 1 : ℚ)
      else if c.2 = j ∧ c.1 < i then
        (μ.auxiliaryCellStatistic c.1 c.2 : ℚ) / (μ.auxiliaryCellStatistic c.1 c.2 - 1 : ℚ)
      else 1) := by
  apply Finset.prod_congr rfl
  intro ⟨a, b⟩ hmem
  simp only
  have hmem' : (a, b) ∈ μ.cells := Finset.mem_of_mem_erase hmem
  have hne : (a, b) ≠ (i, j) := Finset.ne_of_mem_erase hmem
  by_cases hai : a = i
  ·
    have hbj : b ≠ j := fun h => hne (by rw [hai, h])
    have hblt : b < j := by
      rcases Nat.lt_or_gt_of_ne hbj with h | h
      · exact h
      · exfalso
        have := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
        have := YoungDiagram.mem_iff_lt_rowLen.mp (hai ▸ hmem')
        omega

    rw [if_pos ⟨hai, hblt⟩]
    congr 1
    rw [hai, YoungDiagram.removeCorner_hookLength_eq_sub_one_of_lt_col hc hblt]
    have hpos := YoungDiagram.auxiliaryCellStatistic_pos μ i b (hai ▸ hmem')
    simp [Nat.cast_sub (by omega : 1 ≤ μ.auxiliaryCellStatistic i b)]
  · by_cases hbj : b = j
    ·
      have halt : a < i := by
        rcases Nat.lt_or_gt_of_ne hai with h | h
        · exact h
        · exfalso
          have := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc
          have := YoungDiagram.mem_iff_lt_colLen.mp (hbj ▸ hmem')
          omega

      rw [if_neg (fun h => hai h.1), if_pos ⟨hbj, halt⟩]
      congr 1
      rw [hbj, YoungDiagram.removeCorner_hookLength_eq_sub_one_of_lt_row hc halt]
      have hpos := YoungDiagram.auxiliaryCellStatistic_pos μ a j (hbj ▸ hmem')
      simp [Nat.cast_sub (by omega : 1 ≤ μ.auxiliaryCellStatistic a j)]
    ·
      rw [if_neg (fun h => hai h.1), if_neg (fun h => hbj h.1)]
      rw [YoungDiagram.removeCorner_hookLength_eq_of_row_ne_of_col_ne hc hai hbj]
      have hpos := YoungDiagram.auxiliaryCellStatistic_pos μ a b hmem'
      exact div_self (by positivity)


private lemma YoungDiagram.hookCellsExcl_mem_cells
    {μ : YoungDiagram} {a b : ℕ} (hmem : (a, b) ∈ μ.cells)
    {v : ℕ × ℕ} (hv : v ∈ μ.auxiliaryCellFinset a b) : v ∈ μ.cells :=
  YoungDiagram.auxiliaryCellFinset_subset_cells hmem hv




private lemma YoungDiagram.hookWalkWeight_zero_of_row_gt
    {μ : YoungDiagram} {a b i j : ℕ} (ha : i < a)
    (hmem : (a, b) ∈ μ.cells) :
    μ.auxiliaryCellWeight a b (i, j) = 0 := by

  suffices h : ∀ (n : ℕ) (a b : ℕ), i < a → (a, b) ∈ μ.cells →
      μ.auxiliaryCellStatistic a b = n → μ.auxiliaryCellWeight a b (i, j) = 0 from
    h _ a b ha hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b ha hmem hlen
    by_cases hone : μ.auxiliaryCellStatistic a b = 1
    · rw [YoungDiagram.auxiliaryCellWeight, dif_pos hmem, if_pos hone,
          if_neg (by intro h; exact absurd (congr_arg Prod.fst h).symm (by omega))]
    · rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem hone]
      rw [Finset.sum_eq_zero, zero_div]
      intro ⟨v, hv⟩ _
      have hv_mem := YoungDiagram.auxiliaryCellFinset_subset_cells hmem hv
      have hv_lt := YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv
      simp only [YoungDiagram.auxiliaryCellFinset, Finset.mem_union, Finset.mem_image,
        Finset.mem_Ico] at hv
      rcases hv with ⟨b', _, rfl⟩ | ⟨a', ⟨ha', _⟩, rfl⟩
      · exact ih _ (hlen ▸ hv_lt) a b' (by omega) hv_mem rfl
      · exact ih _ (hlen ▸ hv_lt) a' b (by omega) hv_mem rfl



private lemma YoungDiagram.hookWalkWeight_zero_of_col_gt
    {μ : YoungDiagram} {a b i j : ℕ} (hb : j < b)
    (hmem : (a, b) ∈ μ.cells) :
    μ.auxiliaryCellWeight a b (i, j) = 0 := by
  suffices h : ∀ (n : ℕ) (a b : ℕ), j < b → (a, b) ∈ μ.cells →
      μ.auxiliaryCellStatistic a b = n → μ.auxiliaryCellWeight a b (i, j) = 0 from
    h _ a b hb hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b hb hmem hlen
    by_cases hone : μ.auxiliaryCellStatistic a b = 1
    · rw [YoungDiagram.auxiliaryCellWeight, dif_pos hmem, if_pos hone,
          if_neg (by intro h; exact absurd (congr_arg Prod.snd h).symm (by omega))]
    · rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem hone]
      rw [Finset.sum_eq_zero, zero_div]
      intro ⟨v, hv⟩ _
      have hv_mem := YoungDiagram.auxiliaryCellFinset_subset_cells hmem hv
      have hv_lt := YoungDiagram.hookLength_lt_of_hookCellsExcl hmem hv
      simp only [YoungDiagram.auxiliaryCellFinset, Finset.mem_union, Finset.mem_image,
        Finset.mem_Ico] at hv
      rcases hv with ⟨b', ⟨hb', _⟩, rfl⟩ | ⟨a', _, rfl⟩
      · exact ih _ (hlen ▸ hv_lt) a b' (by omega) hv_mem rfl
      · exact ih _ (hlen ▸ hv_lt) a' b (by omega) hv_mem rfl







private lemma YoungDiagram.hookLength_sub_one_decomp
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j)
    {a b : ℕ} (ha : a ≤ i) (hb : b ≤ j) (hmem : (a, b) ∈ μ.cells) :
    μ.auxiliaryCellStatistic a b - 1 = (μ.auxiliaryCellStatistic a j - 1) + (μ.auxiliaryCellStatistic i b - 1) := by
  have hrl := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
  have hcl := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc
  have hmem_aj : (a, j) ∈ μ.cells := by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen]; omega
  have hmem_ib : (i, b) ∈ μ.cells := by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]; omega
  simp only [YoungDiagram.auxiliaryCellStatistic]
  have h1 : i + 1 ≤ μ.colLen b := YoungDiagram.mem_iff_lt_colLen.mp hmem_ib
  have h2 : j + 1 ≤ μ.rowLen a := YoungDiagram.mem_iff_lt_rowLen.mp hmem_aj
  omega




private lemma YoungDiagram.hookWalkWeight_factorization
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j)
    {a b : ℕ} (ha : a ≤ i) (hb : b ≤ j) (hmem : (a, b) ∈ μ.cells) :
    μ.auxiliaryCellWeight a b (i, j) =
      μ.auxiliaryCellWeight a j (i, j) * μ.auxiliaryCellWeight i b (i, j) := by
  have hrl := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
  have hcl := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc

  suffices hsuff : ∀ (n : ℕ) (a b : ℕ), a ≤ i → b ≤ j → (a, b) ∈ μ.cells →
      μ.auxiliaryCellStatistic a b = n →
      μ.auxiliaryCellWeight a b (i, j) =
        μ.auxiliaryCellWeight a j (i, j) * μ.auxiliaryCellWeight i b (i, j) from
    hsuff _ a b ha hb hmem rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b ha hb hmem hlen
    have hmem_aj : (a, j) ∈ μ.cells := by
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen]; omega
    have hmem_ib : (i, b) ∈ μ.cells := by
      rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]; omega
    by_cases hone : μ.auxiliaryCellStatistic a b = 1
    ·

      have hoc := (YoungDiagram.hookLength_eq_one_iff_outerCorner
        (by rw [YoungDiagram.mem_cells] at hmem; exact hmem)).mp hone
      have hab_eq : a = i ∧ b = j := by
        constructor
        ·
          have := YoungDiagram.colLen_eq_succ_of_isOuterCorner hoc
          have := YoungDiagram.mem_iff_lt_colLen.mp hmem_ib
          omega
        ·
          have := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hoc
          have := YoungDiagram.mem_iff_lt_rowLen.mp hmem_aj
          omega
      rw [hab_eq.1, hab_eq.2, YoungDiagram.auxiliaryCellWeight_self_eq_one hc]; ring
    ·

      by_cases hbj : b = j
      ·
        rw [hbj, YoungDiagram.auxiliaryCellWeight_self_eq_one hc, mul_one]
      · by_cases hai : a = i
        ·
          rw [hai, YoungDiagram.auxiliaryCellWeight_self_eq_one hc, one_mul]
        ·
          have halt : a < i := lt_of_le_of_ne ha hai
          have hblt : b < j := lt_of_le_of_ne hb hbj

          have hone_ib : μ.auxiliaryCellStatistic i b ≠ 1 := by
            intro h
            have hoc := (YoungDiagram.hookLength_eq_one_iff_outerCorner
              (by rw [YoungDiagram.mem_cells] at hmem_ib; exact hmem_ib)).mp h
            have hrl_ib := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hoc

            omega
          have hone_aj : μ.auxiliaryCellStatistic a j ≠ 1 := by
            intro h
            have hoc := (YoungDiagram.hookLength_eq_one_iff_outerCorner
              (by rw [YoungDiagram.mem_cells] at hmem_aj; exact hmem_aj)).mp h
            have hcl_aj := YoungDiagram.colLen_eq_succ_of_isOuterCorner hoc

            omega


          have hh_pos : (0 : ℚ) < μ.auxiliaryCellStatistic a b - 1 := by
            have h1 := YoungDiagram.auxiliaryCellStatistic_pos μ a b hmem
            have h2 : 1 < μ.auxiliaryCellStatistic a b := by omega
            exact_mod_cast (show (0 : ℤ) < (μ.auxiliaryCellStatistic a b : ℤ) - 1 by omega)

          suffices hsum : (μ.auxiliaryCellFinset a b).sum
              (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j)) =
              μ.auxiliaryCellWeight a j (i, j) * μ.auxiliaryCellWeight i b (i, j) *
                (↑(μ.auxiliaryCellStatistic a b) - 1) by
            rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem hone]
            change (∑ x ∈ (μ.auxiliaryCellFinset a b).attach,
                μ.auxiliaryCellWeight x.val.1 x.val.2 (i, j)) /
                (↑(μ.auxiliaryCellStatistic a b) - 1) =
              μ.auxiliaryCellWeight a j (i, j) * μ.auxiliaryCellWeight i b (i, j)
            rw [@Finset.sum_attach _ _ _ (μ.auxiliaryCellFinset a b)
                (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j)),
              hsum, mul_div_cancel_right₀ _ (ne_of_gt hh_pos)]

          have hdisj := YoungDiagram.hookCellsExcl_disjoint μ a b
          rw [YoungDiagram.auxiliaryCellFinset, Finset.sum_union hdisj]

          rw [Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
              Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
          simp only [Prod.fst]




          have hrla : j + 1 ≤ μ.rowLen a :=
            YoungDiagram.mem_iff_lt_rowLen.mp hmem_aj
          have hclb : i + 1 ≤ μ.colLen b :=
            YoungDiagram.mem_iff_lt_colLen.mp hmem_ib
          rw [show Finset.Ico (b + 1) (μ.rowLen a) =
                Finset.Ico (b + 1) (j + 1) ∪ Finset.Ico (j + 1) (μ.rowLen a) from
                (Finset.Ico_union_Ico_eq_Ico (by omega) hrla).symm,
              show Finset.Ico (a + 1) (μ.colLen b) =
                Finset.Ico (a + 1) (i + 1) ∪ Finset.Ico (i + 1) (μ.colLen b) from
                (Finset.Ico_union_Ico_eq_Ico (by omega) hclb).symm]
          rw [Finset.sum_union (by
                rw [Finset.disjoint_left]; intro x hx1 hx2
                simp [Finset.mem_Ico] at hx1 hx2; omega),
              Finset.sum_union (by
                rw [Finset.disjoint_left]; intro x hx1 hx2
                simp [Finset.mem_Ico] at hx1 hx2; omega)]

          have hvan_arm : (Finset.Ico (j + 1) (μ.rowLen a)).sum
              (fun b' => μ.auxiliaryCellWeight a b' (i, j)) = 0 := by
            apply Finset.sum_eq_zero; intro b' hb'
            simp [Finset.mem_Ico] at hb'
            exact YoungDiagram.hookWalkWeight_zero_of_col_gt
              (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hb'.2)
          have hvan_leg : (Finset.Ico (i + 1) (μ.colLen b)).sum
              (fun a' => μ.auxiliaryCellWeight a' b (i, j)) = 0 := by
            apply Finset.sum_eq_zero; intro a' ha'
            simp [Finset.mem_Ico] at ha'
            exact YoungDiagram.hookWalkWeight_zero_of_row_gt
              (by omega) (YoungDiagram.mem_iff_lt_colLen.mpr ha'.2)
          rw [hvan_arm, hvan_leg, add_zero, add_zero]




          have hih_arm : ∀ b' ∈ Finset.Ico (b + 1) (j + 1),
              μ.auxiliaryCellWeight a b' (i, j) =
                μ.auxiliaryCellWeight a j (i, j) * μ.auxiliaryCellWeight i b' (i, j) := by
            intro b' hb'
            simp [Finset.mem_Ico] at hb'
            have hb'mem : (a, b') ∈ μ.cells :=
              YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
            have hlt : μ.auxiliaryCellStatistic a b' < μ.auxiliaryCellStatistic a b :=
              YoungDiagram.hookLength_lt_of_right hmem hb'mem (by omega)
            exact ih _ (hlen ▸ hlt) a b' ha (by omega) hb'mem rfl
          have hih_leg : ∀ a' ∈ Finset.Ico (a + 1) (i + 1),
              μ.auxiliaryCellWeight a' b (i, j) =
                μ.auxiliaryCellWeight a' j (i, j) * μ.auxiliaryCellWeight i b (i, j) := by
            intro a' ha'
            simp [Finset.mem_Ico] at ha'
            have ha'mem : (a', b) ∈ μ.cells :=
              YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
            have hlt : μ.auxiliaryCellStatistic a' b < μ.auxiliaryCellStatistic a b :=
              YoungDiagram.hookLength_lt_of_down hmem ha'mem (by omega)
            exact ih _ (hlen ▸ hlt) a' b (by omega) hb ha'mem rfl
          rw [Finset.sum_congr rfl hih_arm, Finset.sum_congr rfl hih_leg]

          rw [← Finset.mul_sum, ← Finset.sum_mul]






          have hrec_ib : (Finset.Ico (b + 1) (j + 1)).sum
              (fun b' => μ.auxiliaryCellWeight i b' (i, j)) =
              (↑(μ.auxiliaryCellStatistic i b) - 1) * μ.auxiliaryCellWeight i b (i, j) := by
            have hunf : μ.auxiliaryCellWeight i b (i, j) =
                (μ.auxiliaryCellFinset i b).sum (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j)) /
                  (↑(μ.auxiliaryCellStatistic i b) - 1) := by
              have h := YoungDiagram.hookWalkWeight_unfold_noncorner hmem_ib hone_ib (i, j)
              change μ.auxiliaryCellWeight i b (i, j) = _
              rw [h]; congr 1
              rw [@Finset.sum_attach _ _ _ (μ.auxiliaryCellFinset i b)
                (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j))]
            rw [YoungDiagram.auxiliaryCellFinset,
                Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ i b),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)] at hunf
            simp only [Prod.fst] at hunf
            rw [hrl] at hunf
            have hleg_van : (Finset.Ico (i + 1) (μ.colLen b)).sum
                (fun a' => μ.auxiliaryCellWeight a' b (i, j)) = 0 :=
              Finset.sum_eq_zero (fun a' ha' => by
                simp [Finset.mem_Ico] at ha'
                exact YoungDiagram.hookWalkWeight_zero_of_row_gt
                  (by omega) (YoungDiagram.mem_iff_lt_colLen.mpr ha'.2))
            rw [hleg_van, add_zero] at hunf
            have hh_ib : (↑(μ.auxiliaryCellStatistic i b) - 1 : ℚ) ≠ 0 := ne_of_gt (by
              have h1 := YoungDiagram.auxiliaryCellStatistic_pos μ i b hmem_ib
              have h2 : 1 < μ.auxiliaryCellStatistic i b := by omega
              exact_mod_cast (show (0 : ℤ) < (μ.auxiliaryCellStatistic i b : ℤ) - 1 by omega))
            rw [hunf, mul_div_cancel₀ _ hh_ib]
          have hrec_aj : (Finset.Ico (a + 1) (i + 1)).sum
              (fun a' => μ.auxiliaryCellWeight a' j (i, j)) =
              (↑(μ.auxiliaryCellStatistic a j) - 1) * μ.auxiliaryCellWeight a j (i, j) := by
            have hunf : μ.auxiliaryCellWeight a j (i, j) =
                (μ.auxiliaryCellFinset a j).sum (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j)) /
                  (↑(μ.auxiliaryCellStatistic a j) - 1) := by
              have h := YoungDiagram.hookWalkWeight_unfold_noncorner hmem_aj hone_aj (i, j)
              change μ.auxiliaryCellWeight a j (i, j) = _
              rw [h]; congr 1
              rw [@Finset.sum_attach _ _ _ (μ.auxiliaryCellFinset a j)
                (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j))]
            rw [YoungDiagram.auxiliaryCellFinset,
                Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ a j),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
                Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)] at hunf
            simp only [Prod.fst] at hunf
            rw [hcl] at hunf
            have harm_van : (Finset.Ico (j + 1) (μ.rowLen a)).sum
                (fun b' => μ.auxiliaryCellWeight a b' (i, j)) = 0 :=
              Finset.sum_eq_zero (fun b' hb' => by
                simp [Finset.mem_Ico] at hb'
                exact YoungDiagram.hookWalkWeight_zero_of_col_gt
                  (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hb'.2))
            rw [harm_van, zero_add] at hunf
            have hh_aj : (↑(μ.auxiliaryCellStatistic a j) - 1 : ℚ) ≠ 0 := ne_of_gt (by
              have h1 := YoungDiagram.auxiliaryCellStatistic_pos μ a j hmem_aj
              have h2 : 1 < μ.auxiliaryCellStatistic a j := by omega
              exact_mod_cast (show (0 : ℤ) < (μ.auxiliaryCellStatistic a j : ℤ) - 1 by omega))
            rw [hunf, mul_div_cancel₀ _ hh_aj]
          rw [hrec_ib, hrec_aj]





          have hdecomp := YoungDiagram.hookLength_sub_one_decomp hc ha hb hmem

          have hd : (μ.auxiliaryCellStatistic a b : ℚ) =
              (μ.auxiliaryCellStatistic a j : ℚ) + (μ.auxiliaryCellStatistic i b : ℚ) - 1 := by
            have h1 := YoungDiagram.auxiliaryCellStatistic_pos μ a b hmem
            have h2 := YoungDiagram.auxiliaryCellStatistic_pos μ a j hmem_aj
            have h3 := YoungDiagram.auxiliaryCellStatistic_pos μ i b hmem_ib
            have : (μ.auxiliaryCellStatistic a b : ℤ) =
                (μ.auxiliaryCellStatistic a j : ℤ) + (μ.auxiliaryCellStatistic i b : ℤ) - 1 := by
              zify [h1, h2, h3] at hdecomp; linarith
            exact_mod_cast this
          rw [hd]; ring



private lemma YoungDiagram.hookWalkWeight_row_telescope
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j)
    {b : ℕ} (hb : b ≤ j) :
    (Finset.Ico b (j + 1)).sum (fun b' => μ.auxiliaryCellWeight i b' (i, j)) =
      (Finset.Ico b j).prod (fun b' =>
        (μ.auxiliaryCellStatistic i b' : ℚ) / (μ.auxiliaryCellStatistic i b' - 1 : ℚ)) := by
  have hrl := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
  suffices ∀ n (b : ℕ), b ≤ j → j + 1 - b = n →
      (Finset.Ico b (j + 1)).sum (fun b' => μ.auxiliaryCellWeight i b' (i, j)) =
        (Finset.Ico b j).prod (fun b' =>
          (μ.auxiliaryCellStatistic i b' : ℚ) / (μ.auxiliaryCellStatistic i b' - 1 : ℚ)) from
    this _ b hb rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b hb hn
    by_cases hbj : b = j
    ·
      rw [show Finset.Ico b (j + 1) = {b} from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_singleton]
      rw [show Finset.Ico b j = ∅ from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_empty, hbj, YoungDiagram.auxiliaryCellWeight_self_eq_one hc]
    · have hblt : b < j := lt_of_le_of_ne hb hbj
      rw [show Finset.Ico b (j + 1) = {b} ∪ Finset.Ico (b + 1) (j + 1) from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.sum_singleton]
      have ih_val := ih (j - b) (by omega) (b + 1) (by omega) (by omega)
      rw [show Finset.Ico b j = {b} ∪ Finset.Ico (b + 1) j from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.prod_singleton]
      have hmem_ib : (i, b) ∈ μ.cells := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hone_ib : μ.auxiliaryCellStatistic i b ≠ 1 := by
        intro h
        have hoc := (YoungDiagram.hookLength_eq_one_iff_outerCorner
          (by rw [YoungDiagram.mem_cells] at hmem_ib; exact hmem_ib)).mp h
        have := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hoc; omega
      have hh_pos : (0 : ℚ) < μ.auxiliaryCellStatistic i b - 1 := by
        have := YoungDiagram.auxiliaryCellStatistic_pos μ i b hmem_ib
        have : 1 < μ.auxiliaryCellStatistic i b := by omega
        exact_mod_cast (show (0 : ℤ) < (μ.auxiliaryCellStatistic i b : ℤ) - 1 by omega)
      have hw_eq : μ.auxiliaryCellWeight i b (i, j) =
          (Finset.Ico (b + 1) (j + 1)).sum (fun b' => μ.auxiliaryCellWeight i b' (i, j)) /
            (μ.auxiliaryCellStatistic i b - 1 : ℚ) := by
        rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem_ib hone_ib]
        congr 1
        change (∑ x ∈ (μ.auxiliaryCellFinset i b).attach,
            μ.auxiliaryCellWeight x.val.1 x.val.2 (i, j)) = _
        rw [@Finset.sum_attach _ _ _ (μ.auxiliaryCellFinset i b)
            (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j))]
        rw [YoungDiagram.auxiliaryCellFinset,
            Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ i b),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
        simp only [Prod.fst]
        rw [hrl]
        have hleg_van : (Finset.Ico (i + 1) (μ.colLen b)).sum
            (fun a' => μ.auxiliaryCellWeight a' b (i, j)) = 0 :=
          Finset.sum_eq_zero (fun a' ha' => by
            simp [Finset.mem_Ico] at ha'
            exact YoungDiagram.hookWalkWeight_zero_of_row_gt
              (by omega) (YoungDiagram.mem_iff_lt_colLen.mpr ha'.2))
        rw [hleg_van, add_zero]
      rw [hw_eq, ih_val]
      have hne : (↑(μ.auxiliaryCellStatistic i b) - 1 : ℚ) ≠ 0 := ne_of_gt hh_pos
      field_simp
      ring


private lemma YoungDiagram.hookWalkWeight_col_telescope
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j)
    {a : ℕ} (ha : a ≤ i) :
    (Finset.Ico a (i + 1)).sum (fun a' => μ.auxiliaryCellWeight a' j (i, j)) =
      (Finset.Ico a i).prod (fun a' =>
        (μ.auxiliaryCellStatistic a' j : ℚ) / (μ.auxiliaryCellStatistic a' j - 1 : ℚ)) := by
  have hcl := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc
  suffices ∀ n (a : ℕ), a ≤ i → i + 1 - a = n →
      (Finset.Ico a (i + 1)).sum (fun a' => μ.auxiliaryCellWeight a' j (i, j)) =
        (Finset.Ico a i).prod (fun a' =>
          (μ.auxiliaryCellStatistic a' j : ℚ) / (μ.auxiliaryCellStatistic a' j - 1 : ℚ)) from
    this _ a ha rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a ha hn
    by_cases haj : a = i
    · rw [show Finset.Ico a (i + 1) = {a} from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_singleton]
      rw [show Finset.Ico a i = ∅ from by ext; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_empty, haj, YoungDiagram.auxiliaryCellWeight_self_eq_one hc]
    · have halt : a < i := lt_of_le_of_ne ha haj
      rw [show Finset.Ico a (i + 1) = {a} ∪ Finset.Ico (a + 1) (i + 1) from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.sum_singleton]
      have ih_val := ih (i - a) (by omega) (a + 1) (by omega) (by omega)
      rw [show Finset.Ico a i = {a} ∪ Finset.Ico (a + 1) i from by
            ext x; simp [Finset.mem_Ico]; omega]
      rw [Finset.prod_union (Finset.disjoint_singleton_left.mpr (by simp [Finset.mem_Ico]))]
      simp only [Finset.prod_singleton]
      have hmem_aj : (a, j) ∈ μ.cells := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      have hone_aj : μ.auxiliaryCellStatistic a j ≠ 1 := by
        intro h
        have hoc := (YoungDiagram.hookLength_eq_one_iff_outerCorner
          (by rw [YoungDiagram.mem_cells] at hmem_aj; exact hmem_aj)).mp h
        have := YoungDiagram.colLen_eq_succ_of_isOuterCorner hoc; omega
      have hh_pos : (0 : ℚ) < μ.auxiliaryCellStatistic a j - 1 := by
        have := YoungDiagram.auxiliaryCellStatistic_pos μ a j hmem_aj
        have : 1 < μ.auxiliaryCellStatistic a j := by omega
        exact_mod_cast (show (0 : ℤ) < (μ.auxiliaryCellStatistic a j : ℤ) - 1 by omega)
      have hw_eq : μ.auxiliaryCellWeight a j (i, j) =
          (Finset.Ico (a + 1) (i + 1)).sum (fun a' => μ.auxiliaryCellWeight a' j (i, j)) /
            (μ.auxiliaryCellStatistic a j - 1 : ℚ) := by
        rw [YoungDiagram.hookWalkWeight_unfold_noncorner hmem_aj hone_aj]
        congr 1
        change (∑ x ∈ (μ.auxiliaryCellFinset a j).attach,
            μ.auxiliaryCellWeight x.val.1 x.val.2 (i, j)) = _
        rw [@Finset.sum_attach _ _ _ (μ.auxiliaryCellFinset a j)
            (fun v => μ.auxiliaryCellWeight v.1 v.2 (i, j))]
        rw [YoungDiagram.auxiliaryCellFinset,
            Finset.sum_union (YoungDiagram.hookCellsExcl_disjoint μ a j),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h),
            Finset.sum_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
        simp only [Prod.fst]
        rw [hcl]
        have harm_van : (Finset.Ico (j + 1) (μ.rowLen a)).sum
            (fun b' => μ.auxiliaryCellWeight a b' (i, j)) = 0 :=
          Finset.sum_eq_zero (fun b' hb' => by
            simp [Finset.mem_Ico] at hb'
            exact YoungDiagram.hookWalkWeight_zero_of_col_gt
              (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr hb'.2))
        rw [harm_van, zero_add]
      rw [hw_eq, ih_val]
      have hne : (↑(μ.auxiliaryCellStatistic a j) - 1 : ℚ) ≠ 0 := ne_of_gt hh_pos
      field_simp
      ring



private lemma YoungDiagram.hookRatio_eq_range_prods
    {μ : YoungDiagram} {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j) :
    (μ.auxiliaryDiagramStatistic : ℚ) / ((μ.auxiliaryCornerTransform i j hc).auxiliaryDiagramStatistic : ℚ) =
      (Finset.range j).prod (fun b =>
        (μ.auxiliaryCellStatistic i b : ℚ) / (μ.auxiliaryCellStatistic i b - 1 : ℚ)) *
      (Finset.range i).prod (fun a =>
        (μ.auxiliaryCellStatistic a j : ℚ) / (μ.auxiliaryCellStatistic a j - 1 : ℚ)) := by
  have hrl := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
  have hcl := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc
  rw [YoungDiagram.hookLengthProduct_div_removeCorner_eq_prod hc]

  have hcond : (μ.cells.erase (i, j)).prod (fun c =>
      (μ.auxiliaryCellStatistic c.1 c.2 : ℚ) /
        ((μ.auxiliaryCornerTransform i j hc).auxiliaryCellStatistic c.1 c.2 : ℚ)) =
    (μ.cells.erase (i, j)).prod (fun c =>
      if c.1 = i ∨ c.2 = j then
        (μ.auxiliaryCellStatistic c.1 c.2 : ℚ) / (μ.auxiliaryCellStatistic c.1 c.2 - 1 : ℚ)
      else 1) := by
    apply Finset.prod_congr rfl
    intro ⟨a, b⟩ hmem
    have hmem' := Finset.mem_of_mem_erase hmem
    have hne := Finset.ne_of_mem_erase hmem
    by_cases hai : a = i
    · have hblt : b < j := by
        have := YoungDiagram.mem_iff_lt_rowLen.mp (hai ▸ hmem')
        have : b ≠ j := fun h => hne (Prod.ext hai h); omega
      rw [if_pos (Or.inl hai)]
      have hmem_ib := hai ▸ hmem'
      have h_pos := YoungDiagram.auxiliaryCellStatistic_pos μ i b hmem_ib
      congr 1; simp only [Prod.fst]
      rw [hai, YoungDiagram.removeCorner_hookLength_eq_sub_one_of_lt_col hc hblt]
      exact Nat.cast_sub (by omega)
    · by_cases hbj : b = j
      · have halt : a < i := by
          have := YoungDiagram.mem_iff_lt_colLen.mp (hbj ▸ hmem')
          omega
        rw [if_pos (Or.inr hbj)]
        have hmem_aj := hbj ▸ hmem'
        have h_pos := YoungDiagram.auxiliaryCellStatistic_pos μ a j hmem_aj
        congr 1; simp only [Prod.fst]
        rw [hbj, YoungDiagram.removeCorner_hookLength_eq_sub_one_of_lt_row hc halt]
        exact Nat.cast_sub (by omega)
      · rw [if_neg (by push Not; exact ⟨hai, hbj⟩)]
        simp only [Prod.fst]
        rw [YoungDiagram.removeCorner_hookLength_eq_of_row_ne_of_col_ne hc hai hbj]
        have h_pos := YoungDiagram.auxiliaryCellStatistic_pos μ a b hmem'
        exact div_self (Nat.cast_ne_zero.mpr (by omega))
  rw [hcond, ← Finset.prod_filter]

  have hfilter_eq : (μ.cells.erase (i, j)).filter (fun c => c.1 = i ∨ c.2 = j) =
      (Finset.range j).image (fun b => (i, b)) ∪
      (Finset.range i).image (fun a => (a, j)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_union,
      Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hne, hmem⟩, hai | hbj⟩
      · left; refine ⟨b, ?_, ?_, ?_⟩
        · have := YoungDiagram.mem_iff_lt_rowLen.mp (hai ▸ hmem)
          have : b ≠ j := fun h => hne (Prod.ext hai h); omega
        · exact hai.symm
        · rfl
      · right; refine ⟨a, ?_, ?_, ?_⟩
        · have := YoungDiagram.mem_iff_lt_colLen.mp (hbj ▸ hmem)
          have : a ≠ i := fun h => hne (Prod.ext h hbj); omega
        · rfl
        · exact hbj.symm
    · rintro (⟨b', hb', rfl, rfl⟩ | ⟨a', ha', rfl, rfl⟩)
      · exact ⟨⟨by intro h; simp [Prod.ext_iff] at h; omega,
                 YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)⟩, Or.inl rfl⟩
      · exact ⟨⟨by intro h; simp [Prod.ext_iff] at h; omega,
                 YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩, Or.inr rfl⟩
  rw [hfilter_eq]

  rw [Finset.prod_union (by
        rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
        simp [Finset.mem_image, Finset.mem_range, Prod.ext_iff] at h1 h2
        obtain ⟨_, _, rfl, rfl⟩ := h1; obtain ⟨_, ha', rfl, _⟩ := h2; omega)]
  conv_lhs =>
    arg 1; rw [Finset.prod_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]
  conv_lhs =>
    arg 2; rw [Finset.prod_image (by intro x _ y _ h; simpa [Prod.ext_iff] using h)]








private lemma YoungDiagram.hookWalkWeight_col_sum_singleton
    (μ : YoungDiagram) {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j)
    (hcard : μ.cells.card = 1) :
    μ.cells.sum (fun u => μ.auxiliaryCellWeight u.1 u.2 (i, j)) =
      (μ.auxiliaryDiagramStatistic : ℚ) /
        ((μ.auxiliaryCornerTransform i j hc).auxiliaryDiagramStatistic : ℚ) := by

  have honly : μ.cells = {(i, j)} := by
    have := Finset.card_eq_one.mp hcard
    obtain ⟨a, ha⟩ := this
    rw [ha]
    have : (i, j) ∈ μ.cells := hc.1
    rw [ha] at this
    exact congrArg _ (Finset.mem_singleton.mp this).symm

  rw [honly, Finset.sum_singleton]
  rw [YoungDiagram.auxiliaryCellWeight_self_eq_one hc]

  have hHP : μ.auxiliaryDiagramStatistic = 1 := by
    unfold YoungDiagram.auxiliaryDiagramStatistic
    rw [honly, Finset.prod_singleton]
    exact YoungDiagram.hookLength_eq_one_of_isOuterCorner hc
  have hHP' : (μ.auxiliaryCornerTransform i j hc).auxiliaryDiagramStatistic = 1 := by
    unfold YoungDiagram.auxiliaryDiagramStatistic
    have : (μ.auxiliaryCornerTransform i j hc).cells = ∅ := by
      simp [YoungDiagram.auxiliaryCornerTransform, honly]
    rw [this, Finset.prod_empty]
  rw [hHP, hHP']
  simp

/-- The sum over all cells of the auxiliary weights directed toward an outer corner equals the quotient of the diagram statistics before and after removing that corner. -/
theorem YoungDiagram.sum_auxiliaryCellWeight_eq_statistic_div
    (μ : YoungDiagram) {i j : ℕ} (hc : μ.auxiliaryCellPredicate i j) :
    μ.cells.sum (fun u => μ.auxiliaryCellWeight u.1 u.2 (i, j)) =
      (μ.auxiliaryDiagramStatistic : ℚ) /
        ((μ.auxiliaryCornerTransform i j hc).auxiliaryDiagramStatistic : ℚ) := by

  suffices h : ∀ (n : ℕ) (μ : YoungDiagram) (i j : ℕ) (hc : μ.auxiliaryCellPredicate i j),
      μ.cells.card = n →
      μ.cells.sum (fun u => μ.auxiliaryCellWeight u.1 u.2 (i, j)) =
        (μ.auxiliaryDiagramStatistic : ℚ) /
          ((μ.auxiliaryCornerTransform i j hc).auxiliaryDiagramStatistic : ℚ) from
    h _ μ i j hc rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro μ i j hc hcard

    by_cases hn : n ≤ 1
    · have hcard1 : μ.cells.card = 1 := by
        have hpos : 0 < μ.cells.card := Finset.card_pos.mpr ⟨(i, j), hc.1⟩
        omega
      exact hookWalkWeight_col_sum_singleton μ hc hcard1
    ·
      push Not at hn

      have hrl := YoungDiagram.rowLen_eq_succ_of_isOuterCorner hc
      have hcl := YoungDiagram.colLen_eq_succ_of_isOuterCorner hc

      have hsum_rect : μ.cells.sum (fun u => μ.auxiliaryCellWeight u.1 u.2 (i, j)) =
          (μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j)).sum
            (fun u => μ.auxiliaryCellWeight u.1 u.2 (i, j)) := by
        rw [Finset.sum_filter_of_ne]
        intro ⟨a, b⟩ hmem hne
        by_contra hab
        simp only [not_and_or, not_le] at hab
        rcases hab with ha | hb
        · exact absurd (YoungDiagram.hookWalkWeight_zero_of_row_gt ha hmem) hne
        · exact absurd (YoungDiagram.hookWalkWeight_zero_of_col_gt hb hmem) hne
      rw [hsum_rect]

      have hfact : (μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j)).sum
            (fun u => μ.auxiliaryCellWeight u.1 u.2 (i, j)) =
          (μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j)).sum
            (fun u => μ.auxiliaryCellWeight u.1 j (i, j) * μ.auxiliaryCellWeight i u.2 (i, j)) := by
        apply Finset.sum_congr rfl
        intro ⟨a, b⟩ hmem
        simp only [Finset.mem_filter] at hmem
        exact YoungDiagram.hookWalkWeight_factorization hc hmem.2.1 hmem.2.2 hmem.1
      rw [hfact]



      have hfilter_eq : μ.cells.filter (fun u => u.1 ≤ i ∧ u.2 ≤ j) =
          Finset.Ico 0 (i + 1) ×ˢ Finset.Ico 0 (j + 1) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
        constructor
        · rintro ⟨_, ha, hb⟩; exact ⟨⟨Nat.zero_le _, Nat.lt_succ_of_le ha⟩,
            ⟨Nat.zero_le _, Nat.lt_succ_of_le hb⟩⟩
        · rintro ⟨⟨_, ha⟩, ⟨_, hb⟩⟩
          have ha' : a ≤ i := Nat.lt_succ_iff.mp ha
          have hb' : b ≤ j := Nat.lt_succ_iff.mp hb
          exact ⟨μ.up_left_mem ha' hb' hc.1, ha', hb'⟩
      rw [hfilter_eq]

      rw [Finset.sum_product]


      simp_rw [← Finset.mul_sum]


      rw [← Finset.sum_mul]


      rw [show Finset.Ico 0 (i + 1) = Finset.Ico 0 (i + 1) from rfl]
      rw [show Finset.Ico 0 (j + 1) = Finset.Ico 0 (j + 1) from rfl]
      rw [YoungDiagram.hookWalkWeight_col_telescope hc (Nat.zero_le _)]
      rw [YoungDiagram.hookWalkWeight_row_telescope hc (Nat.zero_le _)]


      rw [YoungDiagram.hookRatio_eq_range_prods hc]
      simp only [Finset.range_eq_Ico]
      ring


noncomputable section




















private lemma YoungDiagram.hook_quotient_identity_yd
    (μ : YoungDiagram) :
    μ.auxiliaryCellPairFinset.attach.sum (fun c =>
      (μ.auxiliaryDiagramStatistic : ℚ) /
        ((μ.auxiliaryCornerTransform c.val.1 c.val.2
          (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp
            c.property)).auxiliaryDiagramStatistic : ℚ)) =
      (μ.cells.card : ℚ) := by

  have hstep1 : μ.auxiliaryCellPairFinset.attach.sum (fun c =>
      (μ.auxiliaryDiagramStatistic : ℚ) /
        ((μ.auxiliaryCornerTransform c.val.1 c.val.2
          (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property)).auxiliaryDiagramStatistic : ℚ)) =
      μ.auxiliaryCellPairFinset.attach.sum (fun c =>
        μ.cells.sum (fun u => μ.auxiliaryCellWeight u.1 u.2 c.val)) := by
    apply Finset.sum_congr rfl
    intro c _
    exact (YoungDiagram.sum_auxiliaryCellWeight_eq_statistic_div μ
      (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property)).symm
  rw [hstep1]

  rw [Finset.sum_comm]

  have hstep3 : μ.cells.sum (fun u =>
      μ.auxiliaryCellPairFinset.attach.sum (fun c =>
        μ.auxiliaryCellWeight u.1 u.2 c.val)) =
      μ.cells.sum (fun _ => (1 : ℚ)) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_attach]
    exact YoungDiagram.sum_outerCorners_auxiliaryCellWeight_eq_one μ u.1 u.2 hu
  rw [hstep3]

  simp




private lemma hook_quotient_identity
    (n : ℕ) (la : Nat.Partition (n + 1)) :
    la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset.attach.sum (fun c =>
      (la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic : ℚ) /
        (((la.auxiliaryAtOuterCorner c.val
          (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp
            c.property)).auxiliaryYoungDiagramOfPartition
              ).auxiliaryDiagramStatistic)) =
      (n + 1 : ℚ) := by
  have h := YoungDiagram.hook_quotient_identity_yd
    la.auxiliaryYoungDiagramOfPartition
  rw [Partition.card_toYoungDiagram_cells] at h
  simp_rw [Partition.toYoungDiagram_auxiliaryAtOuterCorner]
    at h ⊢
  push_cast at h ⊢
  exact h







/-- Assuming the auxiliary factorial identity at one size, the sum of the auxiliary cardinalities obtained at the outer corners, multiplied by the hook-length product, is the successor factorial. -/
theorem Partition.auxiliaryCornerSum_mul_hookLengthProduct_eq_factorial (n : ℕ) (la : Nat.Partition (n + 1))
    (ih : ∀ la' : Nat.Partition n,
      Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la') *
        la'.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic = n.factorial) :
    la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset.attach.sum (fun c =>
      Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n
        (la.auxiliaryAtOuterCorner c.val
          (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property)))) *
      la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic = (n + 1).factorial := by

  suffices hq : ((la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset.attach.sum (fun c =>
      Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n
        (la.auxiliaryAtOuterCorner c.val
          (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp c.property)))) *
      la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic : ℕ) : ℚ) =
      (((n + 1).factorial : ℕ) : ℚ) by exact_mod_cast hq
  push_cast [Finset.sum_mul]


  have hsummand : ∀ (x : { c // c ∈ la.auxiliaryYoungDiagramOfPartition.auxiliaryCellPairFinset }),
      (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n (la.auxiliaryAtOuterCorner ↑x
        (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp x.property))) : ℚ) *
      (la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic : ℚ) =
      (n.factorial : ℚ) * ((la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic : ℚ) /
        ((la.auxiliaryAtOuterCorner ↑x
          (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp x.property)
            ).auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic : ℚ)) := by
    intro x
    set la' := la.auxiliaryAtOuterCorner ↑x (YoungDiagram.mem_auxiliaryCellPairFinset_iff.mp x.property)
    have ih_c := ih la'
    have hne : (la'.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic : ℚ) ≠ 0 := by
      exact_mod_cast (YoungDiagram.auxiliaryDiagramStatistic_pos la'.auxiliaryYoungDiagramOfPartition).ne'
    have hsyt : (Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la') : ℚ) =
        (n.factorial : ℚ) / (la'.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic : ℚ) := by
      rw [eq_div_iff hne]
      exact_mod_cast ih_c
    rw [hsyt]
    ring
  simp_rw [hsummand]


  rw [← Finset.mul_sum]

  rw [hook_quotient_identity]

  push_cast [Nat.factorial_succ]
  ring





/-- The auxiliary factorial identity for partitions of a given size implies the corresponding identity at the successor size. -/
theorem Partition.auxiliaryFactorialIdentity_succ (n : ℕ)
    (ih : ∀ la' : Nat.Partition n,
      Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la') *
        la'.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic = n.factorial)
    (la : Nat.Partition (n + 1)) :
    Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource (n + 1) la) *
      la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic = (n + 1).factorial := by
  rw [Partition.auxiliaryCard_eq_sum_removeOuterCorner n la]
  exact Partition.auxiliaryCornerSum_mul_hookLengthProduct_eq_factorial n la ih



/-- An auxiliary cardinality associated with a partition, multiplied by its hook-length product, equals its size factorial. -/
theorem Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial (n : ℕ) (la : Nat.Partition n) :
    Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) * la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic =
      n.factorial := by
  induction n with
  | zero => exact Partition.auxiliaryFactorialIdentity_zero la
  | succ n ih => exact Partition.auxiliaryFactorialIdentity_succ n ih la



/-- The hook-length product of a partition divides the factorial of its size. -/
theorem Partition.hookLengthProduct_dvd_factorial (n : ℕ) (la : Nat.Partition n) :
    la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic ∣ n.factorial :=
  ⟨Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la), by linarith [Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial n la]⟩



/-- An auxiliary cardinality associated with a partition equals its size factorial divided by the hook-length product. -/
theorem Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct (n : ℕ) (la : Nat.Partition n) :
    Nat.card (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource n la) =
      n.factorial / la.auxiliaryYoungDiagramOfPartition.auxiliaryDiagramStatistic := by
  have h := Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial n la
  have hpos := YoungDiagram.auxiliaryDiagramStatistic_pos la.auxiliaryYoungDiagramOfPartition
  rw [← h, Nat.mul_div_cancel _ hpos]

end

end RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics

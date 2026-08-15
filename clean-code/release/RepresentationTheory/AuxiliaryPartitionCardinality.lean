/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryPartitionDecomposition

namespace RepresentationTheory.AuxiliaryPartitionCardinality

open RepresentationTheory.AuxiliaryPartitionDecomposition
open RepresentationTheory.PartitionLinearMapVanishing
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.YoungDiagram.PartitionConstructions

/-- An auxiliary type indexed by a natural number and two partitions of that number. -/
noncomputable abbrev auxiliaryFamily
    (n : ℕ) (mu la : Nat.Partition n) :=
  { T : SemistandardYoungTableau (auxiliaryYoungDiagramOfPartition mu) //
    ∀ k : ℕ,
      ((auxiliaryYoungDiagramOfPartition mu).cells.filter
        (fun c => T c.1 c.2 = k)).card =
      (auxiliaryPartitionNatList la).getD k 0 }

/-- The auxiliary cardinal quantity equals the cardinality of the corresponding auxiliary
type. -/
theorem auxiliaryCard_eq_natCard (n : ℕ) (mu la : Nat.Partition n) :
    auxiliaryPartitionPairNat n mu la = Nat.card (auxiliaryFamily n mu la) :=
  rfl

private theorem row_le_entry {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {i j : ℕ} (hcell : (i, j) ∈ mu) :
    i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have habove : (i, j) ∈ mu := mu.up_left_mem (Nat.le_succ i) le_rfl hcell
      exact Nat.succ_le_of_lt
        ((ih habove).trans_lt (T.col_strict (Nat.lt_succ_self i) hcell))

private theorem sum_take_eq_sum_getD (l : List ℕ) (k : ℕ) :
    (l.take k).sum = ∑ i ∈ Finset.range k, l.getD i 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.take_add_one, List.sum_append, ih, Finset.sum_range_succ]
      cases h : l[k]? <;> simp [List.getD_eq_getElem?_getD, h]

private theorem partitionDiagram_rowLen (n : ℕ) (mu : Nat.Partition n) (i : ℕ) :
    (auxiliaryYoungDiagramOfPartition mu).rowLen i =
      (auxiliaryPartitionNatList mu).getD i 0 := by
  have key : ∀ j : ℕ,
      j < (auxiliaryYoungDiagramOfPartition mu).rowLen i ↔
        j < (auxiliaryPartitionNatList mu).getD i 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i, j) ∈
      YoungDiagram.ofRowLens (auxiliaryPartitionNatList mu) _ ↔ _
    rw [YoungDiagram.mem_ofRowLens]
    by_cases hi : i < (auxiliaryPartitionNatList mu).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
    · rw [List.getD_eq_default _ _ (not_lt.mp hi)]
      exact ⟨fun h => (hi h.1).elim, fun h => (Nat.not_lt_zero j h).elim⟩
  have h₁ := key ((auxiliaryYoungDiagramOfPartition mu).rowLen i)
  have h₂ := key ((auxiliaryPartitionNatList mu).getD i 0)
  omega

private theorem sortedParts_length_le (n : ℕ) (la : Nat.Partition n) :
    (auxiliaryPartitionNatList la).length ≤ n := by
  have hsum : (auxiliaryPartitionNatList la).sum = n := by
    have hsort : ((auxiliaryPartitionNatList la : List ℕ) : Multiset ℕ) =
        la.parts :=
      la.parts.sort_eq (· ≥ ·)
    have : (auxiliaryPartitionNatList la).sum = la.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, la.parts_sum]
  have hpos : ∀ x ∈ auxiliaryPartitionNatList la, 1 ≤ x := fun x hx =>
    la.parts_pos ((Multiset.mem_sort _).mp hx)
  exact (List.length_le_sum_of_one_le _ hpos).trans_eq hsum

private theorem entry_lt_succ {n : ℕ} {mu la : Nat.Partition n}
    (T : auxiliaryFamily n mu la) {c : ℕ × ℕ}
    (hc : c ∈ auxiliaryYoungDiagramOfPartition mu) :
    T.1 c.1 c.2 < n + 1 := by
  let k := T.1 c.1 c.2
  have hmem : c ∈
      (auxiliaryYoungDiagramOfPartition mu).cells.filter
        (fun d => T.1 d.1 d.2 = k) := by
    simp [k, hc]
  have hpos : 0 <
      ((auxiliaryYoungDiagramOfPartition mu).cells.filter
        (fun d => T.1 d.1 d.2 = k)).card :=
    Finset.card_pos.mpr ⟨c, hmem⟩
  rw [T.2 k] at hpos
  have hk : k < (auxiliaryPartitionNatList la).length := by
    by_contra h
    rw [List.getD_eq_default _ _ (not_lt.mp h)] at hpos
    omega
  exact lt_of_lt_of_le hk (sortedParts_length_le n la) |>.trans_le (Nat.le_succ n)

/-- Each auxiliary partition-indexed type is finite. -/
noncomputable instance auxiliary_finite
    (n : ℕ) (mu la : Nat.Partition n) : Finite (auxiliaryFamily n mu la) := by
  let encode : auxiliaryFamily n mu la →
      ({c // c ∈ (auxiliaryYoungDiagramOfPartition mu).cells} → Fin (n + 1)) :=
    fun T c => ⟨T.1 c.1.1 c.1.2, entry_lt_succ T c.2⟩
  apply Finite.of_injective encode
  intro T U h
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hc : (i, j) ∈ auxiliaryYoungDiagramOfPartition mu
  · have hij := congrFun h ⟨(i, j), hc⟩
    exact congrArg Fin.val hij
  · rw [T.1.zeros hc, U.1.zeros hc]

/-- An equivalence between the auxiliary partition-indexed type and a finite type of the
corresponding auxiliary cardinality. -/
noncomputable def auxiliaryEquivFin (n : ℕ) (mu la : Nat.Partition n) :
    auxiliaryFamily n mu la ≃ Fin (auxiliaryPartitionPairNat n mu la) := by
  letI := Fintype.ofFinite (auxiliaryFamily n mu la)
  have hcard : Fintype.card (auxiliaryFamily n mu la) =
      auxiliaryPartitionPairNat n mu la := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  exact (Fintype.equivFin (auxiliaryFamily n mu la)).trans
    (Equiv.cast (congrArg Fin hcard))

/-- The number of cells whose auxiliary entry is below a bound equals the sum of the corresponding
initial sorted parts. -/
theorem auxiliaryFamily.auxiliary_card_filter_lt_eq_sum_take
    {n : ℕ} {mu la : Nat.Partition n} (T : auxiliaryFamily n mu la) (k : ℕ) :
    ((auxiliaryYoungDiagramOfPartition mu).cells.filter
      (fun c => T.1 c.1 c.2 < k)).card =
        ((auxiliaryPartitionNatList la).take k).sum := by
  rw [sum_take_eq_sum_getD]
  calc
    ((auxiliaryYoungDiagramOfPartition mu).cells.filter
        (fun c => T.1 c.1 c.2 < k)).card =
      ∑ i ∈ Finset.range k,
        ((auxiliaryYoungDiagramOfPartition mu).cells.filter
          (fun c => T.1 c.1 c.2 = i)).card := by
            simpa only [Finset.mem_range] using
              (Finset.sum_card_fiberwise_eq_card_filter
                (auxiliaryYoungDiagramOfPartition mu).cells
                (Finset.range k) (fun c => T.1 c.1 c.2)).symm
    _ = ∑ i ∈ Finset.range k, (auxiliaryPartitionNatList la).getD i 0 :=
      Finset.sum_congr rfl fun i _ => T.2 i

private theorem card_rows_lt (n : ℕ) (mu : Nat.Partition n) (k : ℕ) :
    ((auxiliaryYoungDiagramOfPartition mu).cells.filter
      (fun c => c.1 < k)).card =
        ((auxiliaryPartitionNatList mu).take k).sum := by
  rw [sum_take_eq_sum_getD]
  calc
    ((auxiliaryYoungDiagramOfPartition mu).cells.filter
        (fun c => c.1 < k)).card =
      ∑ i ∈ Finset.range k,
        ((auxiliaryYoungDiagramOfPartition mu).cells.filter
          (fun c => c.1 = i)).card := by
            simpa only [Finset.mem_range] using
              (Finset.sum_card_fiberwise_eq_card_filter
                (auxiliaryYoungDiagramOfPartition mu).cells
                (Finset.range k) Prod.fst).symm
    _ = ∑ i ∈ Finset.range k,
        (auxiliaryPartitionNatList mu).getD i 0 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        ((auxiliaryYoungDiagramOfPartition mu).cells.filter
            (fun c => c.1 = i)).card =
          ((auxiliaryYoungDiagramOfPartition mu).row i).card := rfl
        _ = (auxiliaryYoungDiagramOfPartition mu).rowLen i :=
          (YoungDiagram.rowLen_eq_card _).symm
        _ = (auxiliaryPartitionNatList mu).getD i 0 :=
          partitionDiagram_rowLen n mu i

/-- The two partitions indexing an auxiliary object satisfy the displayed relation. -/
theorem auxiliaryFamily.auxiliary_relation
    {n : ℕ} {mu la : Nat.Partition n} (T : auxiliaryFamily n mu la) :
    partitionRelation mu la := by
  intro k
  rw [← auxiliary_card_filter_lt_eq_sum_take T k, ← card_rows_lt n mu k]
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, (row_le_entry T.1 hc.1).trans_lt hc.2⟩

/-- The auxiliary cardinal quantity is zero when the displayed partition relation fails. -/
theorem auxiliaryCard_eq_zero_of_not_relation
    (n : ℕ) (mu la : Nat.Partition n) (h : ¬ partitionRelation mu la) :
    auxiliaryPartitionPairNat n mu la = 0 := by
  rw [auxiliaryCard_eq_natCard, Nat.card_eq_zero]
  left
  exact ⟨fun T => h T.auxiliary_relation⟩

private theorem highestWeight_has_diagonal_content
    (n : ℕ) (mu : Nat.Partition n) :
    ∀ k : ℕ,
      ((auxiliaryYoungDiagramOfPartition mu).cells.filter
        (fun c => SemistandardYoungTableau.highestWeight
          (auxiliaryYoungDiagramOfPartition mu) c.1 c.2 = k)).card =
        (auxiliaryPartitionNatList mu).getD k 0 := by
  intro k
  calc
    ((auxiliaryYoungDiagramOfPartition mu).cells.filter
        (fun c => SemistandardYoungTableau.highestWeight
          (auxiliaryYoungDiagramOfPartition mu) c.1 c.2 = k)).card =
      ((auxiliaryYoungDiagramOfPartition mu).row k).card := by
        congr 1
        ext c
        simp only [Finset.mem_filter, YoungDiagram.mem_cells,
          SemistandardYoungTableau.highestWeight_apply,
          YoungDiagram.mem_row_iff]
        constructor
        · rintro ⟨hc, hk⟩
          rw [if_pos hc] at hk
          exact ⟨hc, hk⟩
        · rintro ⟨hc, hk⟩
          exact ⟨hc, by rw [if_pos hc]; exact hk⟩
    _ = (auxiliaryYoungDiagramOfPartition mu).rowLen k :=
      (YoungDiagram.rowLen_eq_card _).symm
    _ = (auxiliaryPartitionNatList mu).getD k 0 :=
      partitionDiagram_rowLen n mu k

private theorem eq_highestWeight_of_diagonal_content
    {n : ℕ} {mu : Nat.Partition n} (T : auxiliaryFamily n mu mu) :
    T.1 = SemistandardYoungTableau.highestWeight
      (auxiliaryYoungDiagramOfPartition mu) := by
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hcell : (i, j) ∈ auxiliaryYoungDiagramOfPartition mu
  · let entries := (auxiliaryYoungDiagramOfPartition mu).cells.filter
      (fun c => T.1 c.1 c.2 < i + 1)
    let rows := (auxiliaryYoungDiagramOfPartition mu).cells.filter
      (fun c => c.1 < i + 1)
    have hsubset : entries ⊆ rows := by
      intro c hc
      simp only [entries, rows, Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, (row_le_entry T.1 hc.1).trans_lt hc.2⟩
    have hcard : rows.card ≤ entries.card := by
      rw [T.auxiliary_card_filter_lt_eq_sum_take (i + 1),
        card_rows_lt n mu (i + 1)]
    have heq : entries = rows := Finset.eq_of_subset_of_card_le hsubset hcard
    have hrow : (i, j) ∈ rows := by simp [rows, hcell]
    have hlt : T.1 i j < i + 1 := by
      have : (i, j) ∈ entries := heq.symm ▸ hrow
      have hmem :
          (i, j) ∈ (auxiliaryYoungDiagramOfPartition mu).cells ∧
            T.1 i j < i + 1 := by
        simpa [entries] using this
      exact hmem.2
    rw [SemistandardYoungTableau.highestWeight_apply, if_pos hcell]
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) (row_le_entry T.1 hcell)
  · rw [T.1.zeros hcell,
      SemistandardYoungTableau.highestWeight_apply, if_neg hcell]

/-- The auxiliary cardinal quantity for a partition paired with itself is one. -/
theorem auxiliaryCard_self (n : ℕ) (mu : Nat.Partition n) :
    auxiliaryPartitionPairNat n mu mu = 1 := by
  rw [auxiliaryCard_eq_natCard, Nat.card_eq_one_iff_unique]
  constructor
  · constructor
    intro T U
    exact Subtype.ext
      ((eq_highestWeight_of_diagonal_content T).trans
        (eq_highestWeight_of_diagonal_content U).symm)
  · exact ⟨⟨SemistandardYoungTableau.highestWeight
      (auxiliaryYoungDiagramOfPartition mu),
        highestWeight_has_diagonal_content n mu⟩⟩

/-- When the displayed relation fails, the displayed auxiliary natural-number value equals the
auxiliary cardinal quantity. -/
theorem auxiliary_nat_value_eq_auxiliaryCard_of_not_relation
    (n : ℕ) (mu nu : Nat.Partition n)
    (h : ¬ partitionRelation nu mu) :
    auxiliaryNatValue n mu nu = auxiliaryPartitionPairNat n nu mu := by
  rw [auxiliaryNatValue_eq_zero_of_not_relation n mu nu h,
    auxiliaryCard_eq_zero_of_not_relation n nu mu h]

/-- On a diagonal pair of partitions, the displayed auxiliary natural-number value equals the
auxiliary cardinal quantity. -/
theorem auxiliary_nat_value_self_eq_auxiliaryCard
    (n : ℕ) (mu : Nat.Partition n) :
    auxiliaryNatValue n mu mu = auxiliaryPartitionPairNat n mu mu := by
  rw [auxiliaryNatValue_self, auxiliaryCard_self]

end RepresentationTheory.AuxiliaryPartitionCardinality

import EtingofRepresentationTheory.Chapter5.YoungRuleInvariantBridge

/-!
# The semistandard-tableau basis in Young's rule

This file constructs the semistandard basis of the row-invariant subspace left by
`YoungRuleInvariantBridge`.  The first step is canonical standardization: order the
cells lexicographically by tableau entry, row, and column, and replace them by their
ranks in that order.
-/

namespace Etingof

noncomputable section

/-- A cell of `nu`, carrying the tableau-dependent lexicographic order used for
standardization. -/
private def KostkaOrderedCell {n : ℕ} {nu mu : Nat.Partition n}
    (_T : KostkaTableau n nu mu) := Cell n nu

private noncomputable instance kostkaOrderedCellFintype
    {n : ℕ} {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) :
    Fintype (KostkaOrderedCell T) :=
  cellFintype n nu

private def kostkaOrderedCellOfCell {n : ℕ} {nu mu : Nat.Partition n}
    (T : KostkaTableau n nu mu) (c : Cell n nu) : KostkaOrderedCell T :=
  ⟨c.1, c.2⟩

private def kostkaCellKey {n : ℕ} {nu mu : Nat.Partition n}
    (T : KostkaTableau n nu mu) (c : KostkaOrderedCell T) :
    ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (T.1 c.1.1 c.1.2, toLex (c.1.1, c.1.2))

private theorem kostkaCellKey_injective {n : ℕ} {nu mu : Nat.Partition n}
    (T : KostkaTableau n nu mu) : Function.Injective (kostkaCellKey T) := by
  intro c d h
  apply Subtype.ext
  have hpair : (c.1.1, c.1.2) = (d.1.1, d.1.2) := by
    exact congrArg (fun x : ℕ ×ₗ (ℕ ×ₗ ℕ) => ofLex (ofLex x).2) h
  exact hpair

private noncomputable instance kostkaOrderedCellLinearOrder
    {n : ℕ} {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) :
    LinearOrder (KostkaOrderedCell T) :=
  LinearOrder.lift' (kostkaCellKey T) (kostkaCellKey_injective T)

private theorem card_kostkaOrderedCell {n : ℕ} {nu mu : Nat.Partition n}
    (T : KostkaTableau n nu mu) : Fintype.card (KostkaOrderedCell T) = n := by
  simpa only [KostkaOrderedCell, Fintype.card_fin] using
    (Fintype.card_congr (canonicalFilling n nu)).symm

/-- A cell in the `StandardYoungTableau` presentation belongs to the Young diagram. -/
private theorem cell_mem_partitionDiagram {n : ℕ} {nu : Nat.Partition n}
    (c : Cell n nu) : c.1 ∈ nu.toYoungDiagram := by
  change c.1 ∈ YoungDiagram.ofRowLens nu.sortedParts _
  rw [YoungDiagram.mem_ofRowLens]
  refine ⟨c.2.1, ?_⟩
  have hc := c.2.2
  rw [List.getD_eq_getElem _ _ c.2.1] at hc
  exact hc

/-- The increasing rank of a cell in the tableau-entry/row/column lexicographic
order. -/
private noncomputable def kostkaCellOrderIso {n : ℕ} {nu mu : Nat.Partition n}
    (T : KostkaTableau n nu mu) : Fin n ≃o KostkaOrderedCell T :=
  Fintype.orderIsoFinOfCardEq (KostkaOrderedCell T) (card_kostkaOrderedCell T)

/-- Canonical standardization of a semistandard tableau: equal entries are numbered
from left to right, with earlier rows first. -/
noncomputable def KostkaTableau.standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) :
    StandardYoungTableau n nu := by
  let e := kostkaCellOrderIso T
  let rank : Cell n nu → Fin n := fun c =>
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
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (c d : Cell n nu) :
    T.standardization.1 c < T.standardization.1 d ↔
      kostkaCellKey T (kostkaOrderedCellOfCell T c) <
        kostkaCellKey T (kostkaOrderedCellOfCell T d) := by
  change (kostkaCellOrderIso T).symm (kostkaOrderedCellOfCell T c) <
      (kostkaCellOrderIso T).symm (kostkaOrderedCellOfCell T d) ↔ _
  exact (kostkaCellOrderIso T).symm.lt_iff_lt

/-- Standardization orders every cell with a smaller semistandard entry first. -/
theorem KostkaTableau.standardization_lt_of_entry_lt {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (c d : Cell n nu)
    (h : T.1 c.1.1 c.1.2 < T.1 d.1.1 d.1.2) :
    T.standardization.1 c < T.standardization.1 d := by
  rw [KostkaTableau.standardization_lt_iff_key_lt T]
  simp only [kostkaCellKey, kostkaOrderedCellOfCell, Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- A cell preceding another in the standardization cannot have a larger
semistandard entry. -/
theorem KostkaTableau.entry_le_of_standardization_le {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (c d : Cell n nu)
    (h : T.standardization.1 c ≤ T.standardization.1 d) :
    T.1 c.1.1 c.1.2 ≤ T.1 d.1.1 d.1.2 := by
  by_contra hnot
  have hdc : T.1 d.1.1 d.1.2 < T.1 c.1.1 c.1.2 := Nat.lt_of_not_ge hnot
  exact (not_lt_of_ge h) (KostkaTableau.standardization_lt_of_entry_lt T d c hdc)

private theorem mem_partitionDiagram_iff_cell_condition {n : ℕ}
    {nu : Nat.Partition n} (c : ℕ × ℕ) :
    c ∈ nu.toYoungDiagram ↔
      c.1 < nu.sortedParts.length ∧ c.2 < nu.sortedParts.getD c.1 0 := by
  change c ∈ YoungDiagram.ofRowLens nu.sortedParts _ ↔ _
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
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (k : ℕ) :
    ((Finset.univ : Finset (Cell n nu)).filter
      (fun c => T.1 c.1.1 c.1.2 < k)).card =
      (mu.sortedParts.take k).sum := by
  rw [← KostkaTableau.card_entries_lt T k]
  let s := (Finset.univ : Finset (Cell n nu)).filter
    (fun c => T.1 c.1.1 c.1.2 < k)
  calc
    s.card = (s.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = (nu.toYoungDiagram.cells.filter (fun c => T.1 c.1 c.2 < k)).card := by
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
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (c : Cell n nu) :
    (mu.sortedParts.take (T.1 c.1.1 c.1.2)).sum ≤
      (T.standardization.1 c).val := by
  let s := (Finset.univ : Finset (Cell n nu)).filter
    (fun d => T.1 d.1.1 d.1.2 < T.1 c.1.1 c.1.2)
  have hmaps : Set.MapsTo (fun d => T.standardization.1 d)
      (↑s : Set (Cell n nu)) (↑(Finset.Iio (T.standardization.1 c)) : Set (Fin n)) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    rw [Finset.mem_coe, Finset.mem_Iio]
    exact KostkaTableau.standardization_lt_of_entry_lt T d c hd.2
  have hinj : Set.InjOn (fun d => T.standardization.1 d) (↑s : Set (Cell n nu)) :=
    T.standardization.2.1.1.injOn
  have hcard := Finset.card_le_card_of_injOn
    (fun d => T.standardization.1 d) hmaps hinj
  rw [show s.card = (mu.sortedParts.take (T.1 c.1.1 c.1.2)).sum by
      exact KostkaTableau.card_cells_entry_lt T _, Fin.card_Iio] at hcard
  exact hcard

private theorem KostkaTableau.standardization_lt_nextPrefix {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (c : Cell n nu) :
    (T.standardization.1 c).val <
      (mu.sortedParts.take (T.1 c.1.1 c.1.2 + 1)).sum := by
  let s := (Finset.univ : Finset (Cell n nu)).filter
    (fun d => T.standardization.1 d ≤ T.standardization.1 c)
  let u := (Finset.univ : Finset (Cell n nu)).filter
    (fun d => T.1 d.1.1 d.1.2 < T.1 c.1.1 c.1.2 + 1)
  have hsubset : s ⊆ u := by
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hentry := KostkaTableau.entry_le_of_standardization_le T d c hd.2
    omega
  have himage : s.image (fun d => T.standardization.1 d) =
      Finset.Iic (T.standardization.1 c) := by
    ext i
    constructor
    · intro hi
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_Iic.mpr (Finset.mem_filter.mp hd).2
    · intro hi
      obtain ⟨d, hd⟩ := T.standardization.2.1.2 i
      apply Finset.mem_image.mpr
      refine ⟨d, ?_, hd⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hd ▸ Finset.mem_Iic.mp hi⟩
  have hscard : s.card = (T.standardization.1 c).val + 1 := by
    calc
      s.card = (s.image (fun d => T.standardization.1 d)).card :=
        (Finset.card_image_of_injective _ T.standardization.2.1.1).symm
      _ = (Finset.Iic (T.standardization.1 c)).card := congrArg Finset.card himage
      _ = (T.standardization.1 c).val + 1 := Fin.card_Iic _
  have hcard := Finset.card_le_card hsubset
  rw [hscard, show u.card =
      (mu.sortedParts.take (T.1 c.1.1 c.1.2 + 1)).sum by
        exact KostkaTableau.card_cells_entry_lt T _] at hcard
  omega

/-- Canonical standardization puts precisely the cells carrying entry `i` into
the `i`-th row block of the Young subgroup belonging to the content. -/
theorem KostkaTableau.rowOfPos_standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) (c : Cell n nu) :
    rowOfPos mu.sortedParts (T.standardization.1 c).val =
      T.1 c.1.1 c.1.2 := by
  let k := T.1 c.1.1 c.1.2
  have hsum : mu.sortedParts.sum = n := by
    have hsort : (mu.sortedParts : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : mu.sortedParts.sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  have hj : (T.standardization.1 c).val < mu.sortedParts.sum := by
    rw [hsum]
    exact (T.standardization.1 c).isLt
  have hbelowNext : rowOfPos mu.sortedParts (T.standardization.1 c).val < k + 1 :=
    (rowOfPos_lt_iff mu.sortedParts _ _ hj).mpr
      (KostkaTableau.standardization_lt_nextPrefix T c)
  have hnotBelow : ¬rowOfPos mu.sortedParts (T.standardization.1 c).val < k := by
    rw [rowOfPos_lt_iff mu.sortedParts _ _ hj]
    exact Nat.not_lt_of_ge (KostkaTableau.prefix_le_standardization T c)
  omega

end

end Etingof

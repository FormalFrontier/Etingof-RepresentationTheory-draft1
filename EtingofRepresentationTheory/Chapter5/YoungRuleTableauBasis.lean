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

private theorem card_positions_rowOfPos_lt {n : ℕ} (mu : Nat.Partition n) (k : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun i => rowOfPos mu.sortedParts i.val < k)).card =
      (mu.sortedParts.take k).sum := by
  have hsum : mu.sortedParts.sum = n := by
    have hsort : (mu.sortedParts : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : mu.sortedParts.sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  have hfilter : (Finset.univ : Finset (Fin n)).filter
      (fun i => rowOfPos mu.sortedParts i.val < k) =
      Finset.univ.filter (fun i : Fin n => i.val < (mu.sortedParts.take k).sum) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact rowOfPos_lt_iff mu.sortedParts i.val k (by rw [hsum]; exact i.isLt)
  rw [hfilter]
  apply card_filter_val_lt
  have hle : (mu.sortedParts.take k).sum ≤ mu.sortedParts.sum :=
    List.Sublist.sum_le_sum (List.take_sublist k mu.sortedParts) (fun _ _ => Nat.zero_le _)
  omega

private theorem take_succ_sum (l : List ℕ) (k : ℕ) :
    (l.take (k + 1)).sum = (l.take k).sum + l.getD k 0 := by
  rw [List.take_add_one, List.sum_append]
  cases h : l[k]? <;> simp [List.getD_eq_getElem?_getD, h]

/-- Exactly `mu[k]` labels lie in the `k`-th row block of the Young subgroup. -/
theorem card_positions_rowOfPos_eq {n : ℕ} (mu : Nat.Partition n) (k : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun i => rowOfPos mu.sortedParts i.val = k)).card =
      mu.sortedParts.getD k 0 := by
  let below := (Finset.univ : Finset (Fin n)).filter
    (fun i => rowOfPos mu.sortedParts i.val < k)
  let fiber := (Finset.univ : Finset (Fin n)).filter
    (fun i => rowOfPos mu.sortedParts i.val = k)
  let belowNext := (Finset.univ : Finset (Fin n)).filter
    (fun i => rowOfPos mu.sortedParts i.val < k + 1)
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
  rw [show below.card = (mu.sortedParts.take k).sum by
      exact card_positions_rowOfPos_lt mu k,
    show belowNext.card = (mu.sortedParts.take (k + 1)).sum by
      exact card_positions_rowOfPos_lt mu (k + 1), take_succ_sum] at hcard
  change fiber.card = _
  exact Nat.add_left_cancel hcard

private theorem rowOfPos_mono_valid (parts : List ℕ) (a b : ℕ)
    (ha : a < parts.sum) (hb : b < parts.sum) (hab : a ≤ b) :
    rowOfPos parts a ≤ rowOfPos parts b := by
  by_contra hnot
  have hlt : rowOfPos parts b < rowOfPos parts a := Nat.lt_of_not_ge hnot
  let k := rowOfPos parts b + 1
  have hbPrefix : b < (parts.take k).sum :=
    (rowOfPos_lt_iff parts b k hb).mp (by simp [k])
  have haPrefix : a < (parts.take k).sum := hab.trans_lt hbPrefix
  have haRow : rowOfPos parts a < k :=
    (rowOfPos_lt_iff parts a k ha).mpr haPrefix
  omega

private def partitionCellOfMem {n : ℕ} {nu : Nat.Partition n}
    (c : ℕ × ℕ) (hc : c ∈ nu.toYoungDiagram) : Cell n nu :=
  ⟨c, (mem_partitionDiagram_iff_cell_condition c).mp hc⟩

/-- Replace each entry of a standard tableau by the row block containing that
entry in the content partition. -/
noncomputable def StandardYoungTableau.contentCollapse {n : ℕ}
    {nu : Nat.Partition n} (mu : Nat.Partition n) (S : StandardYoungTableau n nu)
    (i j : ℕ) : ℕ :=
  if h : (i, j) ∈ nu.toYoungDiagram then
    rowOfPos mu.sortedParts (S.1 (partitionCellOfMem (i, j) h)).val
  else 0

@[simp] theorem StandardYoungTableau.contentCollapse_of_mem {n : ℕ}
    {nu : Nat.Partition n} (mu : Nat.Partition n) (S : StandardYoungTableau n nu)
    {i j : ℕ} (h : (i, j) ∈ nu.toYoungDiagram) :
    S.contentCollapse mu i j =
      rowOfPos mu.sortedParts (S.1 (partitionCellOfMem (i, j) h)).val := by
  simp only [StandardYoungTableau.contentCollapse, dif_pos h]

/-- The nonautomatic condition in collapsing a standard tableau: no column
contains two labels belonging to the same content block. -/
def StandardYoungTableau.ContentCollapseColumnStrict {n : ℕ}
    {nu : Nat.Partition n} (mu : Nat.Partition n) (S : StandardYoungTableau n nu) : Prop :=
  ∀ c₁ c₂ : Cell n nu, c₁.1.2 = c₂.1.2 → c₁.1.1 < c₂.1.1 →
    rowOfPos mu.sortedParts (S.1 c₁).val < rowOfPos mu.sortedParts (S.1 c₂).val

/-- If a standard tableau has no repeated content block in a column, collapsing
its labels produces a semistandard tableau with exactly the prescribed content. -/
noncomputable def StandardYoungTableau.toKostkaTableauOfContentCollapseColumnStrict
    {n : ℕ} {nu mu : Nat.Partition n} (S : StandardYoungTableau n nu)
    (hstrict : S.ContentCollapseColumnStrict mu) : KostkaTableau n nu mu := by
  let entry := S.contentCollapse mu
  have hsum : mu.sortedParts.sum = n := by
    have hsort : (mu.sortedParts : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : mu.sortedParts.sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  let T : SemistandardYoungTableau nu.toYoungDiagram := {
    entry := entry
    row_weak' := by
      intro i j₁ j₂ hj hcell₂
      have hcell₁ := nu.toYoungDiagram.up_left_mem le_rfl (Nat.le_of_lt hj) hcell₂
      rw [show entry i j₁ = S.contentCollapse mu i j₁ from rfl,
        S.contentCollapse_of_mem mu hcell₁,
        show entry i j₂ = S.contentCollapse mu i j₂ from rfl,
        S.contentCollapse_of_mem mu hcell₂]
      apply rowOfPos_mono_valid mu.sortedParts
      · rw [hsum]; exact (S.1 _).isLt
      · rw [hsum]; exact (S.1 _).isLt
      · exact le_of_lt (S.2.2.1 _ _ rfl hj)
    col_strict' := by
      intro i₁ i₂ j hi hcell₂
      have hcell₁ := nu.toYoungDiagram.up_left_mem (Nat.le_of_lt hi) le_rfl hcell₂
      rw [show entry i₁ j = S.contentCollapse mu i₁ j from rfl,
        S.contentCollapse_of_mem mu hcell₁,
        show entry i₂ j = S.contentCollapse mu i₂ j from rfl,
        S.contentCollapse_of_mem mu hcell₂]
      exact hstrict _ _ rfl hi
    zeros' := by
      intro i j hcell
      simp only [entry, StandardYoungTableau.contentCollapse, dif_neg hcell]
  }
  refine ⟨T, ?_⟩
  intro k
  let source := nu.toYoungDiagram.cells.filter (fun c => T c.1 c.2 = k)
  let target := (Finset.univ : Finset (Fin n)).filter
    (fun x => rowOfPos mu.sortedParts x.val = k)
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
        rw [show entry c.1 c.2 = S.contentCollapse mu c.1 c.2 from rfl,
          S.contentCollapse_of_mem mu hc'] at hvalue
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
          rw [show entry c.1.1 c.1.2 = S.contentCollapse mu c.1.1 c.1.2 from rfl,
            S.contentCollapse_of_mem mu (cell_mem_partitionDiagram c)]
          have hcellEq : partitionCellOfMem c.1 (cell_mem_partitionDiagram c) = c :=
            Subtype.ext rfl
          rw [hcellEq, hc]
          have hx' := (Finset.mem_filter.mp hx).2
          exact hx'
        · simpa only [partitionCellOfMem] using hc
    _ = mu.sortedParts.getD k 0 := card_positions_rowOfPos_eq mu k

@[simp] theorem StandardYoungTableau.toKostkaTableauOfContentCollapseColumnStrict_apply
    {n : ℕ} {nu mu : Nat.Partition n} (S : StandardYoungTableau n nu)
    (hstrict : S.ContentCollapseColumnStrict mu) (c : Cell n nu) :
    (S.toKostkaTableauOfContentCollapseColumnStrict hstrict).1.1 c.1.1 c.1.2 =
      rowOfPos mu.sortedParts (S.1 c).val := by
  rw [StandardYoungTableau.toKostkaTableauOfContentCollapseColumnStrict]
  change S.contentCollapse mu c.1.1 c.1.2 = _
  rw [S.contentCollapse_of_mem mu (cell_mem_partitionDiagram c)]
  congr 1

/-- The permutation of a standard tableau sends its entry at a cell to the
canonical position of that cell. -/
theorem sytPerm_apply_tableauEntry {n : ℕ} {nu : Nat.Partition n}
    (S : StandardYoungTableau n nu) (c : Cell n nu) :
    sytPerm n nu S (S.1 c) = (canonicalFilling n nu).symm c := by
  let e : Cell n nu ≃ Fin n := Equiv.ofBijective S.1 S.2.1
  change (canonicalFilling n nu).symm (e.symm (e c)) = _
  rw [e.symm_apply_apply]

private theorem sytPerm_inv_apply_canonical {n : ℕ} {nu : Nat.Partition n}
    (S : StandardYoungTableau n nu) (c : Cell n nu) :
    (sytPerm n nu S)⁻¹ ((canonicalFilling n nu).symm c) = S.1 c := by
  rw [← sytPerm_apply_tableauEntry S c]
  exact (sytPerm n nu S).symm_apply_apply (S.1 c)

private theorem contentCollapse_relabel_mem_rowSubgroup {n : ℕ}
    {nu mu : Nat.Partition n} (S : StandardYoungTableau n nu)
    (hstrict : S.ContentCollapseColumnStrict mu) :
    (sytPerm n nu
        (S.toKostkaTableauOfContentCollapseColumnStrict hstrict).standardization)⁻¹ *
        sytPerm n nu S ∈ RowSubgroup n mu := by
  let U := S.toKostkaTableauOfContentCollapseColumnStrict hstrict
  let V := U.standardization
  let p := (sytPerm n nu V)⁻¹ * sytPerm n nu S
  change p ∈ RowSubgroup n mu
  intro x
  let eS : Cell n nu ≃ Fin n := Equiv.ofBijective S.1 S.2.1
  let c : Cell n nu := eS.symm x
  have hS : S.1 c = x := eS.apply_symm_apply x
  change rowOfPos mu.sortedParts (p x).val = rowOfPos mu.sortedParts x.val
  simp only [p, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [← hS, sytPerm_apply_tableauEntry S c,
    sytPerm_inv_apply_canonical V c]
  change rowOfPos mu.sortedParts (U.standardization.1 c).val = _
  rw [KostkaTableau.rowOfPos_standardization U c]
  change (S.toKostkaTableauOfContentCollapseColumnStrict hstrict).1.1 c.1.1 c.1.2 = _
  rw [S.toKostkaTableauOfContentCollapseColumnStrict_apply hstrict c, hS]

/-- The invariant vector canonically attached to a semistandard tableau. -/
noncomputable def youngRuleSemistandardVector (n : ℕ)
    (mu nu : Nat.Partition n) (T : KostkaTableau n nu mu) :
    YoungRuleRowInvariants n mu nu :=
  youngRuleAveragedPolytabloid n mu nu T.standardization

/-- In the column-strict case, row averaging depends only on the collapsed
semistandard tableau, not on the ordering of labels inside content blocks. -/
theorem youngRuleAveragedPolytabloid_eq_semistandardVector_of_columnStrict
    (n : ℕ) (mu nu : Nat.Partition n) (S : StandardYoungTableau n nu)
    (hstrict : S.ContentCollapseColumnStrict mu) :
    youngRuleAveragedPolytabloid n mu nu S =
      youngRuleSemistandardVector n mu nu
        (S.toKostkaTableauOfContentCollapseColumnStrict hstrict) := by
  let U := S.toKostkaTableauOfContentCollapseColumnStrict hstrict
  let V := U.standardization
  let p := (sytPerm n nu V)⁻¹ * sytPerm n nu S
  have hp : p ∈ RowSubgroup n mu :=
    contentCollapse_relabel_mem_rowSubgroup S hstrict
  have hpEq : p * (sytPerm n nu S)⁻¹ = (sytPerm n nu V)⁻¹ := by
    simp only [p]
    group
  have hrow : RowSymmetrizer n mu *
        MonoidAlgebra.of ℂ _ (sytPerm n nu S)⁻¹ =
      RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ (sytPerm n nu V)⁻¹ := by
    calc
      RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ (sytPerm n nu S)⁻¹ =
          (RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ p) *
            MonoidAlgebra.of ℂ _ (sytPerm n nu S)⁻¹ := by
              rw [RowSymmetrizer_mul_of_row p hp]
      _ = RowSymmetrizer n mu *
          (MonoidAlgebra.of ℂ _ p * MonoidAlgebra.of ℂ _ (sytPerm n nu S)⁻¹) := by
            rw [mul_assoc]
      _ = RowSymmetrizer n mu * MonoidAlgebra.of ℂ _
          (p * (sytPerm n nu S)⁻¹) := by
            congr 1
            exact ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))).map_mul
              p (sytPerm n nu S)⁻¹).symm
      _ = RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ (sytPerm n nu V)⁻¹ := by
        rw [hpEq]
  apply Subtype.ext
  change (youngRuleRowAverage n mu nu (spechtPolytabloid S) :
      SpechtModule n nu) = youngRuleRowAverage n mu nu (spechtPolytabloid V)
  apply Subtype.ext
  change (Nat.card (↥(RowSubgroup n mu)) : ℂ)⁻¹ •
      (RowSymmetrizer n mu *
        ((Nat.card (↥(RowSubgroup n nu)) : ℂ)⁻¹ •
          MonoidAlgebra.of ℂ _ (sytPerm n nu S)⁻¹ * YoungSymmetrizer n nu)) =
    (Nat.card (↥(RowSubgroup n mu)) : ℂ)⁻¹ •
      (RowSymmetrizer n mu *
        ((Nat.card (↥(RowSubgroup n nu)) : ℂ)⁻¹ •
          MonoidAlgebra.of ℂ _ (sytPerm n nu V)⁻¹ * YoungSymmetrizer n nu))
  simp only [Algebra.mul_smul_comm, smul_mul_assoc]
  rw [← mul_assoc, ← mul_assoc, hrow]

private theorem swap_mem_rowSubgroup_of_same_row {n : ℕ} {mu : Nat.Partition n}
    {a b : Fin n}
    (hrow : rowOfPos mu.sortedParts a.val = rowOfPos mu.sortedParts b.val) :
    Equiv.swap a b ∈ RowSubgroup n mu := by
  intro x
  simp only [Equiv.swap_apply_def]
  split_ifs with ha hb
  · subst ha; exact hrow.symm
  · subst hb; exact hrow
  · rfl

private theorem swap_mem_columnSubgroup_of_same_col {n : ℕ} {nu : Nat.Partition n}
    {a b : Fin n}
    (hcol : colOfPos nu.sortedParts a.val = colOfPos nu.sortedParts b.val) :
    Equiv.swap a b ∈ ColumnSubgroup n nu := by
  intro x
  simp only [Equiv.swap_apply_def]
  split_ifs with ha hb
  · subst ha; exact hcol.symm
  · subst hb; exact hcol
  · rfl

private theorem colOfPos_canonical_symm {n : ℕ} {nu : Nat.Partition n}
    (c : Cell n nu) :
    colOfPos nu.sortedParts ((canonicalFilling n nu).symm c).val = c.1.2 := by
  have h := (canonicalFilling n nu).apply_symm_apply c
  have hval := congrArg (fun d : Cell n nu => d.1.2) h
  simpa only [canonicalFilling, canonicalFillingFun, Equiv.ofBijective_apply] using hval

/-- The row of the canonical position of a cell is its row coordinate. -/
theorem rowOfPos_canonical_symm {n : ℕ} {nu : Nat.Partition n}
    (c : Cell n nu) :
    rowOfPos nu.sortedParts ((canonicalFilling n nu).symm c).val = c.1.1 := by
  have h := (canonicalFilling n nu).apply_symm_apply c
  have hval := congrArg (fun d : Cell n nu => d.1.1) h
  simpa only [canonicalFilling, canonicalFillingFun, Equiv.ofBijective_apply] using hval

private theorem of_col_mul_youngSymmetrizer {n : ℕ} {nu : Nat.Partition n}
    (q : Equiv.Perm (Fin n)) (hq : q ∈ ColumnSubgroup n nu) :
    MonoidAlgebra.of ℂ _ q * YoungSymmetrizer n nu =
      ((↑(↑(Equiv.Perm.sign q) : ℤ) : ℂ)) • YoungSymmetrizer n nu := by
  change MonoidAlgebra.of ℂ _ q *
      (ColumnAntisymmetrizer n nu * RowSymmetrizer n nu) =
    _ • (ColumnAntisymmetrizer n nu * RowSymmetrizer n nu)
  rw [← mul_assoc, of_col_mul_ColumnAntisymmetrizer q hq,
    Algebra.smul_mul_assoc]

private theorem contentCollapse_not_columnStrict_data {n : ℕ}
    {nu mu : Nat.Partition n} (S : StandardYoungTableau n nu)
    (hnot : ¬S.ContentCollapseColumnStrict mu) :
    ∃ c₁ c₂ : Cell n nu,
      c₁.1.2 = c₂.1.2 ∧ c₁.1.1 < c₂.1.1 ∧
      rowOfPos mu.sortedParts (S.1 c₁).val =
        rowOfPos mu.sortedParts (S.1 c₂).val := by
  rw [StandardYoungTableau.ContentCollapseColumnStrict] at hnot
  push Not at hnot
  obtain ⟨c₁, c₂, hcol, hrow, hnotlt⟩ := hnot
  refine ⟨c₁, c₂, hcol, hrow, ?_⟩
  have hsum : mu.sortedParts.sum = n := by
    have hsort : (mu.sortedParts : Multiset ℕ) = mu.parts :=
      mu.parts.sort_eq (· ≥ ·)
    have : mu.sortedParts.sum = mu.parts.sum := by
      rw [← Multiset.sum_coe, hsort]
    rw [this, mu.parts_sum]
  have hlabel : S.1 c₁ < S.1 c₂ := S.2.2.2 c₁ c₂ hcol hrow
  have hle := rowOfPos_mono_valid mu.sortedParts
    (S.1 c₁).val (S.1 c₂).val
    (by rw [hsum]; exact (S.1 c₁).isLt)
    (by rw [hsum]; exact (S.1 c₂).isLt) (le_of_lt hlabel)
  exact le_antisymm hle hnotlt

/-- If two labels from one content block occur in a single column, their
row-subgroup transposition acts by `-1`; hence the Reynolds average vanishes. -/
theorem youngRuleAveragedPolytabloid_eq_zero_of_not_columnStrict
    (n : ℕ) (mu nu : Nat.Partition n) (S : StandardYoungTableau n nu)
    (hnot : ¬S.ContentCollapseColumnStrict mu) :
    youngRuleAveragedPolytabloid n mu nu S = 0 := by
  obtain ⟨c₁, c₂, hcol, hrow, hblock⟩ :=
    contentCollapse_not_columnStrict_data S hnot
  let σ := sytPerm n nu S
  let a := S.1 c₁
  let b := S.1 c₂
  let p := Equiv.swap a b
  let q := σ * p * σ⁻¹
  have hab : a ≠ b := ne_of_lt (S.2.2.2 c₁ c₂ hcol hrow)
  have hp : p ∈ RowSubgroup n mu :=
    swap_mem_rowSubgroup_of_same_row hblock
  have hcell : c₁ ≠ c₂ := by
    intro heq
    rw [heq] at hrow
    omega
  have hpos : (canonicalFilling n nu).symm c₁ ≠
      (canonicalFilling n nu).symm c₂ := by
    intro heq
    exact hcell ((canonicalFilling n nu).symm.injective heq)
  have hqEq : q = Equiv.swap ((canonicalFilling n nu).symm c₁)
      ((canonicalFilling n nu).symm c₂) := by
    calc
      q = Equiv.swap (σ a) (σ b) := by
        have h := Equiv.trans_swap_trans_symm a b σ.symm
        change σ * Equiv.swap a b * σ⁻¹ = Equiv.swap (σ a) (σ b) at h
        exact h
      _ = _ := by
        rw [show σ a = (canonicalFilling n nu).symm c₁ by
              exact sytPerm_apply_tableauEntry S c₁,
          show σ b = (canonicalFilling n nu).symm c₂ by
              exact sytPerm_apply_tableauEntry S c₂]
  have hq : q ∈ ColumnSubgroup n nu := by
    rw [hqEq]
    apply swap_mem_columnSubgroup_of_same_col
    rw [colOfPos_canonical_symm c₁, colOfPos_canonical_symm c₂]
    exact hcol
  have hsign : Equiv.Perm.sign q = -1 := by
    rw [hqEq, Equiv.Perm.sign_swap hpos]
  have hqAction : MonoidAlgebra.of ℂ _ q * YoungSymmetrizer n nu =
      (-1 : ℂ) • YoungSymmetrizer n nu := by
    rw [of_col_mul_youngSymmetrizer q hq, hsign]
    norm_num
  have hpEq : p * σ⁻¹ = σ⁻¹ * q := by
    simp only [q]
    group
  let A : SymGroupAlgebra n :=
    RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ σ⁻¹ * YoungSymmetrizer n nu
  have hAneg : A = -A := by
    calc
      A = (RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ p) *
          MonoidAlgebra.of ℂ _ σ⁻¹ * YoungSymmetrizer n nu := by
            rw [RowSymmetrizer_mul_of_row p hp]
      _ = RowSymmetrizer n mu *
          (MonoidAlgebra.of ℂ _ p * MonoidAlgebra.of ℂ _ σ⁻¹) *
            YoungSymmetrizer n nu := by simp only [mul_assoc]
      _ = RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ (p * σ⁻¹) *
          YoungSymmetrizer n nu := by
            congr 2
            exact ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))).map_mul p σ⁻¹).symm
      _ = RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ (σ⁻¹ * q) *
          YoungSymmetrizer n nu := by rw [hpEq]
      _ = RowSymmetrizer n mu *
          (MonoidAlgebra.of ℂ _ σ⁻¹ * MonoidAlgebra.of ℂ _ q) *
            YoungSymmetrizer n nu := by
              congr 2
              exact (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))).map_mul σ⁻¹ q
      _ = RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ σ⁻¹ *
          (MonoidAlgebra.of ℂ _ q * YoungSymmetrizer n nu) := by
            simp only [mul_assoc]
      _ = RowSymmetrizer n mu * MonoidAlgebra.of ℂ _ σ⁻¹ *
          ((-1 : ℂ) • YoungSymmetrizer n nu) := by rw [hqAction]
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
  change (youngRuleRowAverage n mu nu (spechtPolytabloid S) :
      SpechtModule n nu) = 0
  apply Subtype.ext
  change (Nat.card (↥(RowSubgroup n mu)) : ℂ)⁻¹ •
      (RowSymmetrizer n mu *
        ((Nat.card (↥(RowSubgroup n nu)) : ℂ)⁻¹ •
          MonoidAlgebra.of ℂ _ σ⁻¹ * YoungSymmetrizer n nu)) = 0
  simp only [Algebra.mul_smul_comm, smul_mul_assoc, ← mul_assoc, A, hA, smul_zero]

/-- Every averaged standard polytabloid either is the vector of its collapsed
semistandard tableau or vanishes, so it belongs to the semistandard span. -/
theorem youngRuleAveragedPolytabloid_mem_span_semistandardVector
    (n : ℕ) (mu nu : Nat.Partition n) (S : StandardYoungTableau n nu) :
    youngRuleAveragedPolytabloid n mu nu S ∈
      Submodule.span ℂ (Set.range (youngRuleSemistandardVector n mu nu)) := by
  by_cases hstrict : S.ContentCollapseColumnStrict mu
  · rw [youngRuleAveragedPolytabloid_eq_semistandardVector_of_columnStrict
      n mu nu S hstrict]
    apply Submodule.subset_span
    exact ⟨S.toKostkaTableauOfContentCollapseColumnStrict hstrict, rfl⟩
  · rw [youngRuleAveragedPolytabloid_eq_zero_of_not_columnStrict
      n mu nu S hstrict]
    exact Submodule.zero_mem _

/-- The semistandard-tableau vectors span the full row-invariant subspace. -/
theorem span_range_youngRuleSemistandardVector (n : ℕ)
    (mu nu : Nat.Partition n) :
    Submodule.span ℂ (Set.range (youngRuleSemistandardVector n mu nu)) = ⊤ := by
  rw [eq_top_iff, ← span_youngRuleAveragedPolytabloid n mu nu]
  apply Submodule.span_le.mpr
  rintro _ ⟨S, rfl⟩
  exact youngRuleAveragedPolytabloid_mem_span_semistandardVector n mu nu S

/-- The canonical standardization always has column-strict content collapse. -/
theorem KostkaTableau.standardization_contentCollapseColumnStrict {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) :
    T.standardization.ContentCollapseColumnStrict mu := by
  intro c₁ c₂ hcol hrow
  rw [KostkaTableau.rowOfPos_standardization T c₁,
    KostkaTableau.rowOfPos_standardization T c₂]
  simpa [hcol] using T.1.col_strict hrow (cell_mem_partitionDiagram c₂)

/-- Collapsing the canonical standardization recovers the original
semistandard tableau. -/
theorem KostkaTableau.toKostkaTableau_standardization {n : ℕ}
    {nu mu : Nat.Partition n} (T : KostkaTableau n nu mu) :
    T.standardization.toKostkaTableauOfContentCollapseColumnStrict
      T.standardization_contentCollapseColumnStrict = T := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hcell : (i, j) ∈ nu.toYoungDiagram
  · let c := partitionCellOfMem (i, j) hcell
    change (T.standardization.toKostkaTableauOfContentCollapseColumnStrict
      T.standardization_contentCollapseColumnStrict).1.1 c.1.1 c.1.2 =
        T.1 c.1.1 c.1.2
    rw [T.standardization.toKostkaTableauOfContentCollapseColumnStrict_apply
      T.standardization_contentCollapseColumnStrict c,
      KostkaTableau.rowOfPos_standardization T c]
  · rw [(T.standardization.toKostkaTableauOfContentCollapseColumnStrict
      T.standardization_contentCollapseColumnStrict).1.zeros hcell, T.1.zeros hcell]

/-- Canonical standardization remembers the semistandard tableau because its
content-block collapse is a left inverse. -/
theorem KostkaTableau.standardization_injective {n : ℕ}
    {nu mu : Nat.Partition n} :
    Function.Injective (KostkaTableau.standardization :
      KostkaTableau n nu mu → StandardYoungTableau n nu) := by
  intro T U h
  have hfun : T.standardization.1 = U.standardization.1 :=
    congrArg Subtype.val h
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hcell : (i, j) ∈ nu.toYoungDiagram
  · let c := partitionCellOfMem (i, j) hcell
    change T.1 c.1.1 c.1.2 = U.1 c.1.1 c.1.2
    rw [← KostkaTableau.rowOfPos_standardization T c,
      ← KostkaTableau.rowOfPos_standardization U c, hfun]
  · rw [T.1.zeros hcell, U.1.zeros hcell]

end

end Etingof

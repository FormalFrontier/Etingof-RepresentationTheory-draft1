import EtingofRepresentationTheory.Chapter5.YoungRuleDecomposition

/-!
# The combinatorial boundary of Young's rule

This file begins the missing bridge between the representation-theoretic multiplicity
`YoungRuleMultiplicity` and the semistandard-tableau cardinal `KostkaNumber`.

Every semistandard tableau of shape `mu` and content `la` forces `mu` to dominate `la`.
Moreover, at `mu = la` the highest-weight tableau is the unique tableau with that content.
Consequently the two definitions agree off the dominance cone and on its diagonal. The remaining
case is the genuinely positive, strictly dominant part of Young's rule.
-/

namespace Etingof

/-- The finite-content tableaux counted by `KostkaNumber`. Naming the subtype makes the exact
combinatorial object needed for the remaining Young-rule bijection available to later files. -/
noncomputable abbrev KostkaTableau
    (n : ℕ) (mu la : Nat.Partition n) :=
  { T : SemistandardYoungTableau mu.toYoungDiagram //
    ∀ k : ℕ, (mu.toYoungDiagram.cells.filter (fun c => T c.1 c.2 = k)).card =
      la.sortedParts.getD k 0 }

theorem kostkaNumber_eq_card_kostkaTableau
    (n : ℕ) (mu la : Nat.Partition n) :
    KostkaNumber n mu la = Nat.card (KostkaTableau n mu la) :=
  rfl

/-- An entry in row `i` of a semistandard tableau is at least `i`. -/
private theorem row_le_entry {mu : YoungDiagram}
    (T : SemistandardYoungTableau mu) {i j : ℕ} (hcell : (i, j) ∈ mu) :
    i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have habove : (i, j) ∈ mu := mu.up_left_mem (Nat.le_succ i) le_rfl hcell
      exact Nat.succ_le_of_lt
        ((ih habove).trans_lt (T.col_strict (Nat.lt_succ_self i) hcell))

/-- A `take` sum written using `getD`, so it also covers indices beyond the list. -/
private theorem sum_take_eq_sum_getD (l : List ℕ) (k : ℕ) :
    (l.take k).sum = ∑ i ∈ Finset.range k, l.getD i 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.take_add_one, List.sum_append, ih, Finset.sum_range_succ]
      cases h : l[k]? <;> simp [List.getD_eq_getElem?_getD, h]

/-- The row length of the diagram attached to a partition is its corresponding sorted part. -/
private theorem partitionDiagram_rowLen (n : ℕ) (mu : Nat.Partition n) (i : ℕ) :
    mu.toYoungDiagram.rowLen i = mu.sortedParts.getD i 0 := by
  have key : ∀ j : ℕ,
      j < mu.toYoungDiagram.rowLen i ↔ j < mu.sortedParts.getD i 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i, j) ∈ YoungDiagram.ofRowLens mu.sortedParts _ ↔ _
    rw [YoungDiagram.mem_ofRowLens]
    by_cases hi : i < mu.sortedParts.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
    · rw [List.getD_eq_default _ _ (not_lt.mp hi)]
      exact ⟨fun h => (hi h.1).elim, fun h => (Nat.not_lt_zero j h).elim⟩
  have h₁ := key (mu.toYoungDiagram.rowLen i)
  have h₂ := key (mu.sortedParts.getD i 0)
  omega

/-- A partition of `n` has at most `n` positive parts. -/
private theorem sortedParts_length_le (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.length ≤ n := by
  have hsum : la.sortedParts.sum = n := by
    have hsort : (la.sortedParts : Multiset ℕ) = la.parts :=
      la.parts.sort_eq (· ≥ ·)
    have : la.sortedParts.sum = la.parts.sum := by rw [← Multiset.sum_coe, hsort]
    rw [this, la.parts_sum]
  have hpos : ∀ x ∈ la.sortedParts, 1 ≤ x := fun x hx =>
    la.parts_pos ((Multiset.mem_sort _).mp hx)
  exact (List.length_le_sum_of_one_le _ hpos).trans_eq hsum

/-- The content condition bounds every entry, making the counted tableau subtype finite. -/
private theorem entry_lt_succ {n : ℕ} {mu la : Nat.Partition n}
    (T : KostkaTableau n mu la) {c : ℕ × ℕ} (hc : c ∈ mu.toYoungDiagram) :
    T.1 c.1 c.2 < n + 1 := by
  let k := T.1 c.1 c.2
  have hmem : c ∈ mu.toYoungDiagram.cells.filter (fun d => T.1 d.1 d.2 = k) := by
    simp [k, hc]
  have hpos : 0 < (mu.toYoungDiagram.cells.filter (fun d => T.1 d.1 d.2 = k)).card :=
    Finset.card_pos.mpr ⟨c, hmem⟩
  rw [T.2 k] at hpos
  have hk : k < la.sortedParts.length := by
    by_contra h
    rw [List.getD_eq_default _ _ (not_lt.mp h)] at hpos
    omega
  exact lt_of_lt_of_le hk (sortedParts_length_le n la) |>.trans_le (Nat.le_succ n)

noncomputable instance kostkaTableau_finite
    (n : ℕ) (mu la : Nat.Partition n) : Finite (KostkaTableau n mu la) := by
  let encode : KostkaTableau n mu la →
      ({ c // c ∈ mu.toYoungDiagram.cells } → Fin (n + 1)) := fun T c =>
    ⟨T.1 c.1.1 c.1.2, entry_lt_succ T c.2⟩
  apply Finite.of_injective encode
  intro T U h
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hc : (i, j) ∈ mu.toYoungDiagram
  · have hij := congrFun h ⟨(i, j), hc⟩
    exact congrArg Fin.val hij
  · rw [T.1.zeros hc, U.1.zeros hc]

/-- The tableau cardinal really indexes the tableaux counted by `KostkaNumber`. -/
noncomputable def kostkaTableauEquivFin
    (n : ℕ) (mu la : Nat.Partition n) :
    KostkaTableau n mu la ≃ Fin (KostkaNumber n mu la) := by
  letI := Fintype.ofFinite (KostkaTableau n mu la)
  have hcard : Fintype.card (KostkaTableau n mu la) = KostkaNumber n mu la := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  exact (Fintype.equivFin (KostkaTableau n mu la)).trans
    (Equiv.cast (congrArg Fin hcard))

/-- The content of a Kostka tableau determines the number of cells carrying an
entry strictly below any cutoff. -/
theorem KostkaTableau.card_entries_lt {n : ℕ} {mu la : Nat.Partition n}
    (T : KostkaTableau n mu la) (k : ℕ) :
    (mu.toYoungDiagram.cells.filter (fun c => T.1 c.1 c.2 < k)).card =
      (la.sortedParts.take k).sum := by
  rw [sum_take_eq_sum_getD]
  calc
    (mu.toYoungDiagram.cells.filter (fun c => T.1 c.1 c.2 < k)).card =
        ∑ i ∈ Finset.range k,
          (mu.toYoungDiagram.cells.filter (fun c => T.1 c.1 c.2 = i)).card := by
            simpa only [Finset.mem_range] using
              (Finset.sum_card_fiberwise_eq_card_filter mu.toYoungDiagram.cells
                (Finset.range k) (fun c => T.1 c.1 c.2)).symm
    _ = ∑ i ∈ Finset.range k, la.sortedParts.getD i 0 :=
      Finset.sum_congr rfl fun i _ => T.2 i

/-- Count the cells in the first `k` rows by summing their row lengths. -/
private theorem card_rows_lt (n : ℕ) (mu : Nat.Partition n) (k : ℕ) :
    (mu.toYoungDiagram.cells.filter (fun c => c.1 < k)).card =
      (mu.sortedParts.take k).sum := by
  rw [sum_take_eq_sum_getD]
  calc
    (mu.toYoungDiagram.cells.filter (fun c => c.1 < k)).card =
        ∑ i ∈ Finset.range k,
          (mu.toYoungDiagram.cells.filter (fun c => c.1 = i)).card := by
            simpa only [Finset.mem_range] using
              (Finset.sum_card_fiberwise_eq_card_filter mu.toYoungDiagram.cells
                (Finset.range k) Prod.fst).symm
    _ = ∑ i ∈ Finset.range k, mu.sortedParts.getD i 0 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (mu.toYoungDiagram.cells.filter (fun c => c.1 = i)).card =
            (mu.toYoungDiagram.row i).card := rfl
        _ = mu.toYoungDiagram.rowLen i := (YoungDiagram.rowLen_eq_card _).symm
        _ = mu.sortedParts.getD i 0 := partitionDiagram_rowLen n mu i

/-- The tableau support theorem for Kostka numbers: shape dominates content. -/
theorem KostkaTableau.dominates {n : ℕ} {mu la : Nat.Partition n}
    (T : KostkaTableau n mu la) : Nat.Partition.Dominates mu la := by
  intro k
  rw [← card_entries_lt T k, ← card_rows_lt n mu k]
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, (row_le_entry T.1 hc.1).trans_lt hc.2⟩

/-- The combinatorial Kostka number vanishes outside the dominance cone. -/
theorem kostkaNumber_eq_zero_of_not_dominates
    (n : ℕ) (mu la : Nat.Partition n)
    (h : ¬ Nat.Partition.Dominates mu la) :
    KostkaNumber n mu la = 0 := by
  rw [kostkaNumber_eq_card_kostkaTableau, Nat.card_eq_zero]
  left
  exact ⟨fun T => h T.dominates⟩

/-- The highest-weight tableau has content equal to the row lengths of its shape. -/
private theorem highestWeight_has_diagonal_content
    (n : ℕ) (mu : Nat.Partition n) :
    ∀ k : ℕ,
      (mu.toYoungDiagram.cells.filter
        (fun c => SemistandardYoungTableau.highestWeight mu.toYoungDiagram c.1 c.2 = k)).card =
        mu.sortedParts.getD k 0 := by
  intro k
  calc
    (mu.toYoungDiagram.cells.filter
        (fun c => SemistandardYoungTableau.highestWeight mu.toYoungDiagram c.1 c.2 = k)).card =
        (mu.toYoungDiagram.row k).card := by
          congr 1
          ext c
          simp only [Finset.mem_filter, YoungDiagram.mem_cells,
            SemistandardYoungTableau.highestWeight_apply, YoungDiagram.mem_row_iff]
          constructor
          · rintro ⟨hc, hk⟩
            rw [if_pos hc] at hk
            exact ⟨hc, hk⟩
          · rintro ⟨hc, hk⟩
            exact ⟨hc, by rw [if_pos hc]; exact hk⟩
    _ = mu.toYoungDiagram.rowLen k := (YoungDiagram.rowLen_eq_card _).symm
    _ = mu.sortedParts.getD k 0 := partitionDiagram_rowLen n mu k

/-- The diagonal content forces every entry in row `i` to equal `i`. -/
private theorem eq_highestWeight_of_diagonal_content
    {n : ℕ} {mu : Nat.Partition n} (T : KostkaTableau n mu mu) :
    T.1 = SemistandardYoungTableau.highestWeight mu.toYoungDiagram := by
  apply SemistandardYoungTableau.ext
  intro i j
  by_cases hcell : (i, j) ∈ mu.toYoungDiagram
  · let entries := mu.toYoungDiagram.cells.filter (fun c => T.1 c.1 c.2 < i + 1)
    let rows := mu.toYoungDiagram.cells.filter (fun c => c.1 < i + 1)
    have hsubset : entries ⊆ rows := by
      intro c hc
      simp only [entries, rows, Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, (row_le_entry T.1 hc.1).trans_lt hc.2⟩
    have hcard : rows.card ≤ entries.card := by
      rw [T.card_entries_lt (i + 1), card_rows_lt n mu (i + 1)]
    have heq : entries = rows := Finset.eq_of_subset_of_card_le hsubset hcard
    have hrow : (i, j) ∈ rows := by simp [rows, hcell]
    have hlt : T.1 i j < i + 1 := by
      have : (i, j) ∈ entries := heq.symm ▸ hrow
      have hmem : (i, j) ∈ mu.toYoungDiagram.cells ∧ T.1 i j < i + 1 := by
        simpa [entries] using this
      exact hmem.2
    rw [SemistandardYoungTableau.highestWeight_apply, if_pos hcell]
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) (row_le_entry T.1 hcell)
  · rw [T.1.zeros hcell, SemistandardYoungTableau.highestWeight_apply, if_neg hcell]

/-- The combinatorial Kostka number is one on the diagonal. -/
theorem kostkaNumber_diagonal (n : ℕ) (mu : Nat.Partition n) :
    KostkaNumber n mu mu = 1 := by
  rw [kostkaNumber_eq_card_kostkaTableau, Nat.card_eq_one_iff_unique]
  constructor
  · constructor
    intro T U
    exact Subtype.ext ((eq_highestWeight_of_diagonal_content T).trans
      (eq_highestWeight_of_diagonal_content U).symm)
  · exact ⟨⟨SemistandardYoungTableau.highestWeight mu.toYoungDiagram,
      highestWeight_has_diagonal_content n mu⟩⟩

/-- The two Kostka notions agree everywhere outside the dominance cone. -/
theorem youngRuleMultiplicity_eq_kostkaNumber_of_not_dominates
    (n : ℕ) (mu nu : Nat.Partition n)
    (h : ¬ Nat.Partition.Dominates nu mu) :
    YoungRuleMultiplicity n mu nu = KostkaNumber n nu mu := by
  rw [youngRuleMultiplicity_eq_zero_of_not_dominates n mu nu h,
    kostkaNumber_eq_zero_of_not_dominates n nu mu h]

/-- The two Kostka notions agree on the unitriangular diagonal. -/
theorem youngRuleMultiplicity_eq_kostkaNumber_diagonal
    (n : ℕ) (mu : Nat.Partition n) :
    YoungRuleMultiplicity n mu mu = KostkaNumber n mu mu := by
  rw [youngRuleMultiplicity_diagonal, kostkaNumber_diagonal]

end Etingof

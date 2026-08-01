import Mathlib

/-!
# Definition 5.12.1: Partitions, Young Diagrams, Young Tableaux

A **partition** λ of n is a sequence λ₁ ≥ λ₂ ≥ ... ≥ λ_p > 0 with λ₁ + ... + λ_p = n.

A **Young diagram** of λ is a collection of n unit squares arranged in p left-aligned
rows, with λᵢ squares in row i.

A **Young tableau** of shape λ is a filling of the Young diagram with numbers 1, ..., n.

The **row subgroup** P_λ ⊂ S_n consists of permutations preserving each row.
The **column subgroup** Q_λ ⊂ S_n consists of permutations preserving each column.

Etingof's Young projectors (Discussion after Definition 5.12.1) are the **normalized**
elements of ℂ[S_n]
- a_λ = |P_λ|⁻¹ Σ_{g ∈ P_λ} g   (`youngProjectorRow`),
- b_λ = |Q_λ|⁻¹ Σ_{g ∈ Q_λ} sign(g) · g   (`youngProjectorCol`),
- c_λ = a_λ · b_λ   (`youngProjector`, row-then-column).

This file *also* provides the **unnormalized** sums `RowSymmetrizer = Σ_{g ∈ P_λ} g` and
`ColumnAntisymmetrizer = Σ_{g ∈ Q_λ} sign(g) · g`, and the element
`YoungSymmetrizer = ColumnAntisymmetrizer · RowSymmetrizer` (the *opposite*, unnormalized
`b_λ · a_λ` order). `YoungSymmetrizer` is the generator used by the downstream
`SpechtModule` construction; it is NOT Etingof's `c_λ`. The two are related by the
positive scalar `|P_λ| · |Q_λ|` and the factor order swap (see
`Etingof.youngProjectorCol_mul_youngProjectorRow` and the source-order
`Etingof.Lemma5_13_1_source` in `Lemma5_13_1.lean`).

## Mathlib correspondence

Mathlib has `Nat.Partition`, `YoungDiagram`, and `SemistandardYoungTableau`.
Standard Young tableaux, row/column subgroups, and Young symmetrizers need custom definitions.
-/

namespace Etingof

/-- Given a list of row lengths and a position k, return the row index
in the canonical (left-to-right, top-to-bottom) filling of the Young diagram. -/
def rowOfPos : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, k => if k < p then 0 else 1 + rowOfPos ps (k - p)

/-- Given a list of row lengths and a position k, return the column index
in the canonical (left-to-right, top-to-bottom) filling of the Young diagram. -/
def colOfPos : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, k => if k < p then k else colOfPos ps (k - p)

/-- The sorted (descending) parts of a partition, as a list of row lengths. -/
noncomputable def _root_.Nat.Partition.sortedParts {n : ℕ} (la : Nat.Partition n) : List ℕ :=
  la.parts.sort (· ≥ ·)

/-- An (ordinary) **Young tableau** of shape `λ` is *any* filling of the cells of the
Young diagram by the numbers `1, …, n` without repetition, i.e. a bijection from the
cells to `Fin n`. Row and column monotonicity are **not** required. (Etingof
Definition 5.12.1: "the result of filling the numbers `1, …, n` into the squares of
`Y_λ` in some way (without repetitions)".)

For shape `(2)` the filling `[2, 1]` is a genuine Young tableau even though it is not
standard. The increasing left-to-right, top-to-bottom tableau `T_λ` is merely one
particular example; see `canonicalYoungTableau`. The strictly-increasing
`StandardYoungTableau` is the refinement obtained by additionally imposing
monotonicity; see `StandardYoungTableau.toYoungTableau` for the forgetful bridge. -/
noncomputable def YoungTableau (n : ℕ) (la : Nat.Partition n) : Type :=
  let parts := la.sortedParts
  let Cell := { c : ℕ × ℕ // c.1 < parts.length ∧ c.2 < parts.getD c.1 0 }
  { f : Cell → Fin n // Function.Bijective f }

/-- A standard Young tableau of shape λ is a filling of a Young diagram with 0..n-1
such that entries increase along rows and down columns. (Etingof Definition 5.12.1)

Concretely: a bijection from cells of the diagram to `Fin n`, strictly increasing
along rows and down columns. A cell (i, j) is valid when i < number of rows and
j < length of row i (using the canonical descending-sorted parts).

This is the refinement of the ordinary `YoungTableau` by row/column monotonicity;
the forgetful map is `StandardYoungTableau.toYoungTableau`. -/
noncomputable def StandardYoungTableau (n : ℕ) (la : Nat.Partition n) : Type :=
  let parts := la.sortedParts
  let Cell := { c : ℕ × ℕ // c.1 < parts.length ∧ c.2 < parts.getD c.1 0 }
  { f : Cell → Fin n //
    Function.Bijective f ∧
    (∀ c₁ c₂ : Cell, c₁.1.1 = c₂.1.1 → c₁.1.2 < c₂.1.2 → f c₁ < f c₂) ∧
    (∀ c₁ c₂ : Cell, c₁.1.2 = c₂.1.2 → c₁.1.1 < c₂.1.1 → f c₁ < f c₂) }

/-- Every standard Young tableau is in particular an ordinary Young tableau: forget the
row/column monotonicity conditions and keep the underlying bijective filling. This is
the explicit bridge between the two notions of Etingof Definition 5.12.1. -/
noncomputable def StandardYoungTableau.toYoungTableau {n : ℕ} {la : Nat.Partition n}
    (T : StandardYoungTableau n la) : YoungTableau n la :=
  ⟨T.1, T.2.1⟩

/-- The row subgroup P_λ of S_n: permutations preserving each row of
the Young diagram. (Etingof Definition 5.12.1)

Two positions i, j ∈ Fin n are in the same row when `rowOfPos parts i = rowOfPos parts j`
where `parts` are the descending-sorted parts and `rowOfPos` computes the row index
in the canonical left-to-right, top-to-bottom filling. -/
noncomputable def RowSubgroup (n : ℕ) (la : Nat.Partition n) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | ∀ k : Fin n,
    rowOfPos la.sortedParts (σ k).val = rowOfPos la.sortedParts k.val }
  one_mem' := by
    intro k
    simp [Equiv.Perm.one_apply]
  mul_mem' := by
    intro σ τ hσ hτ k
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ (τ k), hτ k]
  inv_mem' := by
    intro σ hσ k
    have h := hσ (σ⁻¹ k)
    rw [show σ (σ⁻¹ k) = k from σ.apply_symm_apply k] at h
    exact h.symm

/-- The column subgroup Q_λ of S_n: permutations preserving each column of
the Young diagram. (Etingof Definition 5.12.1)

Two positions i, j ∈ Fin n are in the same column when `colOfPos parts i = colOfPos parts j`
where `parts` are the descending-sorted parts and `colOfPos` computes the column index
in the canonical left-to-right, top-to-bottom filling. -/
noncomputable def ColumnSubgroup (n : ℕ) (la : Nat.Partition n) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := { σ | ∀ k : Fin n,
    colOfPos la.sortedParts (σ k).val = colOfPos la.sortedParts k.val }
  one_mem' := by
    intro k
    simp [Equiv.Perm.one_apply]
  mul_mem' := by
    intro σ τ hσ hτ k
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ (τ k), hτ k]
  inv_mem' := by
    intro σ hσ k
    have h := hσ (σ⁻¹ k)
    rw [show σ (σ⁻¹ k) = k from σ.apply_symm_apply k] at h
    exact h.symm

/-- The row symmetrizer a_λ = ∑_{g ∈ P_λ} g in the group algebra ℂ[S_n].
(Etingof Definition 5.12.1) -/
noncomputable def RowSymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ RowSubgroup n la) := Classical.decPred _
  ∑ g : (RowSubgroup n la), MonoidAlgebra.of ℂ _ g.val

/-- The column antisymmetrizer b_λ = ∑_{g ∈ Q_λ} sign(g) · g in the group algebra ℂ[S_n].
(Etingof Definition 5.12.1) -/
noncomputable def ColumnAntisymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  ∑ g : (ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : ℂ) • MonoidAlgebra.of ℂ _ g.val

/-- The **unnormalized** element `b_λ · a_λ = ColumnAntisymmetrizer · RowSymmetrizer` in
the group algebra ℂ[S_n], where a_λ = ∑_{g ∈ P_λ} g and b_λ = ∑_{g ∈ Q_λ} sign(g) · g.

**Warning on naming/convention.** This is *not* Etingof's Young projector `c_λ`. Etingof
defines the normalized `c_λ = a_λ · b_λ` (row-then-column); see `youngProjector`. The
element here differs from `c_λ` both in normalization (by the positive scalar
`|P_λ| · |Q_λ|`) and in factor order (`b_λ · a_λ` vs `a_λ · b_λ`), and the factors do not
commute. It is retained under this name because it is the historical generator of the
downstream `SpechtModule` left ideal ℂ[S_n]·(b_λ a_λ): the ordering makes polytabloids
`e_T = κ_T · of(σ_T) · a_λ` left multiples of `b_λ · a_λ` for the canonical filling. The
precise relationship to the source projectors is
`Etingof.youngProjectorCol_mul_youngProjectorRow`. -/
noncomputable def YoungSymmetrizer (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  ColumnAntisymmetrizer n la * RowSymmetrizer n la

/-- Etingof's **normalized row projector** `a_λ = |P_λ|⁻¹ ∑_{g ∈ P_λ} g` in ℂ[S_n]
(Discussion of Young projectors after Definition 5.12.1). Unlike `RowSymmetrizer`, this is
a genuine idempotent: `youngProjectorRow_mul_self`. -/
noncomputable def youngProjectorRow (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (Nat.card (RowSubgroup n la) : ℂ)⁻¹ • RowSymmetrizer n la

/-- Etingof's **normalized column projector** `b_λ = |Q_λ|⁻¹ ∑_{g ∈ Q_λ} sign(g) · g` in
ℂ[S_n] (Discussion of Young projectors after Definition 5.12.1). A genuine idempotent:
`youngProjectorCol_mul_self`. -/
noncomputable def youngProjectorCol (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (Nat.card (ColumnSubgroup n la) : ℂ)⁻¹ • ColumnAntisymmetrizer n la

/-- Etingof's **Young projector** `c_λ = a_λ · b_λ` (row-then-column, normalized), the
source-faithful element of ℂ[S_n] from the Discussion after Definition 5.12.1.

This is the honest formalization of Etingof's `c_λ`. It is distinct from the
implementation element `YoungSymmetrizer = b_λ · a_λ` (opposite order, unnormalized). -/
noncomputable def youngProjector (n : ℕ) (la : Nat.Partition n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  youngProjectorRow n la * youngProjectorCol n la

/-! ## Helper lemmas for rowOfPos and colOfPos -/

-- colOfPos is bounded by the row width for valid positions
theorem colOfPos_lt_getD (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    colOfPos parts k < parts.getD (rowOfPos parts k) 0 := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    simp only [rowOfPos, colOfPos]
    split_ifs with hlt
    · rw [List.getD_cons_zero]; omega
    · have hk' : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      change colOfPos ps (k - p) < (p :: ps).getD (1 + rowOfPos ps (k - p)) 0
      rw [show 1 + rowOfPos ps (k - p) = rowOfPos ps (k - p) + 1 from by omega,
          List.getD_cons_succ]
      exact ih (k - p) hk'

-- (rowOfPos, colOfPos) is injective on valid positions
theorem rowOfPos_colOfPos_injective (parts : List ℕ) (k₁ k₂ : ℕ)
    (hk₁ : k₁ < parts.sum) (hk₂ : k₂ < parts.sum)
    (hrow : rowOfPos parts k₁ = rowOfPos parts k₂)
    (hcol : colOfPos parts k₁ = colOfPos parts k₂) : k₁ = k₂ := by
  induction parts generalizing k₁ k₂ with
  | nil => simp [List.sum_nil] at hk₁
  | cons p ps ih =>
    simp only [rowOfPos, colOfPos] at hrow hcol
    by_cases h₁ : k₁ < p <;> by_cases h₂ : k₂ < p
    · simp [h₁, h₂] at hcol; exact hcol
    · simp only [h₁, ite_true, h₂, ite_false] at hrow; omega
    · simp only [h₁, ite_false, h₂, ite_true] at hrow; omega
    · simp only [h₁, ite_false, h₂] at hrow hcol
      have hk₁' : k₁ - p < ps.sum := by simp [List.sum_cons] at hk₁; omega
      have hk₂' : k₂ - p < ps.sum := by simp [List.sum_cons] at hk₂; omega
      have : k₁ - p = k₂ - p := ih (k₁ - p) (k₂ - p) hk₁' hk₂' (by omega) hcol
      omega

-- For a valid cell (r, c), there exists a position with that row and column
theorem exists_pos_of_cell (parts : List ℕ) (r c : ℕ)
    (hr : c < parts.getD r 0) :
    ∃ k, k < parts.sum ∧ rowOfPos parts k = r ∧ colOfPos parts k = c := by
  induction parts generalizing r with
  | nil => simp [List.getD] at hr
  | cons p ps ih =>
    cases r with
    | zero =>
      rw [List.getD_cons_zero] at hr
      exact ⟨c, by simp [List.sum_cons]; omega,
        by simp [rowOfPos]; omega, by simp [colOfPos]; omega⟩
    | succ r =>
      rw [List.getD_cons_succ] at hr
      obtain ⟨k, hk, hrow, hcol⟩ := ih r hr
      exact ⟨p + k, by simp [List.sum_cons]; omega,
        by simp [rowOfPos]; omega,
        by simp [colOfPos]; omega⟩

/-! ## The canonical increasing tableau `T_λ`

Etingof singles out the tableau `T_λ` obtained by "filling in the numbers in increasing
order, left to right, top to bottom". We construct it here, as both an ordinary
`YoungTableau` and a `StandardYoungTableau`, so that the two notions of
Definition 5.12.1 are connected by a concrete example. -/

/-- The linear position (0-indexed) of cell `(r, c)` in the canonical left-to-right,
top-to-bottom filling: all `(la.sortedParts.take r).sum` cells in earlier rows, plus the
`c` cells to its left in row `r`. -/
def posOfCell (parts : List ℕ) (rc : ℕ × ℕ) : ℕ :=
  (parts.take rc.1).sum + rc.2

/-- The sorted parts of a partition of `n` sum to `n`. -/
private theorem sortedParts_sum (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have hcoe : (la.sortedParts : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at hcoe
  rw [hcoe, la.parts_sum]

/-- `rowOfPos` returns a value less than the list length for valid positions. -/
private theorem rowOfPos_lt_length (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    rowOfPos parts k < parts.length := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    simp only [rowOfPos, List.length_cons]
    split_ifs with h
    · omega
    · have : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      have := ih _ this; omega

/-- take-sums are monotone in the truncation length (over `ℕ`). -/
private theorem sum_take_le (l : List ℕ) (a b : ℕ) (h : a ≤ b) :
    (l.take a).sum ≤ (l.take b).sum := by
  calc (l.take a).sum
      = ((l.take b).take a).sum := by rw [List.take_take, Nat.min_eq_left h]
    _ ≤ ((l.take b).take a).sum + ((l.take b).drop a).sum := Nat.le_add_right _ _
    _ = (l.take b).sum := by rw [← List.sum_append, List.take_append_drop]

/-- Round trip: the canonical position of the cell at position `k` is `k` again. -/
private theorem posOfCell_rowColOfPos (parts : List ℕ) (k : ℕ) (hk : k < parts.sum) :
    posOfCell parts (rowOfPos parts k, colOfPos parts k) = k := by
  induction parts generalizing k with
  | nil => simp [List.sum_nil] at hk
  | cons p ps ih =>
    by_cases hlt : k < p
    · simp only [rowOfPos, colOfPos, hlt, if_true, posOfCell, List.take_zero,
        List.sum_nil, Nat.zero_add]
    · have hk' : k - p < ps.sum := by simp [List.sum_cons] at hk; omega
      simp only [rowOfPos, colOfPos, hlt, if_false, posOfCell]
      rw [show 1 + rowOfPos ps (k - p) = rowOfPos ps (k - p) + 1 from Nat.add_comm _ _,
          List.take_succ_cons, List.sum_cons]
      have := ih (k - p) hk'
      simp only [posOfCell] at this
      omega

/-- Round trip: the position of a valid cell `(r, c)` sits back in row `r`, column `c`. -/
private theorem rowColOfPos_posOfCell (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts.getD r 0) :
    rowOfPos parts (posOfCell parts (r, c)) = r ∧
    colOfPos parts (posOfCell parts (r, c)) = c := by
  induction parts generalizing r with
  | nil => simp at hr
  | cons p ps ih =>
    cases r with
    | zero =>
      have hcp : c < p := by rwa [List.getD_cons_zero] at hc
      refine ⟨?_, ?_⟩ <;>
        simp only [posOfCell, List.take_zero, List.sum_nil, Nat.zero_add, rowOfPos, colOfPos,
          hcp, if_true]
    | succ r =>
      have hr' : r < ps.length := by simpa using hr
      have hc' : c < ps.getD r 0 := by rwa [List.getD_cons_succ] at hc
      have hpos : posOfCell (p :: ps) (r + 1, c) = p + posOfCell ps (r, c) := by
        simp only [posOfCell, List.take_succ_cons, List.sum_cons]; ring
      rw [hpos]
      obtain ⟨ih1, ih2⟩ := ih r hr' hc'
      have hge : ¬ (p + posOfCell ps (r, c) < p) := by omega
      refine ⟨?_, ?_⟩
      · simp only [rowOfPos, hge, if_false, Nat.add_sub_cancel_left, ih1]; omega
      · simp only [colOfPos, hge, if_false, Nat.add_sub_cancel_left, ih2]

/-- The canonical position of a valid cell is a genuine position, i.e. `< parts.sum`. -/
private theorem posOfCell_lt_sum (parts : List ℕ) (r c : ℕ)
    (hr : r < parts.length) (hc : c < parts.getD r 0) :
    posOfCell parts (r, c) < parts.sum := by
  have hgetD : parts.getD r 0 = parts[r] := List.getD_eq_getElem parts 0 hr
  have hsucc : (parts.take (r + 1)).sum = (parts.take r).sum + parts[r] :=
    List.sum_take_succ parts r hr
  have hle : (parts.take (r + 1)).sum ≤ (parts.take parts.length).sum :=
    sum_take_le parts (r + 1) parts.length hr
  rw [List.take_length] at hle
  simp only [posOfCell]
  rw [hgetD] at hc
  omega

/-- The underlying filling of the canonical tableau `T_λ`: cell `(r, c) ↦ posOfCell`. -/
private noncomputable def canonicalFun (n : ℕ) (la : Nat.Partition n) :
    { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0 } → Fin n :=
  fun cell => ⟨posOfCell la.sortedParts cell.1, by
    have h := posOfCell_lt_sum la.sortedParts cell.1.1 cell.1.2 cell.2.1 cell.2.2
    rw [sortedParts_sum] at h; exact h⟩

/-- The canonical filling is a bijection: it uses every number `1, …, n` exactly once. -/
private theorem canonicalFun_bijective (n : ℕ) (la : Nat.Partition n) :
    Function.Bijective (canonicalFun n la) := by
  have hsum : la.sortedParts.sum = n := sortedParts_sum n la
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun k => ⟨(rowOfPos la.sortedParts k.val, colOfPos la.sortedParts k.val),
      rowOfPos_lt_length la.sortedParts k.val (by omega),
      colOfPos_lt_getD la.sortedParts k.val (by omega)⟩, ?_, ?_⟩
  · intro cell
    apply Subtype.ext
    obtain ⟨⟨r, c⟩, hr, hc⟩ := cell
    simp only [canonicalFun]
    obtain ⟨e1, e2⟩ := rowColOfPos_posOfCell la.sortedParts r c hr hc
    rw [e1, e2]
  · intro k
    apply Fin.ext
    simp only [canonicalFun]
    exact posOfCell_rowColOfPos la.sortedParts k.val (by omega)

/-- Along a fixed row, the canonical filling increases left to right. -/
private theorem canonicalFun_row_inc (n : ℕ) (la : Nat.Partition n)
    (c₁ c₂ : { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0 })
    (hrow : c₁.1.1 = c₂.1.1) (hcol : c₁.1.2 < c₂.1.2) :
    canonicalFun n la c₁ < canonicalFun n la c₂ := by
  simp only [canonicalFun, Fin.mk_lt_mk, posOfCell]
  rw [hrow]
  omega

/-- Down a fixed column, the canonical filling increases top to bottom. -/
private theorem canonicalFun_col_inc (n : ℕ) (la : Nat.Partition n)
    (c₁ c₂ : { c : ℕ × ℕ // c.1 < la.sortedParts.length ∧ c.2 < la.sortedParts.getD c.1 0 })
    (hcol : c₁.1.2 = c₂.1.2) (hrow : c₁.1.1 < c₂.1.1) :
    canonicalFun n la c₁ < canonicalFun n la c₂ := by
  simp only [canonicalFun, Fin.mk_lt_mk, posOfCell]
  have hr1 : c₁.1.1 < la.sortedParts.length := c₁.2.1
  have hgetD : la.sortedParts.getD c₁.1.1 0 = la.sortedParts[c₁.1.1] :=
    List.getD_eq_getElem la.sortedParts 0 hr1
  have hc1 : c₁.1.2 < la.sortedParts.getD c₁.1.1 0 := c₁.2.2
  have hsucc : (la.sortedParts.take (c₁.1.1 + 1)).sum
      = (la.sortedParts.take c₁.1.1).sum + la.sortedParts[c₁.1.1] :=
    List.sum_take_succ la.sortedParts c₁.1.1 hr1
  have hle : (la.sortedParts.take (c₁.1.1 + 1)).sum ≤ (la.sortedParts.take c₂.1.1).sum :=
    sum_take_le la.sortedParts (c₁.1.1 + 1) c₂.1.1 (by omega)
  rw [hgetD] at hc1
  omega

/-- The **canonical (increasing) Young tableau** `T_λ`, as an *ordinary* Young tableau:
cell `(r, c)` receives the number equal to its position in the left-to-right,
top-to-bottom reading order. (Etingof Definition 5.12.1, the example tableau `T_λ`.) -/
noncomputable def canonicalYoungTableau (n : ℕ) (la : Nat.Partition n) : YoungTableau n la :=
  ⟨canonicalFun n la, canonicalFun_bijective n la⟩

/-- The canonical tableau `T_λ` is standard: it strictly increases along rows and down
columns. This is the increasing tableau singled out in Etingof Definition 5.12.1. -/
noncomputable def canonicalStandardYoungTableau (n : ℕ) (la : Nat.Partition n) :
    StandardYoungTableau n la :=
  ⟨canonicalFun n la, canonicalFun_bijective n la,
    canonicalFun_row_inc n la, canonicalFun_col_inc n la⟩

/-- The standard canonical tableau, viewed as an ordinary tableau via the forgetful
bridge, is the ordinary canonical tableau. -/
theorem canonicalStandardYoungTableau_toYoungTableau (n : ℕ) (la : Nat.Partition n) :
    (canonicalStandardYoungTableau n la).toYoungTableau = canonicalYoungTableau n la :=
  rfl

end Etingof

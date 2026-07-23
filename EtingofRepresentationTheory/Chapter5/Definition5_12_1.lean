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

/-- A standard Young tableau of shape λ is a filling of a Young diagram with 0..n-1
such that entries increase along rows and down columns. (Etingof Definition 5.12.1)

Concretely: a bijection from cells of the diagram to `Fin n`, strictly increasing
along rows and down columns. A cell (i, j) is valid when i < number of rows and
j < length of row i (using the canonical descending-sorted parts). -/
noncomputable def StandardYoungTableau (n : ℕ) (la : Nat.Partition n) : Type :=
  let parts := la.sortedParts
  let Cell := { c : ℕ × ℕ // c.1 < parts.length ∧ c.2 < parts.getD c.1 0 }
  { f : Cell → Fin n //
    Function.Bijective f ∧
    (∀ c₁ c₂ : Cell, c₁.1.1 = c₂.1.1 → c₁.1.2 < c₂.1.2 → f c₁ < f c₂) ∧
    (∀ c₁ c₂ : Cell, c₁.1.2 = c₂.1.2 → c₁.1.1 < c₂.1.1 → f c₁ < f c₂) }

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
      show colOfPos ps (k - p) < (p :: ps).getD (1 + rowOfPos ps (k - p)) 0
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

end Etingof

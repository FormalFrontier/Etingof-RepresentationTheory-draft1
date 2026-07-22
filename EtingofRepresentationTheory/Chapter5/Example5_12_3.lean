import EtingofRepresentationTheory.Chapter5.CharValueHookFormula
import EtingofRepresentationTheory.Chapter5.FRTHelpers
import EtingofRepresentationTheory.Chapter5.Lemma5_13_1

/-!
# Example 5.12.3: Concrete Examples of Specht Modules

Explicit dimension computations of Specht modules `V_λ = ℂ[S_n] · c_λ` for small
partitions, following Etingof Example 5.12.3.

- **Partition `(n)`** (one row): `V_{(n)}` is the trivial representation, of dimension `1`.
- **Partition `(1,…,1)`** (one column): `V_{(1ⁿ)}` is the sign representation, of dimension `1`.
- **`n = 3`, `λ = (2,1)`**: `dim V_{(2,1)} = 2` (the standard representation of `S₃`).
- **`n = 4`, `λ = (2,2)`**: `dim V_{(2,2)} = 2`.
- **`n = 4`, `λ = (3,1)`**: `dim V_{(3,1)} = 3`.
- **`n = 4`, `λ = (2,1,1)`**: `dim V_{(2,1,1)} = 3`.

All dimensions are obtained from the Frame–Robinson–Thrall hook-length formula
`dim_ℂ V_λ = |SYT(λ)| = n! / ∏ h(i,j)` (`finrank_spechtModule_eq_card_syt_general`
and `card_standardYoungTableau_eq`), specialised to each shape. The book's `(n)`
and `(1ⁿ)` cases are the trivial- and sign-representation extremes, both of
dimension `1`; the four explicit small partitions exhibit the remaining
nontrivial dimensions.

For the two extreme partitions the book asserts a representation isomorphism,
not merely a dimension. We capture this directly at the `ℂ[Sₙ]`-module level:
`Example5_12_3_trivial_rep` shows every group element acts as the identity on
`V_{(n)}` (trivial representation), and `Example5_12_3_sign_rep` shows every
group element `σ` acts as `sign σ` on `V_{(1ⁿ)}` (sign representation). These
distinguish the two one-dimensional representations, which a dimension count
alone cannot.

## Mathlib correspondence

These are concrete instances of the general §5.12 / §5.17 hook-length theory
already formalised in this project; no new Mathlib API is required.
-/

namespace Etingof

namespace Example5_12_3

/-! ## Computable reformulation of the hook-length product

`YoungDiagram.rowLen`/`colLen` are defined via `Nat.find`, which does not reduce
in the kernel, so `decide` cannot evaluate `hookLengthProduct` directly. We first
rewrite everything into a `Nat.find`-free form that *does* reduce. -/

/-- General column-length formula for a partition's Young diagram, with no
`Nat.find`: `colLen c` counts the rows whose length exceeds `c`. -/
theorem toYoungDiagram_colLen_eq {m : ℕ} (μ : Nat.Partition m) (c : ℕ) :
    μ.toYoungDiagram.colLen c
      = ((Finset.range μ.sortedParts.length).filter
          (fun i => c < μ.sortedParts.getD i 0)).card := by
  rw [← Finset.card_range (μ.toYoungDiagram.colLen c)]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen,
      Nat.Partition.toYoungDiagram_rowLen_eq_getD]
  constructor
  · intro h
    refine ⟨?_, h⟩
    by_contra hge
    push Not at hge
    rw [List.getD_eq_default _ _ hge] at h
    exact absurd h (Nat.not_lt_zero c)
  · intro h; exact h.2

/-- The hook-length product in a fully computable form (no `Nat.find`). -/
theorem hookLengthProduct_eq_compute {m : ℕ} (μ : Nat.Partition m) :
    μ.toYoungDiagram.hookLengthProduct
      = ∏ x ∈ μ.toYoungDiagram.cells,
          (μ.sortedParts.getD x.1 0
            + ((Finset.range μ.sortedParts.length).filter
                (fun r => x.2 < μ.sortedParts.getD r 0)).card - x.1 - x.2 - 1) := by
  unfold YoungDiagram.hookLengthProduct
  refine Finset.prod_congr rfl (fun x _ => ?_)
  rw [YoungDiagram.hookLength, Nat.Partition.toYoungDiagram_rowLen_eq_getD,
      toYoungDiagram_colLen_eq]

/-- The sorted parts of a partition equal any already-descending list whose
coercion to a multiset is the partition's parts. -/
theorem sortedParts_eq_of {m : ℕ} (μ : Nat.Partition m) (L : List ℕ)
    (hμ : μ.parts = (↑L : Multiset ℕ)) (hL : L.Pairwise (· ≥ ·)) :
    μ.sortedParts = L := by
  unfold Nat.Partition.sortedParts
  rw [hμ, Multiset.coe_sort]
  exact List.mergeSort_eq_self (r := (· ≥ ·)) hL

/-- Bridge to compute `hookLengthProduct` from an explicit sorted parts list `L`;
once `L` is a literal the residual product over `cellsOfRowLens L` is `Nat.find`-free
and closes by `decide`. -/
theorem hookLengthProduct_eq_of {m : ℕ} (μ : Nat.Partition m) (L : List ℕ) (v : ℕ)
    (hL : μ.sortedParts = L)
    (hv : ∏ x ∈ YoungDiagram.cellsOfRowLens L,
            (L.getD x.1 0
              + ((Finset.range L.length).filter
                  (fun r => x.2 < L.getD r 0)).card - x.1 - x.2 - 1) = v) :
    μ.toYoungDiagram.hookLengthProduct = v := by
  rw [hookLengthProduct_eq_compute]
  have hcells : μ.toYoungDiagram.cells = YoungDiagram.cellsOfRowLens μ.sortedParts := rfl
  rw [hcells, hL]
  exact hv

/-- `∏_{k<n} (n - k) = n!`, the hook-length product of a single row (or column). -/
theorem prod_range_sub (n : ℕ) : ∏ k ∈ Finset.range n, (n - k) = n.factorial := by
  rw [← Finset.prod_range_reflect (fun k => n - k) n]
  rw [show (∏ j ∈ Finset.range n, (n - (n - 1 - j))) = ∏ j ∈ Finset.range n, (j + 1) from
    Finset.prod_congr rfl (fun i hi => by rw [Finset.mem_range] at hi; omega)]
  exact Finset.prod_range_add_one_eq_factorial n

/-! ## The one-row partition `(n)`: the trivial representation -/

/-- The partition `(n)` of `n` (a single row of length `n`). -/
def rowPartition (n : ℕ) (hn : 0 < n) : Nat.Partition n where
  parts := {n}
  parts_pos := fun {i} hi => by rw [Multiset.mem_singleton] at hi; omega
  parts_sum := by simp

theorem sortedParts_rowPartition (n : ℕ) (hn : 0 < n) :
    (rowPartition n hn).sortedParts = [n] :=
  sortedParts_eq_of _ [n] rfl (by simp)

theorem hookLengthProduct_rowPartition (n : ℕ) (hn : 0 < n) :
    (rowPartition n hn).toYoungDiagram.hookLengthProduct = n.factorial := by
  refine hookLengthProduct_eq_of _ [n] _ (sortedParts_rowPartition n hn) ?_
  have hcells : YoungDiagram.cellsOfRowLens [n] = ({0} : Finset ℕ) ×ˢ Finset.range n := by
    simp [YoungDiagram.cellsOfRowLens]
  rw [hcells, Finset.prod_product, Finset.prod_singleton, ← prod_range_sub n]
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

/-- The partition `(1,…,1)` of `n` (a single column of height `n`). -/
def columnPartition (n : ℕ) (_hn : 0 < n) : Nat.Partition n where
  parts := Multiset.replicate n 1
  parts_pos := fun {i} hi => by have := Multiset.eq_of_mem_replicate hi; omega
  parts_sum := by rw [Multiset.sum_replicate]; simp

theorem sortedParts_columnPartition (n : ℕ) (hn : 0 < n) :
    (columnPartition n hn).sortedParts = List.replicate n 1 :=
  sortedParts_eq_of _ (List.replicate n 1) (Multiset.coe_replicate n 1).symm
    (List.pairwise_replicate_of_refl)

theorem hookLengthProduct_columnPartition (n : ℕ) (hn : 0 < n) :
    (columnPartition n hn).toYoungDiagram.hookLengthProduct = n.factorial := by
  refine hookLengthProduct_eq_of _ (List.replicate n 1) _
    (sortedParts_columnPartition n hn) ?_
  have hcells : YoungDiagram.cellsOfRowLens (List.replicate n 1)
      = (Finset.range n) ×ˢ ({0} : Finset ℕ) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cellsOfRowLens, List.length_replicate, List.getElem_replicate,
      Nat.lt_one_iff, Finset.mem_product, Finset.mem_range, Finset.mem_singleton, exists_prop]
  rw [hcells, Finset.prod_product, ← prod_range_sub n]
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

/-- **Etingof Example 5.12.3.** For the one-row partition `λ = (n)` the Specht
module `V_{(n)}` is the trivial representation of `Sₙ`; in particular it is
one-dimensional. (Here `P_λ = Sₙ`, `Q_λ = {1}`, so `c_λ` is the symmetrizer.) -/
theorem Example5_12_3_trivial (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (SpechtModule n (rowPartition n hn)) = 1 := by
  rw [finrank_spechtModule_eq_card_syt_general, card_standardYoungTableau_eq,
      hookLengthProduct_rowPartition n hn]
  exact Nat.div_self (Nat.factorial_pos n)

/-- **Etingof Example 5.12.3.** For the one-column partition `λ = (1,…,1)` the
Specht module `V_{(1ⁿ)}` is the sign representation of `Sₙ`; in particular it is
one-dimensional. (Here `Q_λ = Sₙ`, `P_λ = {1}`, so `c_λ` is the antisymmetrizer.) -/
theorem Example5_12_3_sign (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (SpechtModule n (columnPartition n hn)) = 1 := by
  rw [finrank_spechtModule_eq_card_syt_general, card_standardYoungTableau_eq,
      hookLengthProduct_columnPartition n hn]
  exact Nat.div_self (Nat.factorial_pos n)

/-! ### The four small explicit partitions -/

/-- The partition `(2,1)` of `3`. -/
def p_21 : Nat.Partition 3 where
  parts := {2, 1}
  parts_pos := by decide
  parts_sum := by decide

/-- The partition `(2,2)` of `4`. -/
def p_22 : Nat.Partition 4 where
  parts := {2, 2}
  parts_pos := by decide
  parts_sum := by decide

/-- The partition `(3,1)` of `4`. -/
def p_31 : Nat.Partition 4 where
  parts := {3, 1}
  parts_pos := by decide
  parts_sum := by decide

/-- The partition `(2,1,1)` of `4`. -/
def p_211 : Nat.Partition 4 where
  parts := {2, 1, 1}
  parts_pos := by decide
  parts_sum := by decide

/-- **Etingof Example 5.12.3, `n = 3`.** `dim V_{(2,1)} = 2`: the standard
representation `ℂ²` of `S₃`. -/
theorem Example5_12_3_dim_21 :
    Module.finrank ℂ (SpechtModule 3 p_21) = 2 := by
  rw [finrank_spechtModule_eq_card_syt_general, card_standardYoungTableau_eq,
      hookLengthProduct_eq_of p_21 [2, 1] 3 (sortedParts_eq_of _ [2, 1] rfl (by decide))
        (by decide)]
  rfl

/-- **Etingof Example 5.12.3, `n = 4`.** `dim V_{(2,2)} = 2`. -/
theorem Example5_12_3_dim_22 :
    Module.finrank ℂ (SpechtModule 4 p_22) = 2 := by
  rw [finrank_spechtModule_eq_card_syt_general, card_standardYoungTableau_eq,
      hookLengthProduct_eq_of p_22 [2, 2] 12 (sortedParts_eq_of _ [2, 2] rfl (by decide))
        (by decide)]
  rfl

/-- **Etingof Example 5.12.3, `n = 4`.** `dim V_{(3,1)} = 3` (the `ℂ³₋`). -/
theorem Example5_12_3_dim_31 :
    Module.finrank ℂ (SpechtModule 4 p_31) = 3 := by
  rw [finrank_spechtModule_eq_card_syt_general, card_standardYoungTableau_eq,
      hookLengthProduct_eq_of p_31 [3, 1] 8 (sortedParts_eq_of _ [3, 1] rfl (by decide))
        (by decide)]
  rfl

/-- **Etingof Example 5.12.3, `n = 4`.** `dim V_{(2,1,1)} = 3` (the `ℂ³₊`). -/
theorem Example5_12_3_dim_211 :
    Module.finrank ℂ (SpechtModule 4 p_211) = 3 := by
  rw [finrank_spechtModule_eq_card_syt_general, card_standardYoungTableau_eq,
      hookLengthProduct_eq_of p_211 [2, 1, 1] 8 (sortedParts_eq_of _ [2, 1, 1] rfl (by decide))
        (by decide)]
  rfl

/-! ## Representation-level structure: the trivial and sign characters

The book's claim is stronger than a dimension count: `V_{(n)}` is the *trivial*
representation and `V_{(1ⁿ)}` is the *sign* representation. A dimension of `1`
is necessary but not sufficient — `Sₙ` has exactly two one-dimensional
representations, and the book asserts a specific one in each case. We pin this
down as genuine `ℂ[Sₙ]`-module statements: every group element `σ` acts on
`V_{(n)}` as the identity (`Example5_12_3_trivial_rep`), and on `V_{(1ⁿ)}` as
multiplication by `sign σ` (`Example5_12_3_sign_rep`).

The arguments are the classical ones. For `(n)` the column group `Q_λ` is
trivial, so `c_λ = a_λ = ∑_{g} g` and `g · a_λ = a_λ`; for `(1ⁿ)` the row group
`P_λ` is trivial, so `c_λ = b_λ = ∑_g sign(g)·g` and `g · b_λ = sign(g)·b_λ`.
Combined with `dim V_λ = 1`, the action on the whole one-dimensional module is
determined by its action on the generator `c_λ`. -/

/-- For the one-column partition `(1ⁿ)` every cell lies in column `0`. -/
theorem colOfPos_replicate_one (n k : ℕ) : colOfPos (List.replicate n 1) k = 0 := by
  induction n generalizing k with
  | zero => simp [colOfPos]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [colOfPos]
    split_ifs with h
    · omega
    · exact ih (k - 1)

/-- For the one-column partition `(1ⁿ)` the row of cell `k` is `k` itself. -/
theorem rowOfPos_replicate_one (n : ℕ) :
    ∀ k, k < n → rowOfPos (List.replicate n 1) k = k := by
  induction n with
  | zero => intro k hk; omega
  | succ m ih =>
    intro k hk
    rw [List.replicate_succ]
    simp only [rowOfPos]
    split_ifs with h
    · omega
    · rw [ih (k - 1) (by omega)]; omega

/-! ### The one-row partition `(n)`: trivial action -/

/-- For the one-row partition `(n)`, every permutation preserves rows
(there is only one row), so `P_λ = Sₙ`. -/
theorem mem_rowSubgroup_rowPartition (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ RowSubgroup n (rowPartition n hn) := by
  have hrow : ∀ j : Fin n, rowOfPos [n] j.val = 0 := fun j => by
    simp only [rowOfPos]; exact if_pos j.isLt
  intro k
  rw [sortedParts_rowPartition n hn, hrow (σ k), hrow k]

/-- For the one-row partition `(n)`, the column group `Q_λ` is trivial: every
cell is in its own column, so a column-preserving permutation is the identity. -/
theorem columnSubgroup_rowPartition_eq_one (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ ColumnSubgroup n (rowPartition n hn)) : σ = 1 := by
  have hcol : ∀ j : Fin n, colOfPos [n] j.val = j.val := fun j => by
    simp only [colOfPos]; exact if_pos j.isLt
  apply Equiv.Perm.ext
  intro k
  have h := hσ k
  rw [sortedParts_rowPartition n hn, hcol (σ k), hcol k] at h
  rw [Equiv.Perm.one_apply]
  exact Fin.ext h

/-- For the one-row partition `(n)`, the column antisymmetrizer `b_λ` is `1`. -/
theorem columnAntisymmetrizer_rowPartition (n : ℕ) (hn : 0 < n) :
    ColumnAntisymmetrizer n (rowPartition n hn) = 1 := by
  classical
  have htriv : ∀ g : ↥(ColumnSubgroup n (rowPartition n hn)), (g : Equiv.Perm (Fin n)) = 1 :=
    fun g => columnSubgroup_rowPartition_eq_one n hn g.val g.prop
  haveI : Unique ↥(ColumnSubgroup n (rowPartition n hn)) :=
    ⟨⟨⟨1, (ColumnSubgroup n (rowPartition n hn)).one_mem⟩⟩, fun g => Subtype.ext (htriv g)⟩
  simp only [ColumnAntisymmetrizer, htriv, Units.val_one, Int.cast_one,
    one_smul, map_one, Finset.sum_const, Finset.card_univ, Fintype.card_unique]

/-- `c_λ` for the one-row partition equals the full symmetrizer `a_λ = ∑_g g`,
and every group element absorbs into it: `of(σ) · c_λ = c_λ`. -/
theorem of_mul_youngSymmetrizer_rowPartition (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ * YoungSymmetrizer n (rowPartition n hn)
      = YoungSymmetrizer n (rowPartition n hn) := by
  rw [YoungSymmetrizer, columnAntisymmetrizer_rowPartition n hn, one_mul]
  exact of_row_mul_RowSymmetrizer σ (mem_rowSubgroup_rowPartition n hn σ)

/-! ### The one-column partition `(1ⁿ)`: sign action -/

/-- For the one-column partition `(1ⁿ)`, every permutation preserves columns
(there is only one column), so `Q_λ = Sₙ`. -/
theorem mem_columnSubgroup_columnPartition (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ ColumnSubgroup n (columnPartition n hn) := by
  intro k
  rw [sortedParts_columnPartition n hn, colOfPos_replicate_one, colOfPos_replicate_one]

/-- For the one-column partition `(1ⁿ)`, the row group `P_λ` is trivial: every
cell is in its own row, so a row-preserving permutation is the identity. -/
theorem rowSubgroup_columnPartition_eq_one (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ RowSubgroup n (columnPartition n hn)) : σ = 1 := by
  apply Equiv.Perm.ext
  intro k
  have h := hσ k
  rw [sortedParts_columnPartition n hn,
    rowOfPos_replicate_one n (σ k).val (σ k).isLt,
    rowOfPos_replicate_one n k.val k.isLt] at h
  rw [Equiv.Perm.one_apply]
  exact Fin.ext h

/-- For the one-column partition `(1ⁿ)`, the row symmetrizer `a_λ` is `1`. -/
theorem rowSymmetrizer_columnPartition (n : ℕ) (hn : 0 < n) :
    RowSymmetrizer n (columnPartition n hn) = 1 := by
  classical
  have htriv : ∀ g : ↥(RowSubgroup n (columnPartition n hn)), (g : Equiv.Perm (Fin n)) = 1 :=
    fun g => rowSubgroup_columnPartition_eq_one n hn g.val g.prop
  haveI : Unique ↥(RowSubgroup n (columnPartition n hn)) :=
    ⟨⟨⟨1, (RowSubgroup n (columnPartition n hn)).one_mem⟩⟩, fun g => Subtype.ext (htriv g)⟩
  simp only [RowSymmetrizer, htriv, map_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_nsmul]

/-- `c_λ` for the one-column partition equals the full antisymmetrizer
`b_λ = ∑_g sign(g)·g`, and `of(σ) · c_λ = sign(σ) · c_λ`. -/
theorem of_mul_youngSymmetrizer_columnPartition (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ * YoungSymmetrizer n (columnPartition n hn)
      = ((↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) • YoungSymmetrizer n (columnPartition n hn) := by
  rw [YoungSymmetrizer, rowSymmetrizer_columnPartition n hn, mul_one]
  exact of_col_mul_ColumnAntisymmetrizer σ (mem_columnSubgroup_columnPartition n hn σ)

/-! ### From the generator to the whole module -/

/-- If `V_λ` is one-dimensional and the group element `σ` scales the generator
`c_λ` by `χ`, then `σ` acts on every vector of `V_λ` by `χ`. (Since `V_λ` is
one-dimensional over `ℂ`, it equals `ℂ · c_λ`, so the `ℂ[Sₙ]`-action is
determined by its value on `c_λ`.) -/
theorem spechtModule_smul_eq (n : ℕ) (la : Nat.Partition n) (σ : Equiv.Perm (Fin n)) (χ : ℂ)
    (hdim : Module.finrank ℂ (SpechtModule n la) = 1)
    (hgen : (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : SymGroupAlgebra n)
        * YoungSymmetrizer n la = χ • YoungSymmetrizer n la)
    (v : SpechtModule n la) :
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : SymGroupAlgebra n) • v = χ • v := by
  classical
  have hcne : YoungSymmetrizer n la ≠ 0 := by
    intro h0
    have hbot : SpechtModule n la = ⊥ := by
      rw [SpechtModule, h0]; exact Submodule.span_singleton_eq_bot.mpr rfl
    rw [hbot, Module.finrank_zero_of_subsingleton] at hdim
    exact one_ne_zero hdim.symm
  have hmem_c : YoungSymmetrizer n la ∈ SpechtModule n la := Submodule.subset_span rfl
  have hspan_le : Submodule.span ℂ {YoungSymmetrizer n la}
      ≤ (SpechtModule n la).restrictScalars ℂ := by
    rw [Submodule.span_singleton_le_iff_mem]; exact hmem_c
  have hfin : Module.finrank ℂ ((SpechtModule n la).restrictScalars ℂ) = 1 := hdim
  have hspaneq : Submodule.span ℂ {YoungSymmetrizer n la}
      = (SpechtModule n la).restrictScalars ℂ :=
    Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hfin, finrank_span_singleton hcne])
  have hv_mem : (v : SymGroupAlgebra n) ∈ Submodule.span ℂ {YoungSymmetrizer n la} := by
    rw [hspaneq]; exact v.2
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hv_mem
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_smul_of_tower, smul_eq_mul, ← hz,
    Algebra.mul_smul_comm, hgen, smul_comm]

/-- **Etingof Example 5.12.3 (trivial representation).** For the one-row
partition `λ = (n)`, every group element acts as the identity on the Specht
module `V_{(n)}`: it is the trivial representation of `Sₙ`. -/
theorem Example5_12_3_trivial_rep (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (v : SpechtModule n (rowPartition n hn)) :
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : SymGroupAlgebra n) • v = v := by
  have h := spechtModule_smul_eq n (rowPartition n hn) σ 1 (Example5_12_3_trivial n hn)
    (by rw [one_smul]; exact of_mul_youngSymmetrizer_rowPartition n hn σ) v
  rwa [one_smul] at h

/-- **Etingof Example 5.12.3 (sign representation).** For the one-column
partition `λ = (1,…,1)`, every group element `σ` acts as multiplication by
`sign σ` on the Specht module `V_{(1ⁿ)}`: it is the sign representation of
`Sₙ`. -/
theorem Example5_12_3_sign_rep (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin n))
    (v : SpechtModule n (columnPartition n hn)) :
    (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ : SymGroupAlgebra n) • v
      = ((↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) • v :=
  spechtModule_smul_eq n (columnPartition n hn) σ _ (Example5_12_3_sign n hn)
    (of_mul_youngSymmetrizer_columnPartition n hn σ) v

end Example5_12_3

end Etingof

import EtingofRepresentationTheory.Chapter5.CharValueHookFormula
import EtingofRepresentationTheory.Chapter5.FRTHelpers

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

end Example5_12_3

end Etingof

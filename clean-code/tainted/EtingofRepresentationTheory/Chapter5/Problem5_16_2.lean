import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible
import EtingofRepresentationTheory.Chapter5.Definition5_14_2
import EtingofRepresentationTheory.Chapter5.PolytabloidBasis

/-!
# Problem 5.16.2: the sum of transpositions acts on `V_λ` by the content

**Problem 5.16.2.** The **content** `c(λ)` of a Young diagram `λ` is the sum
`∑_j ∑_{i=1}^{λ_j} (i - j)`. Let `C = ∑_{i < j} (ij) ∈ ℂ[S_n]` be the sum of all
transpositions. Show that `C` acts on the Specht module `V_λ` by multiplication by `c(λ)`.

## Formalization

* `sumTranspositions n : ℂ[S_n]` is `∑_{i < j} (i j)`, the sum over ordered pairs `i < j` of
  the transposition `Equiv.swap i j`.
* `content la : ℤ` is `∑_{(i,j) ∈ cells} (j - i)`, summing `col − row` over the cells of the
  Young diagram of `λ` (cells are `0`-indexed `(row, col)`, so `col − row` matches the book's
  `i − j` with `i` = column, `j` = row).

`C` is central in `ℂ[S_n]` (a sum over a full conjugacy class), so left multiplication by `C`
preserves the left ideal `V_λ = ℂ[S_n]·c_λ` and, `V_λ` being irreducible, acts as a scalar
(Schur's lemma over the algebraically closed field `ℂ`). The scalar is read off by evaluating on
the Young symmetrizer `c_λ` and taking the coefficient of the identity permutation; that scalar is
the content `c(λ)`.

## Proof structure

* `sumTranspositions_central`: `C` commutes with every element of `ℂ[S_n]`.
* `sumTranspositions_mul_youngSymmetrizer`: `C · c_λ = c(λ) • c_λ`, proved by Schur (scalar
  existence) plus the coefficient identity `sumTranspositions_youngSymmetrizer_coeff_one`.
* The main theorem reduces to the eigenvalue equation on `c_λ` using centrality.
-/

namespace Etingof

open scoped Classical

local instance problem5162CoeFun {R M : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R M) (fun _ => M → R) :=
  ⟨fun a => a.coeff⟩

/-- `C = ∑_{i < j} (i j)`: the sum of all transpositions in `ℂ[S_n]`. -/
noncomputable def sumTranspositions (n : ℕ) : SymGroupAlgebra n :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2)

/-- The content `c(λ) = ∑_{cells (i,j)} (j − i)` of the Young diagram of `λ`
(cells are `0`-indexed `(row, col)`; `j − i = col − row`). -/
noncomputable def content {n : ℕ} (la : Nat.Partition n) : ℤ :=
  ∑ c ∈ la.toYoungDiagram.cells, ((c.2 : ℤ) - (c.1 : ℤ))

/-- Reindexing the transposition sum by an arbitrary permutation `h`: summing the conjugated
transpositions `swap (h i) (h j)` over pairs `i < j` recovers `C = ∑_{i<j} (ij)`, because
`(i, j) ↦ {h i, h j}` is a bijection of the set of unordered pairs. -/
private lemma sumTranspositions_reindex (n : ℕ) (h : Equiv.Perm (Fin n)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap (h p.1) (h p.2)) : SymGroupAlgebra n)
      = sumTranspositions n := by
  rw [sumTranspositions]
  refine Finset.sum_nbij'
    (i := fun p => if h p.1 < h p.2 then (h p.1, h p.2) else (h p.2, h p.1))
    (j := fun p => if h⁻¹ p.1 < h⁻¹ p.2 then (h⁻¹ p.1, h⁻¹ p.2) else (h⁻¹ p.2, h⁻¹ p.1))
    ?_ ?_ ?_ ?_ ?_
  · -- image lands in the filter
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hne : h p.1 ≠ h p.2 := fun e => (ne_of_lt hp) (h.injective e)
    split_ifs with hc
    · exact hc
    · exact lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
  · -- inverse image lands in the filter
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hne : h⁻¹ p.1 ≠ h⁻¹ p.2 := fun e => (ne_of_lt hp) (h⁻¹.injective e)
    split_ifs with hc
    · exact hc
    · exact lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
  · -- left inverse
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hc : h p.1 < h p.2
    · simp only [if_pos hc, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, if_pos hp, Prod.mk.eta]
    · simp only [if_neg hc, Equiv.Perm.coe_inv, Equiv.symm_apply_apply,
        if_neg (not_lt.mpr hp.le), Prod.mk.eta]
  · -- right inverse
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hc : h⁻¹ p.1 < h⁻¹ p.2
    · simp only [if_pos hc]
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, if_pos hp, Prod.mk.eta]
    · simp only [if_neg hc]
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, if_neg (not_lt.mpr hp.le), Prod.mk.eta]
  · -- summands match
    intro p hp
    by_cases hc : h p.1 < h p.2
    · simp only [if_pos hc]
    · simp only [if_neg hc]
      rw [Equiv.swap_comm]

/-- `C = ∑_{i<j}(ij)` commutes with every group-algebra element: it is the sum over the full
conjugacy class of transpositions, hence central in `ℂ[S_n]`. -/
lemma sumTranspositions_central (n : ℕ) (y : SymGroupAlgebra n) :
    sumTranspositions n * y = y * sumTranspositions n := by
  -- Reduce to `y = of g` by linearity.
  induction y using MonoidAlgebra.induction_on with
  | hM g =>
    -- `C * (of g) = ∑_{i<j} of(g · swap(g⁻¹ i)(g⁻¹ j))`, using `swap · g = g · swap(g⁻¹·)(g⁻¹·)`.
    have e1 : sumTranspositions n * MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
        = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
            MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (g * Equiv.swap (g⁻¹ p.1) (g⁻¹ p.2)) := by
      rw [sumTranspositions, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [← map_mul, Equiv.swap_mul_eq_mul_swap]
    -- Factor `of g` back out and reindex the remaining transposition sum.
    have e2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (g * Equiv.swap (g⁻¹ p.1) (g⁻¹ p.2))
        = MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g
            * ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
                MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap (g⁻¹ p.1) (g⁻¹ p.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [map_mul]
    rw [e1, e2, sumTranspositions_reindex n g⁻¹]
  | hadd f₁ f₂ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
  | hsmul r f h => rw [mul_smul_comm, smul_mul_assoc, h]

/-- The coefficient of a transposition `(i j)` (with `i ≠ j`) in the Young symmetrizer `c_λ`:
`+1` if `i, j` lie in the same row of the canonical tableau, `-1` if they lie in the same
column, and `0` otherwise. This is the convolution formula `c_λ(σ) = ∑_{q ∈ Q_λ} sign(q)·[q⁻¹σ ∈ P_λ]`
specialized to a transposition, using `P_λ ∩ Q_λ = {1}` (so each `σ` has at most one `q·p`
decomposition). -/
lemma youngSymmetrizer_swap_coeff (n : ℕ) (la : Nat.Partition n) {i j : Fin n} (hij : i ≠ j) :
    (YoungSymmetrizer n la : SymGroupAlgebra n) (Equiv.swap i j)
      = (if rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val then (1 : ℂ) else 0)
        - (if colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val then (1 : ℂ)
            else 0) := by
  classical
  have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
  have hbounds : ∀ k : Fin n, k.val < la.sortedParts.sum := fun k => by rw [hsum]; exact k.isLt
  by_cases hrow : rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val
  · -- same row ⟹ swap ∈ P_λ, coeff = 1; can't also share a column
    have hswapP : Equiv.swap i j ∈ RowSubgroup n la := swap_mem_RowSubgroup hrow
    have hcoeff : (YoungSymmetrizer n la : SymGroupAlgebra n) (Equiv.swap i j) = 1 := by
      have h := youngSymmetrizer_pq_coeff n la 1 (ColumnSubgroup n la).one_mem
        (Equiv.swap i j) hswapP
      simpa [Equiv.Perm.sign_one] using h
    have hcolne : colOfPos la.sortedParts i.val ≠ colOfPos la.sortedParts j.val := by
      intro hc
      exact hij (Fin.ext (rowOfPos_colOfPos_injective la.sortedParts i.val j.val
        (hbounds i) (hbounds j) hrow hc))
    rw [hcoeff, if_pos hrow, if_neg hcolne]; ring
  · by_cases hcol : colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val
    · -- same column ⟹ swap ∈ Q_λ, coeff = sign(swap) = -1
      have hswapQ : Equiv.swap i j ∈ ColumnSubgroup n la := swap_mem_ColumnSubgroup hcol
      have hcoeff : (YoungSymmetrizer n la : SymGroupAlgebra n) (Equiv.swap i j)
          = ((Equiv.Perm.sign (Equiv.swap i j) : ℤ) : ℂ) := by
        have h := youngSymmetrizer_pq_coeff n la (Equiv.swap i j) hswapQ 1
          (RowSubgroup n la).one_mem
        simpa using h
      rw [hcoeff, Equiv.Perm.sign_swap hij, if_neg hrow, if_pos hcol]; norm_num
    · -- different row and column ⟹ coeff = 0
      have hzero : (YoungSymmetrizer n la : SymGroupAlgebra n) (Equiv.swap i j) = 0 := by
        by_contra hne
        obtain ⟨q, hq, p, hp, hqp⟩ := youngSymmetrizer_support n la (Equiv.swap i j) hne
        -- `p` fixes every position outside `{i, j}`
        have hpfix : ∀ k : Fin n, k ≠ i → k ≠ j → p k = k := by
          intro k hki hkj
          have hsk : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
          have hqpk : q (p k) = k := by
            have hcompose : (q * p) k = k := by rw [← hqp]; exact hsk
            rwa [Equiv.Perm.mul_apply] at hcompose
          have hpk_eq : p k = q⁻¹ k := by
            have h2 := congrArg (fun x => q⁻¹ x) hqpk
            simpa using h2
          have hrowpk : rowOfPos la.sortedParts (p k).val = rowOfPos la.sortedParts k.val := hp k
          have hcolpk : colOfPos la.sortedParts (p k).val = colOfPos la.sortedParts k.val := by
            rw [hpk_eq]; exact (ColumnSubgroup n la).inv_mem hq k
          exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts (p k).val k.val
            (hbounds _) (hbounds k) hrowpk hcolpk)
        -- hence `p i ∈ {i, j}`
        have hpi : p i = i ∨ p i = j := by
          by_contra hcon
          push Not at hcon
          obtain ⟨hpi_i, hpi_j⟩ := hcon
          exact hpi_i (p.injective (hpfix (p i) hpi_i hpi_j))
        rcases hpi with h | h
        · -- p i = i ⟹ q i = j ⟹ i, j share a column
          have hqi : q i = j := by
            have h1 : (q * p) i = j := by rw [← hqp, Equiv.swap_apply_left]
            rwa [Equiv.Perm.mul_apply, h] at h1
          have hcc : colOfPos la.sortedParts (q i).val = colOfPos la.sortedParts i.val := hq i
          rw [hqi] at hcc
          exact hcol hcc.symm
        · -- p i = j ⟹ i, j share a row
          have hrr : rowOfPos la.sortedParts (p i).val = rowOfPos la.sortedParts i.val := hp i
          rw [h] at hrr
          exact hrow hrr.symm
      rw [hzero, if_neg hrow, if_neg hcol]; ring

/-! ### Counting infrastructure for the content identity -/

/-- Canonical decomposition of a position: `m = (offset of its row) + (its column)`. -/
private lemma pos_decomp_list (parts : List ℕ) (m : ℕ) (hm : m < parts.sum) :
    m = (parts.take (rowOfPos parts m)).sum + colOfPos parts m := by
  have hrlen : rowOfPos parts m < parts.length := rowOfPos_lt_length parts m hm
  have hclt : colOfPos parts m < parts[rowOfPos parts m] := colOfPos_lt_getElem parts m hm
  obtain ⟨hcr, hcc⟩ := rowOfPos_colOfPos_canonical parts (rowOfPos parts m) (colOfPos parts m)
    hrlen hclt
  have hlt := canonical_pos_lt_sum parts (rowOfPos parts m) (colOfPos parts m) hrlen hclt
  exact (rowOfPos_colOfPos_injective parts
    ((parts.take (rowOfPos parts m)).sum + colOfPos parts m) m hlt hm hcr hcc).symm

/-- The number of positions in a half-open interval `[a, b)` of `Fin n` is `b - a`. -/
private lemma card_val_Ico (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => a ≤ i.val ∧ i.val < b)).card = b - a := by
  have hsub : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < a)
      ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < b) := by
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hdiff : (Finset.univ : Finset (Fin n)).filter (fun i => a ≤ i.val ∧ i.val < b)
      = (Finset.univ.filter (fun i => i.val < b)) \ (Finset.univ.filter (fun i => i.val < a)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]; omega
  rw [hdiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_filter_val_lt n b hb,
    card_filter_val_lt n a (le_trans hab hb)]

/-- The number of positions before `j` in the same row as `j` equals the column index of `j`. -/
private lemma card_before_sameRow (n : ℕ) (la : Nat.Partition n) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i =>
      i < j ∧ rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val)).card
      = colOfPos la.sortedParts j.val := by
  have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
  set r := rowOfPos la.sortedParts j.val with hr
  have hjdecomp : j.val = (la.sortedParts.take r).sum + colOfPos la.sortedParts j.val := by
    have h := pos_decomp_list la.sortedParts j.val (by rw [hsum]; exact j.isLt)
    rw [← hr] at h; exact h
  have hset : (Finset.univ : Finset (Fin n)).filter (fun i =>
        i < j ∧ rowOfPos la.sortedParts i.val = r)
      = (Finset.univ : Finset (Fin n)).filter (fun i =>
          (la.sortedParts.take r).sum ≤ i.val ∧ i.val < j.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    have hib : i.val < la.sortedParts.sum := by rw [hsum]; exact i.isLt
    have hjb : j.val < la.sortedParts.sum := by rw [hsum]; exact j.isLt
    constructor
    · rintro ⟨hij, hri⟩
      refine ⟨?_, hij⟩
      by_contra hlt
      push Not at hlt
      have : rowOfPos la.sortedParts i.val < r :=
        (rowOfPos_lt_iff la.sortedParts i.val r hib).mpr hlt
      omega
    · rintro ⟨hge, hij⟩
      refine ⟨hij, ?_⟩
      have hnlt : ¬ (rowOfPos la.sortedParts i.val < r) := by
        rw [rowOfPos_lt_iff la.sortedParts i.val r hib]; omega
      have hjr1 : rowOfPos la.sortedParts j.val < r + 1 := by rw [← hr]; omega
      have hjr1' : j.val < (la.sortedParts.take (r+1)).sum :=
        (rowOfPos_lt_iff la.sortedParts j.val (r+1) hjb).mp hjr1
      have hir1 : rowOfPos la.sortedParts i.val < r + 1 :=
        (rowOfPos_lt_iff la.sortedParts i.val (r+1) hib).mpr (by omega)
      omega
  rw [hset, card_val_Ico n ((la.sortedParts.take r).sum) j.val (by omega) (le_of_lt j.isLt)]
  omega

/-- The number of positions before `j` in the same column as `j` equals the row index of `j`. -/
private lemma card_before_sameCol (n : ℕ) (la : Nat.Partition n) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i =>
      i < j ∧ colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val)).card
      = rowOfPos la.sortedParts j.val := by
  have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
  have hsorted : la.sortedParts.Pairwise (· ≥ ·) := sortedParts_sorted la
  have hjb : j.val < la.sortedParts.sum := by rw [hsum]; exact j.isLt
  have hrlen : rowOfPos la.sortedParts j.val < la.sortedParts.length :=
    rowOfPos_lt_length la.sortedParts j.val hjb
  have hclt : colOfPos la.sortedParts j.val < la.sortedParts[rowOfPos la.sortedParts j.val] :=
    colOfPos_lt_getElem la.sortedParts j.val hjb
  have hjdecomp := pos_decomp_list la.sortedParts j.val hjb
  set r := rowOfPos la.sortedParts j.val with hr
  set c := colOfPos la.sortedParts j.val with hc
  have hmono : ∀ a b : ℕ, a ≤ b → (la.sortedParts.take a).sum ≤ (la.sortedParts.take b).sum := by
    intro a b hab
    have he : la.sortedParts.take a = (la.sortedParts.take b).take a := by
      rw [List.take_take, min_eq_left hab]
    rw [he]
    exact List.Sublist.sum_le_sum (List.take_sublist a (la.sortedParts.take b))
      (fun _ _ => Nat.zero_le _)
  rw [← Finset.card_range r]
  refine Finset.card_bij (fun i _ => rowOfPos la.sortedParts i.val) ?_ ?_ ?_
  · -- forward map lands in `range r`
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, hij, hcoli⟩ := hi
    rw [Fin.lt_def] at hij
    have hib : i.val < la.sortedParts.sum := by rw [hsum]; exact i.isLt
    have hidecomp : i.val = (la.sortedParts.take (rowOfPos la.sortedParts i.val)).sum + c := by
      have h := pos_decomp_list la.sortedParts i.val hib
      rw [hcoli] at h; exact h
    rw [Finset.mem_range]
    by_contra hle
    push Not at hle
    have : (la.sortedParts.take r).sum ≤ (la.sortedParts.take (rowOfPos la.sortedParts i.val)).sum :=
      hmono r _ hle
    omega
  · -- injective
    intro i₁ hi₁ i₂ hi₂ heq
    rw [Finset.mem_filter] at hi₁ hi₂
    obtain ⟨-, -, hcoli₁⟩ := hi₁
    obtain ⟨-, -, hcoli₂⟩ := hi₂
    have hb₁ : i₁.val < la.sortedParts.sum := by rw [hsum]; exact i₁.isLt
    have hb₂ : i₂.val < la.sortedParts.sum := by rw [hsum]; exact i₂.isLt
    exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts i₁.val i₂.val hb₁ hb₂ heq
      (by rw [hcoli₁, hcoli₂]))
  · -- surjective
    intro b hb
    rw [Finset.mem_range] at hb
    have hblen : b < la.sortedParts.length := lt_trans hb hrlen
    have hcb : c < la.sortedParts[b] :=
      col_exists_earlier_row la.sortedParts hsorted r b c hrlen hblen (le_of_lt hb) hclt
    obtain ⟨hcr', hcc'⟩ := rowOfPos_colOfPos_canonical la.sortedParts b c hblen hcb
    have hmlt : (la.sortedParts.take b).sum + c < la.sortedParts.sum :=
      canonical_pos_lt_sum la.sortedParts b c hblen hcb
    have hmn : (la.sortedParts.take b).sum + c < n := lt_of_lt_of_eq hmlt hsum
    -- strict monotonicity: (take b).sum < (take r).sum
    have hstep : (la.sortedParts.take (b+1)).sum = (la.sortedParts.take b).sum
        + la.sortedParts[b] := List.sum_take_succ la.sortedParts b hblen
    have hpos : 0 < la.sortedParts[b] := lt_of_le_of_lt (Nat.zero_le c) hcb
    have hstrict : (la.sortedParts.take b).sum < (la.sortedParts.take r).sum := by
      have h1 : (la.sortedParts.take (b+1)).sum ≤ (la.sortedParts.take r).sum := hmono _ _ hb
      omega
    refine ⟨⟨(la.sortedParts.take b).sum + c, hmn⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hcc'⟩
      rw [Fin.lt_def]
      exact (by omega : (la.sortedParts.take b).sum + c < j.val)
    · exact hcr'

/-- The content, reindexed as a sum over positions: `c(λ) = ∑_k (col(k) − row(k))`. -/
private lemma content_eq_sum (n : ℕ) (la : Nat.Partition n) :
    (content la : ℤ)
      = ∑ k : Fin n, ((colOfPos la.sortedParts k.val : ℤ) - rowOfPos la.sortedParts k.val) := by
  have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
  have hbounds : ∀ k : Fin n, k.val < la.sortedParts.sum := fun k => by rw [hsum]; exact k.isLt
  rw [content]
  refine (Finset.sum_bij (fun (k : Fin n) _ =>
    ((rowOfPos la.sortedParts k.val, colOfPos la.sortedParts k.val) : ℕ × ℕ)) ?_ ?_ ?_ ?_).symm
  · -- lands in cells
    intro k _
    simp only [YoungDiagram.mem_cells, Nat.Partition.toYoungDiagram, YoungDiagram.mem_ofRowLens]
    exact ⟨rowOfPos_lt_length la.sortedParts k.val (hbounds k),
      colOfPos_lt_getElem la.sortedParts k.val (hbounds k)⟩
  · -- injective
    intro k₁ _ k₂ _ heq
    rw [Prod.mk.injEq] at heq
    exact Fin.ext (rowOfPos_colOfPos_injective la.sortedParts k₁.val k₂.val
      (hbounds k₁) (hbounds k₂) heq.1 heq.2)
  · -- surjective
    intro cell hcell
    simp only [YoungDiagram.mem_cells, Nat.Partition.toYoungDiagram,
      YoungDiagram.mem_ofRowLens] at hcell
    obtain ⟨hr, hc⟩ := hcell
    have hcgetD : cell.2 < la.sortedParts.getD cell.1 0 := by
      rw [List.getD_eq_getElem la.sortedParts 0 hr]; exact hc
    obtain ⟨m, hmlt, hmr, hmc⟩ := exists_pos_of_cell la.sortedParts cell.1 cell.2 hcgetD
    refine ⟨⟨m, lt_of_lt_of_eq hmlt hsum⟩, Finset.mem_univ _, ?_⟩
    simp only [hmr, hmc]
  · -- values match
    intro k _
    rfl

/-- For a fixed `j`, the signed count of transpositions `(i j)` with `i < j`:
`+1` for each earlier same-row position and `-1` for each earlier same-column one, totalling
`col(j) − row(j)`. -/
private lemma inner_transposition_sum (n : ℕ) (la : Nat.Partition n) (j : Fin n) :
    ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i < j),
      ((if rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val then (1 : ℂ) else 0)
        - (if colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val then (1 : ℂ) else 0))
      = (colOfPos la.sortedParts j.val : ℂ) - (rowOfPos la.sortedParts j.val : ℂ) := by
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, Finset.filter_filter,
    Finset.filter_filter, card_before_sameRow n la j, card_before_sameCol n la j]

/-- The combinatorial heart of the problem: summing the coefficient of each transposition `(ij)`
in the Young symmetrizer `c_λ = b_λ a_λ` gives the content `c(λ)`.

By the convolution formula `c_λ((ij)) = ∑_{q ∈ Q_λ, q⁻¹(ij) ∈ P_λ} sign(q)`, the coefficient is
`+1` when `i, j` share a row (`q = 1`, `(ij) ∈ P_λ`), `-1` when they share a column
(`q = (ij) ∈ Q_λ`, `p = 1`), and `0` otherwise. Grouping by the larger index `j`, the sum over
`i < j` telescopes to `col(j) − row(j)`, and summing over positions gives the content `c(λ)`. -/
private lemma youngSymmetrizer_transposition_sum_eq_content (n : ℕ) (la : Nat.Partition n) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (YoungSymmetrizer n la : SymGroupAlgebra n) (Equiv.swap p.1 p.2) = (content la : ℂ) := by
  classical
  have key : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (YoungSymmetrizer n la : SymGroupAlgebra n) (Equiv.swap p.1 p.2) =
        (if rowOfPos la.sortedParts p.1.val = rowOfPos la.sortedParts p.2.val then (1 : ℂ) else 0)
        - (if colOfPos la.sortedParts p.1.val = colOfPos la.sortedParts p.2.val then (1 : ℂ)
            else 0) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact youngSymmetrizer_swap_coeff n la (ne_of_lt hp.2)
  rw [Finset.sum_congr rfl key, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hstep : ∀ j : Fin n,
      (∑ i : Fin n, if i < j then
          ((if rowOfPos la.sortedParts i.val = rowOfPos la.sortedParts j.val then (1 : ℂ) else 0)
           - (if colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val then (1 : ℂ)
              else 0))
        else 0)
      = (colOfPos la.sortedParts j.val : ℂ) - (rowOfPos la.sortedParts j.val : ℂ) := by
    intro j
    rw [← Finset.sum_filter]
    exact inner_transposition_sum n la j
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_sub_distrib]
  have hcast : (content la : ℂ) = (∑ j : Fin n, (colOfPos la.sortedParts j.val : ℂ))
      - (∑ j : Fin n, (rowOfPos la.sortedParts j.val : ℂ)) := by
    have h2 : ((content la : ℤ) : ℂ)
        = ((∑ k : Fin n, ((colOfPos la.sortedParts k.val : ℤ) - rowOfPos la.sortedParts k.val)) : ℂ)
        := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (content_eq_sum n la)
    rw [h2]; push_cast; rw [Finset.sum_sub_distrib]
  rw [hcast]

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient of the identity permutation in `C · c_λ` equals the content `c(λ)`.
Expanding `C = ∑_{i<j} (ij)` and using `((ij) · c_λ)(e) = c_λ((ij))` reduces this to the
combinatorial identity `youngSymmetrizer_transposition_sum_eq_content`. -/
private lemma sumTranspositions_youngSymmetrizer_coeff_one (n : ℕ) (la : Nat.Partition n) :
    (sumTranspositions n * YoungSymmetrizer n la : SymGroupAlgebra n) 1 = (content la : ℂ) := by
  rw [← youngSymmetrizer_transposition_sum_eq_content n la, sumTranspositions, Finset.sum_mul,
    MonoidAlgebra.coeff_sum]
  change (Finsupp.applyAddHom 1)
    (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      ((MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2) :
        SymGroupAlgebra n) * YoungSymmetrizer n la).coeff) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  change (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2) *
    YoungSymmetrizer n la).coeff 1 = _
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply]
  simp [Equiv.swap_inv]

set_option backward.isDefEq.respectTransparency false in
/-- `C · c_λ = c(λ) • c_λ`: left multiplication by the central element `C` acts on the simple
module `V_λ` as the scalar `c(λ)`. Existence of *some* scalar is Schur's lemma; its value is
pinned down by the coefficient of the identity, using `c_λ(e) = 1`. -/
lemma sumTranspositions_mul_youngSymmetrizer (n : ℕ) (la : Nat.Partition n) :
    sumTranspositions n * YoungSymmetrizer n la = (content la : ℂ) • YoungSymmetrizer n la := by
  set A := SymGroupAlgebra n with hA
  set V := SpechtModule n la with hV
  -- Left multiplication by `C` as an `A`-linear endomorphism of `A` (centrality gives linearity).
  let LC : A →ₗ[A] A :=
    { toFun := fun x => sumTranspositions n * x
      map_add' := fun x y => mul_add _ _ _
      map_smul' := fun a x => by
        simp only [smul_eq_mul, RingHom.id_apply]
        rw [← mul_assoc, sumTranspositions_central n a, mul_assoc] }
  have hmaps : ∀ x ∈ V, LC x ∈ V := by
    intro x hx
    change sumTranspositions n * x ∈ V
    rw [← smul_eq_mul]
    exact V.smul_mem _ hx
  -- Restrict `LC` to the simple submodule `V`.
  let L : Module.End A V := LC.restrict hmaps
  -- Schur: any `A`-endomorphism of the simple module `V` is a scalar.
  haveI : IsSimpleModule A V := Theorem5_12_2_irreducible n la
  obtain ⟨μ, hμ⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
    (k := ℂ) (A := A) (V := V)).surjective L
  -- Evaluate on `c_λ ∈ V`.
  have hcl : YoungSymmetrizer n la ∈ V := Submodule.subset_span rfl
  have hLc : (L ⟨YoungSymmetrizer n la, hcl⟩ : A) = sumTranspositions n * YoungSymmetrizer n la :=
    LinearMap.coe_restrict_apply hmaps _
  have hscal : (L ⟨YoungSymmetrizer n la, hcl⟩ : A) = μ • (YoungSymmetrizer n la : A) := by
    rw [← hμ]
    simp [Module.algebraMap_end_apply]
  have hCeq : sumTranspositions n * YoungSymmetrizer n la = μ • YoungSymmetrizer n la := by
    rw [← hLc, hscal]
  -- Identify `μ` by reading off the coefficient at the identity permutation.
  have hμval : μ = (content la : ℂ) := by
    have h1 : (sumTranspositions n * YoungSymmetrizer n la : SymGroupAlgebra n) 1
        = (μ • YoungSymmetrizer n la : SymGroupAlgebra n) 1 := by rw [hCeq]
    rw [sumTranspositions_youngSymmetrizer_coeff_one] at h1
    rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      youngSymmetrizer_identity_coeff, mul_one] at h1
    exact h1.symm
  rw [hCeq, hμval]

/-- Problem 5.16.2. The sum of all transpositions `C = ∑_{i<j}(ij)` acts on the Specht module
`V_λ = ℂ[S_n]·c_λ` (by left multiplication) as multiplication by the content `c(λ)`. -/
theorem sumTranspositions_mul_eq_content_smul
    (n : ℕ) (la : Nat.Partition n)
    (x : SymGroupAlgebra n) (hx : x ∈ SpechtModule n la) :
    sumTranspositions n * x = (content la : ℂ) • x := by
  -- Every `x ∈ V_λ` is `a · c_λ`; use centrality to move `C` past `a`.
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [smul_eq_mul, ← mul_assoc, sumTranspositions_central, mul_assoc,
    sumTranspositions_mul_youngSymmetrizer, mul_smul_comm]

end Etingof

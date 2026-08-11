import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Remark 5.15.5: the positive-root order on partitions

For partitions `λ` and `μ` of `n`, the book writes `λ ≼ μ` when `μ - λ` is a sum of
vectors `e i - e j` with `i < j` (the *positive roots*). Remark 5.15.5 makes four
assertions: this is a partial order; `μ ≽ λ` implies `μ ≥ λ` in the dominance order;
the Specht-module character expands as

  `χ_λ = ∑_{μ ≽ λ} K̃_{μλ} χ_{U_μ}`

with `(K̃_{λμ})` the matrix inverse of the Kostka matrix `(K_{λμ})`; and consequently
`K_{μλ} = 0` unless `μ ≽ λ`.

All four are formalized here. The pivot is `Nat.Partition.rootLe_iff_dominates`: on
partitions of a fixed `n` the positive-root order and the dominance order *coincide*.
The book only asserts one implication, but the converse is what turns the existing
dominance-order vanishing statement (`Etingof.spechtMultiplicity_vanishing_general`)
into the root-order vanishing statement the remark records, so it is proved here rather
than assumed.

The character expansion is obtained by inverting the Kostka matrix. Triangularity makes
`K = 1 + N` with `N` supported strictly below the diagonal; grading the partitions of `n`
by `Etingof.domRank` makes `N` nilpotent, so the finite geometric series `∑_k (-N)^k` is a
two-sided inverse that is again supported on the order. That support statement is exactly
the restriction `μ ≽ λ` on the book's displayed sum.

## Main definitions

* `Nat.Partition.partAt` — the `i`-th part in non-increasing order, `0` past the end.
* `Nat.Partition.RootLe` — the positive-root order `λ ≼ μ`.
* `Etingof.kostkaMatrix`, `Etingof.inverseKostkaMatrix` — `(K_{λμ})` and `(K̃_{λμ})`.

## Main results

* `Nat.Partition.RootLe.refl`, `.trans`, `.antisymm` — it is a partial order.
* `Nat.Partition.RootLe.dominates` — `μ ≽ λ` implies `μ ≥ λ` (the book's implication).
* `Nat.Partition.Dominates.rootLe` — the converse.
* `Nat.Partition.rootLe_iff_dominates` — the resulting equivalence.
* `Etingof.spechtMultiplicity_vanishing_rootOrder` — `K_{μλ} = 0` unless `μ ≽ λ`.
* `Etingof.isUnit_kostkaMatrix`, `Etingof.mul_inverseKostkaMatrix` — `K̃` inverts `K`.
* `Etingof.inverseKostkaMatrix_eq_zero_of_not_rootLe` — `K̃_{μλ} = 0` unless `μ ≽ λ`.
* `Etingof.spechtCharacter_eq_sum_inverseKostka_rootLe` — the displayed expansion.

## Note on `Etingof.KostkaNumber`

`Etingof.kostkaMatrix` uses `Etingof.spechtMultiplicity`, the Young's-rule multiplicity of
`V_μ` in `U_λ`, which is the form Theorem 5.15.1 and its proof supply. The
semistandard-tableau basis of row invariants proves downstream that this equals
the tableau cardinal `Etingof.KostkaNumber` of Definition 5.14.2. Thus the matrix
used here is the classical Kostka matrix under that identification.
-/

namespace Etingof

/-! ## Indexing the parts of a partition -/

/-- The `i`-th part of `la` in non-increasing order, and `0` once `i` runs past the
last part. This is the `i`-th coordinate of `la` viewed as a vector, which is the
form Remark 5.15.5 uses. -/
noncomputable def _root_.Nat.Partition.partAt {n : ℕ} (la : Nat.Partition n) (i : ℕ) : ℕ :=
  la.sortedParts.getD i 0

/-- Splitting off the last entry of a truncated sum. Stated for `List.getD` so that it
also covers the case `k ≥ l.length`, where both sides are unchanged. -/
private theorem sum_take_succ_getD (l : List ℕ) (k : ℕ) :
    (l.take (k + 1)).sum = (l.take k).sum + l.getD k 0 := by
  rw [List.take_add_one, List.sum_append]
  congr 1
  rcases h : l[k]? with _ | x
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

/-- The sum of the first `k` parts, as a `Finset.range` sum of `partAt`. -/
theorem _root_.Nat.Partition.sum_take_eq_sum_partAt {n : ℕ} (la : Nat.Partition n) (k : ℕ) :
    (la.sortedParts.take k).sum = ∑ i ∈ Finset.range k, la.partAt i := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_take_succ_getD, ih, Finset.sum_range_succ]; rfl

/-- A partition of `n` has at most `n` parts, since every part is positive. -/
theorem _root_.Nat.Partition.sortedParts_length_le {n : ℕ} (la : Nat.Partition n) :
    la.sortedParts.length ≤ n := by
  have hsum : la.sortedParts.sum = n := by
    have hsort : (la.sortedParts : Multiset ℕ) = la.parts := la.parts.sort_eq (· ≥ ·)
    have : la.sortedParts.sum = la.parts.sum := by rw [← Multiset.sum_coe, hsort]
    rw [this, la.parts_sum]
  have hpos : ∀ x ∈ la.sortedParts, 1 ≤ x := fun x hx =>
    la.parts_pos ((Multiset.mem_sort _).mp hx)
  calc la.sortedParts.length ≤ la.sortedParts.sum := List.length_le_sum_of_one_le _ hpos
    _ = n := hsum

/-- Past the `n`-th place, the parts of a partition of `n` are all zero. -/
theorem _root_.Nat.Partition.partAt_eq_zero_of_le {n : ℕ} (la : Nat.Partition n) {i : ℕ}
    (hi : n ≤ i) : la.partAt i = 0 := by
  have := la.sortedParts_length_le
  simp [Nat.Partition.partAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by omega : la.sortedParts.length ≤ i)]

/-- Once `k` reaches `n`, the first `k` parts already exhaust the partition. -/
theorem _root_.Nat.Partition.sum_take_of_le {n : ℕ} (la : Nat.Partition n) {k : ℕ}
    (hk : n ≤ k) : (la.sortedParts.take k).sum = n := by
  have hlen : la.sortedParts.length ≤ k := le_trans la.sortedParts_length_le hk
  rw [List.take_of_length_le hlen]
  have hsort : (la.sortedParts : Multiset ℕ) = la.parts := la.parts.sort_eq (· ≥ ·)
  have : la.sortedParts.sum = la.parts.sum := by rw [← Multiset.sum_coe, hsort]
  rw [this, la.parts_sum]

/-! ## The positive-root order -/

/-- The positive root `e i - e j`, as an integer vector on part indices. -/
def rootVec (i j : ℕ) : ℕ → ℤ := fun k => (if i = k then 1 else 0) - (if j = k then 1 else 0)

/-- The positive-root order of Remark 5.15.5: `λ ≼ μ` when `μ - λ` is a sum of vectors
`e i - e j` with `i < j`. The list `L` records the multiset of positive roots used
(with repetitions). -/
def _root_.Nat.Partition.RootLe {n : ℕ} (la mu : Nat.Partition n) : Prop :=
  ∃ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 < p.2) ∧
    ∀ k : ℕ, (mu.partAt k : ℤ) = la.partAt k + (L.map (fun p => rootVec p.1 p.2 k)).sum

theorem _root_.Nat.Partition.RootLe.refl {n : ℕ} (la : Nat.Partition n) : la.RootLe la :=
  ⟨[], by simp, by simp⟩

theorem _root_.Nat.Partition.RootLe.trans {n : ℕ} {la mu nu : Nat.Partition n}
    (h₁ : la.RootLe mu) (h₂ : mu.RootLe nu) : la.RootLe nu := by
  obtain ⟨L₁, hL₁, hs₁⟩ := h₁
  obtain ⟨L₂, hL₂, hs₂⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    exacts [hL₁ p hp, hL₂ p hp]
  · intro k
    rw [List.map_append, List.sum_append, hs₂ k, hs₁ k]
    ring

/-! ### Partial sums of a sum of positive roots -/

/-- The partial sum of a single positive root: `∑_{m < k} (e i - e j)_m`. -/
private theorem sum_range_rootVec (i j k : ℕ) :
    ∑ m ∈ Finset.range k, rootVec i j m =
      (if i < k then (1 : ℤ) else 0) - (if j < k then 1 else 0) := by
  simp only [rootVec, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq (Finset.range k) i (fun _ => (1 : ℤ)),
    Finset.sum_ite_eq (Finset.range k) j (fun _ => (1 : ℤ))]
  simp [Finset.mem_range]

/-- Partial sums commute with the list of positive roots. -/
private theorem sum_range_list_rootVec (L : List (ℕ × ℕ)) (k : ℕ) :
    ∑ m ∈ Finset.range k, (L.map (fun p => rootVec p.1 p.2 m)).sum =
      (L.map (fun p => (if p.1 < k then (1 : ℤ) else 0) - (if p.2 < k then 1 else 0))).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih, sum_range_rootVec]

/-- The book's implication: `μ ≽ λ` implies `μ ≥ λ` in the dominance order. -/
theorem _root_.Nat.Partition.RootLe.dominates {n : ℕ} {la mu : Nat.Partition n}
    (h : la.RootLe mu) : Nat.Partition.Dominates mu la := by
  obtain ⟨L, hL, hs⟩ := h
  intro k
  -- Compare the two partial sums as integers.
  have key : ((la.sortedParts.take k).sum : ℤ) ≤ ((mu.sortedParts.take k).sum : ℤ) := by
    rw [la.sum_take_eq_sum_partAt k, mu.sum_take_eq_sum_partAt k]
    push_cast
    have hsum : ∑ i ∈ Finset.range k, (mu.partAt i : ℤ) =
        ∑ i ∈ Finset.range k, (la.partAt i : ℤ) +
          (L.map (fun p => (if p.1 < k then (1 : ℤ) else 0) - (if p.2 < k then 1 else 0))).sum := by
      rw [← sum_range_list_rootVec L k, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hs i
    have hnonneg : (0 : ℤ) ≤
        (L.map (fun p => (if p.1 < k then (1 : ℤ) else 0) - (if p.2 < k then 1 else 0))).sum := by
      refine List.sum_nonneg ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hlt := hL p hp
      -- `p.1 < p.2`, so the `e p.2` indicator can only fire when the `e p.1` one does.
      rcases Nat.lt_or_ge p.2 k with h2 | h2
      · have h1 : p.1 < k := by omega
        simp [h1, h2]
      · have h2' : ¬ p.2 < k := by omega
        rcases Nat.lt_or_ge p.1 k with h1 | h1
        · simp [h1, h2']
        · have h1' : ¬ p.1 < k := by omega
          simp [h1', h2']
    omega
  exact_mod_cast key

/-! ### The converse: dominance implies the positive-root order -/

/-- The defect `D k = S_k(μ) - S_k(λ)` of the two partial sums, as a natural number.
Under dominance this is the honest difference. -/
private noncomputable def domDefect {n : ℕ} (la mu : Nat.Partition n) (k : ℕ) : ℕ :=
  (mu.sortedParts.take k).sum - (la.sortedParts.take k).sum

private theorem domDefect_cast {n : ℕ} {la mu : Nat.Partition n}
    (h : Nat.Partition.Dominates mu la) (k : ℕ) :
    (domDefect la mu k : ℤ) =
      ((mu.sortedParts.take k).sum : ℤ) - ((la.sortedParts.take k).sum : ℤ) := by
  have := h k
  simp only [domDefect]
  omega

private theorem domDefect_eq_zero_of_le {n : ℕ} (la mu : Nat.Partition n) {k : ℕ}
    (hk : n ≤ k) : domDefect la mu k = 0 := by
  simp [domDefect, la.sum_take_of_le hk, mu.sum_take_of_le hk]

/-- The successive difference of the defects is the difference of the parts. -/
private theorem domDefect_succ_sub {n : ℕ} {la mu : Nat.Partition n}
    (h : Nat.Partition.Dominates mu la) (i : ℕ) :
    (domDefect la mu (i + 1) : ℤ) - (domDefect la mu i : ℤ) =
      (mu.partAt i : ℤ) - (la.partAt i : ℤ) := by
  rw [domDefect_cast h, domDefect_cast h, sum_take_succ_getD, sum_take_succ_getD]
  push_cast
  simp only [Nat.Partition.partAt]
  ring

/-- The witness list for `Dominates → RootLe`, built one simple root at a time:
`domWitnessAux la mu m` uses `D (k+1)` copies of the simple root `e k - e (k+1)` for
each `k < m`. -/
private noncomputable def domWitnessAux {n : ℕ} (la mu : Nat.Partition n) :
    ℕ → List (ℕ × ℕ)
  | 0 => []
  | k + 1 => domWitnessAux la mu k ++ List.replicate (domDefect la mu (k + 1)) (k, k + 1)

private theorem domWitnessAux_mem {n : ℕ} (la mu : Nat.Partition n) (m : ℕ) :
    ∀ p ∈ domWitnessAux la mu m, p.1 < p.2 := by
  induction m with
  | zero => simp [domWitnessAux]
  | succ m ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih p hp
    · rw [List.eq_of_mem_replicate hp]; omega

/-- The coordinatewise effect of the witness list at index `i`. -/
private theorem domWitnessAux_sum {n : ℕ} (la mu : Nat.Partition n) (m i : ℕ) :
    ((domWitnessAux la mu m).map (fun p => rootVec p.1 p.2 i)).sum =
      ∑ k ∈ Finset.range m, (domDefect la mu (k + 1) : ℤ) * rootVec k (k + 1) i := by
  induction m with
  | zero => simp [domWitnessAux]
  | succ m ih =>
    rw [domWitnessAux, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
      List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-- The `e i` component of the witness list: the sum telescopes to `D (i+1) - D i`. -/
private theorem domWitnessAux_coeff {n : ℕ} (la mu : Nat.Partition n) (i : ℕ) :
    ((domWitnessAux la mu n).map (fun p => rootVec p.1 p.2 i)).sum =
      (domDefect la mu (i + 1) : ℤ) - (domDefect la mu i : ℤ) := by
  rw [domWitnessAux_sum]
  have hsplit : ∀ k ∈ Finset.range n,
      (domDefect la mu (k + 1) : ℤ) * rootVec k (k + 1) i =
        (if k = i then (domDefect la mu (k + 1) : ℤ) else 0) -
          (if k + 1 = i then (domDefect la mu (k + 1) : ℤ) else 0) := by
    intro k _
    simp only [rootVec, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  -- The `e k` half picks out `k = i`, giving `D (i+1)`.
  have hA : (∑ k ∈ Finset.range n, if k = i then (domDefect la mu (k + 1) : ℤ) else 0) =
      (domDefect la mu (i + 1) : ℤ) := by
    rw [Finset.sum_ite_eq' (Finset.range n) i fun k => (domDefect la mu (k + 1) : ℤ)]
    by_cases hi : i < n
    · simp [Finset.mem_range, hi]
    · simp [Finset.mem_range, hi, domDefect_eq_zero_of_le la mu (show n ≤ i + 1 by omega)]
  -- The `e (k+1)` half picks out `k = i - 1`, giving `D i`.
  have hB : (∑ k ∈ Finset.range n, if k + 1 = i then (domDefect la mu (k + 1) : ℤ) else 0) =
      (domDefect la mu i : ℤ) := by
    rcases i with _ | j
    · simp [domDefect]
    · have hcongr : ∀ k ∈ Finset.range n,
          (if k + 1 = j + 1 then (domDefect la mu (k + 1) : ℤ) else 0) =
            (if k = j then (domDefect la mu (k + 1) : ℤ) else 0) := by
        intro k _
        by_cases hkj : k = j <;> simp [hkj]
      rw [Finset.sum_congr rfl hcongr,
        Finset.sum_ite_eq' (Finset.range n) j fun k => (domDefect la mu (k + 1) : ℤ)]
      by_cases hj : j < n
      · simp [Finset.mem_range, hj]
      · simp [Finset.mem_range, hj, domDefect_eq_zero_of_le la mu (show n ≤ j + 1 by omega)]
  rw [hA, hB]

/-- The converse of the book's implication: dominance implies the positive-root order.
Together with `Nat.Partition.RootLe.dominates` this shows the two orders coincide. -/
theorem _root_.Nat.Partition.Dominates.rootLe {n : ℕ} {la mu : Nat.Partition n}
    (h : Nat.Partition.Dominates mu la) : la.RootLe mu := by
  refine ⟨domWitnessAux la mu n, domWitnessAux_mem la mu n, fun i => ?_⟩
  rw [domWitnessAux_coeff]
  have hdiff := domDefect_succ_sub h i
  omega

/-- **Remark 5.15.5** (the two orders coincide): for partitions of `n`, `μ - λ` is a sum
of positive roots exactly when `μ` dominates `λ`. -/
theorem _root_.Nat.Partition.rootLe_iff_dominates {n : ℕ} (la mu : Nat.Partition n) :
    la.RootLe mu ↔ Nat.Partition.Dominates mu la :=
  ⟨Nat.Partition.RootLe.dominates, Nat.Partition.Dominates.rootLe⟩

/-- Antisymmetry of the positive-root order, completing the partial-order claim of
Remark 5.15.5. -/
theorem _root_.Nat.Partition.RootLe.antisymm {n : ℕ} {la mu : Nat.Partition n}
    (h₁ : la.RootLe mu) (h₂ : mu.RootLe la) : la = mu :=
  (_root_.Nat.Partition.Dominates.antisymm h₂.dominates h₁.dominates)

/-- The book's claim that `≼` "is a partial order", packaged as the corresponding
`IsPartialOrder` instance. -/
instance rootLe_isPartialOrder (n : ℕ) :
    IsPartialOrder (Nat.Partition n) Nat.Partition.RootLe where
  refl := Nat.Partition.RootLe.refl
  trans _ _ _ := Nat.Partition.RootLe.trans
  antisymm _ _ h₁ h₂ := Nat.Partition.RootLe.antisymm h₁ h₂

/-! ## Vanishing of Kostka numbers in the positive-root order -/

/-- **Remark 5.15.5** (Kostka vanishing): the Kostka number `K_{μλ}`, the multiplicity of
the Specht module `V_μ` in the permutation module `U_λ`, vanishes unless `μ ≽ λ`.

This is the root-order sharpening of `Etingof.spechtMultiplicity_vanishing_general`, and
uses `Nat.Partition.Dominates.rootLe` to convert dominance into the root order. -/
theorem spechtMultiplicity_vanishing_rootOrder (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ la.RootLe mu) : spechtMultiplicity n la mu = 0 :=
  spechtMultiplicity_vanishing_general n la mu
    (fun hd => h (Nat.Partition.Dominates.rootLe hd))

/-! ## The Kostka matrix and its inverse

The rest of the file establishes the displayed character expansion of Remark 5.15.5,

  `χ_λ = ∑_{μ ≽ λ} K̃_{μλ} χ_{U_μ}`,

where `(K̃_{λμ})` is the matrix inverse of the Kostka matrix `(K_{λμ})`.

The Kostka matrix is unitriangular for the dominance (equivalently, positive-root) order,
so `K = 1 + N` with `N` supported strictly below the diagonal. Grading the partitions of
`n` by `domRank` makes `N` nilpotent, and the resulting finite geometric series is a
two-sided inverse of `K` that is again supported on the order. -/

/-- Reflexivity of the dominance order. -/
theorem _root_.Nat.Partition.Dominates.refl {n : ℕ} (la : Nat.Partition n) :
    Nat.Partition.Dominates la la := fun _ => le_refl _

/-- Transitivity of the dominance order. -/
theorem _root_.Nat.Partition.Dominates.trans {n : ℕ} {la mu nu : Nat.Partition n}
    (h₁ : Nat.Partition.Dominates la mu) (h₂ : Nat.Partition.Dominates mu nu) :
    Nat.Partition.Dominates la nu := fun k => le_trans (h₂ k) (h₁ k)

/-! ### A grading that strictly increases along the dominance order -/

/-- Every truncation of a partition of `n` sums to at most `n`. -/
private theorem sum_take_le {n : ℕ} (la : Nat.Partition n) (k : ℕ) :
    (la.sortedParts.take k).sum ≤ n := by
  have hsplit : (la.sortedParts.take k).sum + (la.sortedParts.drop k).sum =
      la.sortedParts.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hfull : la.sortedParts.sum = n := by
    have hsort : (la.sortedParts : Multiset ℕ) = la.parts := la.parts.sort_eq (· ≥ ·)
    have : la.sortedParts.sum = la.parts.sum := by rw [← Multiset.sum_coe, hsort]
    rw [this, la.parts_sum]
  omega

/-- The total of all partial sums of `la`, used as an integer grading on the partitions
of `n`. It is monotone for the dominance order and strictly monotone on strict
dominance, which is what makes the strictly-triangular part of the Kostka matrix
nilpotent. -/
noncomputable def domRank {n : ℕ} (la : Nat.Partition n) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (la.sortedParts.take k).sum

private theorem domRank_le {n : ℕ} (la : Nat.Partition n) : domRank la ≤ (n + 1) * n := by
  calc domRank la ≤ ∑ _k ∈ Finset.range (n + 1), n :=
        Finset.sum_le_sum fun k _ => sum_take_le la k
    _ = (n + 1) * n := by simp [Finset.sum_const, mul_comm]

private theorem domRank_mono {n : ℕ} {la mu : Nat.Partition n}
    (h : Nat.Partition.Dominates mu la) : domRank la ≤ domRank mu :=
  Finset.sum_le_sum fun k _ => h k

/-- Strict monotonicity: distinct comparable partitions get distinct grades. -/
private theorem domRank_lt {n : ℕ} {la mu : Nat.Partition n}
    (h : Nat.Partition.Dominates mu la) (hne : la ≠ mu) : domRank la < domRank mu := by
  rcases lt_or_eq_of_le (domRank_mono h) with hlt | heq
  · exact hlt
  · -- Equal grades force equality of every partial sum, hence of the partitions.
    exfalso
    have hall : ∀ k ∈ Finset.range (n + 1),
        (la.sortedParts.take k).sum = (mu.sortedParts.take k).sum :=
      (Finset.sum_eq_sum_iff_of_le fun k _ => h k).mp heq
    have hconv : Nat.Partition.Dominates la mu := by
      intro k
      rcases le_or_gt k n with hk | hk
      · exact le_of_eq (hall k (Finset.mem_range.mpr (by omega))).symm
      · rw [la.sum_take_of_le (by omega), mu.sum_take_of_le (by omega)]
    exact hne (Nat.Partition.Dominates.antisymm hconv h)

/-! ### Matrices supported on the dominance order -/

section Matrices

variable {n : ℕ}

/-- `M` is supported on the dominance order: `M i j` can be nonzero only when `i`
dominates `j`. -/
private def TriSupp (M : Matrix (Nat.Partition n) (Nat.Partition n) ℂ) : Prop :=
  ∀ i j, M i j ≠ 0 → Nat.Partition.Dominates i j

private theorem TriSupp.one : TriSupp (1 : Matrix (Nat.Partition n) (Nat.Partition n) ℂ) := by
  intro i j hij
  by_cases h : i = j
  · exact h ▸ Nat.Partition.Dominates.refl i
  · simp [Matrix.one_apply_ne h] at hij

private theorem TriSupp.mul {A B : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : TriSupp A) (hB : TriSupp B) : TriSupp (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact Nat.Partition.Dominates.trans (hA i l (left_ne_zero_of_mul hl))
    (hB l j (right_ne_zero_of_mul hl))

private theorem TriSupp.neg {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : TriSupp A) : TriSupp (-A) := fun i j hij => hA i j (neg_ne_zero.mp hij)

private theorem TriSupp.pow {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : TriSupp A) (k : ℕ) : TriSupp (A ^ k) := by
  induction k with
  | zero => simpa using TriSupp.one
  | succ k ih => rw [pow_succ]; exact ih.mul hA

private theorem TriSupp.sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Nat.Partition n) (Nat.Partition n) ℂ) (hf : ∀ i ∈ s, TriSupp (f i)) :
    TriSupp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => intro i j hij; simp at hij
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    intro i j hij
    rw [Matrix.add_apply] at hij
    by_cases h : f a i j = 0
    · exact ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) i j (by simpa [h] using hij)
    · exact hf a (Finset.mem_insert_self a s) i j h

/-- `M` raises the grading by at least `d`: this is the quantitative form of "strictly
below the diagonal" that makes the nilpotency argument go through. -/
private def GradedBy (M : Matrix (Nat.Partition n) (Nat.Partition n) ℂ) (d : ℕ) : Prop :=
  ∀ i j, M i j ≠ 0 → domRank j + d ≤ domRank i

private theorem GradedBy.mul {A B : Matrix (Nat.Partition n) (Nat.Partition n) ℂ} {d e : ℕ}
    (hA : GradedBy A d) (hB : GradedBy B e) : GradedBy (A * B) (d + e) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  have h1 := hA i l (left_ne_zero_of_mul hl)
  have h2 := hB l j (right_ne_zero_of_mul hl)
  omega

private theorem GradedBy.pow {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ}
    (hA : GradedBy A 1) (k : ℕ) : GradedBy (A ^ k) k := by
  induction k with
  | zero =>
    intro i j hij
    have hij' : i = j := by
      by_contra hne
      simp [pow_zero, Matrix.one_apply_ne hne] at hij
    simp [hij']
  | succ k ih =>
    have := ih.mul hA
    rwa [← pow_succ] at this

/-- A matrix that raises the grading beyond its own range is zero. -/
private theorem GradedBy.eq_zero {A : Matrix (Nat.Partition n) (Nat.Partition n) ℂ} {d : ℕ}
    (hA : GradedBy A d) (hd : (n + 1) * n < d) : A = 0 := by
  ext i j
  by_contra hij
  have := hA i j hij
  have := domRank_le i
  omega

end Matrices

/-! ### The Kostka matrix -/

section Kostka

variable {n : ℕ}

/-- The Kostka matrix `(K_{ij})`: `K_{ij}` is the multiplicity of the Specht module `V_i`
in the permutation module `U_j`, i.e. the Kostka number of Definition 5.14.2 in the form
supplied by Young's rule. -/
noncomputable def kostkaMatrix (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) ℂ :=
  Matrix.of fun i j => (spechtMultiplicity n j i : ℂ)

theorem kostkaMatrix_apply (i j : Nat.Partition n) :
    kostkaMatrix n i j = (spechtMultiplicity n j i : ℂ) := rfl

/-- The Kostka matrix has `1` on the diagonal. -/
theorem kostkaMatrix_diagonal (i : Nat.Partition n) : kostkaMatrix n i i = 1 := by
  rw [kostkaMatrix_apply, spechtMultiplicity_diagonal]; norm_num

/-- The Kostka matrix is triangular for the positive-root order: `K_{ij} = 0` unless
`i ≽ j`. This is `spechtMultiplicity_vanishing_rootOrder` in matrix form. -/
theorem kostkaMatrix_eq_zero_of_not_rootLe {i j : Nat.Partition n} (h : ¬ j.RootLe i) :
    kostkaMatrix n i j = 0 := by
  rw [kostkaMatrix_apply, spechtMultiplicity_vanishing_rootOrder n j i h]
  norm_num

private theorem kostkaMatrix_triSupp : TriSupp (kostkaMatrix n) := by
  intro i j hij
  by_contra hd
  exact hij (kostkaMatrix_eq_zero_of_not_rootLe
    (fun hr => hd (Nat.Partition.RootLe.dominates hr)))

/-- The strictly-triangular part `N = K - 1` of the Kostka matrix. -/
private noncomputable def kostkaNil (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) ℂ :=
  kostkaMatrix n - 1

private theorem kostkaNil_triSupp : TriSupp (kostkaNil n) := by
  intro i j hij
  by_cases h : i = j
  · exact h ▸ Nat.Partition.Dominates.refl i
  · refine kostkaMatrix_triSupp i j ?_
    intro hz
    apply hij
    simp [kostkaNil, Matrix.sub_apply, hz, Matrix.one_apply_ne h]

private theorem kostkaNil_gradedBy : GradedBy (kostkaNil n) 1 := by
  intro i j hij
  by_cases h : i = j
  · exfalso
    apply hij
    simp [kostkaNil, Matrix.sub_apply, h, kostkaMatrix_diagonal, Matrix.one_apply_eq]
  · have hdom : Nat.Partition.Dominates i j := kostkaNil_triSupp i j hij
    exact domRank_lt hdom (Ne.symm h)

private theorem kostkaNil_pow_eq_zero :
    kostkaNil n ^ ((n + 1) * n + 1) = 0 :=
  (kostkaNil_gradedBy.pow _).eq_zero (by omega)

/-- The finite geometric series `∑_k (-N)^k`, which inverts `K = 1 + N`. -/
private noncomputable def kostkaGeom (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) ℂ :=
  ∑ k ∈ Finset.range ((n + 1) * n + 1), (-kostkaNil n) ^ k

private theorem neg_kostkaNil_pow_eq_zero :
    (-kostkaNil n) ^ ((n + 1) * n + 1) = 0 := by
  rw [neg_pow, kostkaNil_pow_eq_zero, mul_zero]

private theorem kostkaMatrix_eq_neg : kostkaMatrix n = -(-kostkaNil n - 1) := by
  rw [kostkaNil]; abel

private theorem kostkaGeom_mul : kostkaGeom n * kostkaMatrix n = 1 := by
  have hgeom := geom_sum_mul (-kostkaNil n) ((n + 1) * n + 1)
  rw [neg_kostkaNil_pow_eq_zero] at hgeom
  rw [kostkaGeom, kostkaMatrix_eq_neg, mul_neg, hgeom]
  simp

private theorem mul_kostkaGeom : kostkaMatrix n * kostkaGeom n = 1 := by
  have hgeom := mul_geom_sum (-kostkaNil n) ((n + 1) * n + 1)
  rw [neg_kostkaNil_pow_eq_zero] at hgeom
  rw [kostkaGeom, kostkaMatrix_eq_neg, neg_mul, hgeom]
  simp

/-- The inverse Kostka matrix `(K̃_{ij})` of Remark 5.15.5. -/
noncomputable def inverseKostkaMatrix (n : ℕ) :
    Matrix (Nat.Partition n) (Nat.Partition n) ℂ := (kostkaMatrix n)⁻¹

theorem inverseKostkaMatrix_mul : inverseKostkaMatrix n * kostkaMatrix n = 1 := by
  rw [inverseKostkaMatrix, Matrix.inv_eq_left_inv kostkaGeom_mul]
  exact kostkaGeom_mul

theorem mul_inverseKostkaMatrix : kostkaMatrix n * inverseKostkaMatrix n = 1 := by
  rw [inverseKostkaMatrix, Matrix.inv_eq_left_inv kostkaGeom_mul]
  exact mul_kostkaGeom

/-- The Kostka matrix is invertible. -/
theorem isUnit_kostkaMatrix : IsUnit (kostkaMatrix n) :=
  ⟨⟨kostkaMatrix n, inverseKostkaMatrix n, mul_inverseKostkaMatrix, inverseKostkaMatrix_mul⟩,
    rfl⟩

/-- **Remark 5.15.5** (support of the inverse Kostka matrix): `K̃_{μλ} = 0` unless
`μ ≽ λ`. Inverting a matrix triangular for the positive-root order keeps it
triangular. -/
theorem inverseKostkaMatrix_eq_zero_of_not_rootLe {mu la : Nat.Partition n}
    (h : ¬ la.RootLe mu) : inverseKostkaMatrix n mu la = 0 := by
  have hgeom : inverseKostkaMatrix n = kostkaGeom n := by
    rw [inverseKostkaMatrix, Matrix.inv_eq_left_inv kostkaGeom_mul]
  have htri : TriSupp (kostkaGeom n) :=
    TriSupp.sum _ _ fun k _ => TriSupp.pow kostkaNil_triSupp.neg k
  by_contra hne
  rw [hgeom] at hne
  exact h (Nat.Partition.Dominates.rootLe (htri mu la hne))

/-! ### The character expansion -/

/-- **Remark 5.15.5** (character expansion, unrestricted sum): the Specht-module character
`χ_λ` is the `K̃_{·λ}`-combination of the permutation-module characters `χ_{U_μ}`.

This is Young's rule (`Etingof.youngsRule_character`) read through the inverse of the
Kostka matrix. -/
theorem spechtCharacter_eq_sum_inverseKostka (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter n la σ =
      ∑ mu : Nat.Partition n,
        inverseKostkaMatrix n mu la * (permModuleCharacter n mu σ : ℂ) := by
  symm
  have hyoung : ∀ mu : Nat.Partition n, (permModuleCharacter n mu σ : ℂ) =
      ∑ nu : Nat.Partition n, kostkaMatrix n nu mu * spechtModuleCharacter n nu σ := by
    intro mu
    rw [youngsRule_character n mu σ]
    rfl
  calc ∑ mu : Nat.Partition n,
        inverseKostkaMatrix n mu la * (permModuleCharacter n mu σ : ℂ)
      = ∑ mu : Nat.Partition n, ∑ nu : Nat.Partition n,
          (kostkaMatrix n nu mu * inverseKostkaMatrix n mu la) *
            spechtModuleCharacter n nu σ := by
        refine Finset.sum_congr rfl fun mu _ => ?_
        rw [hyoung mu, Finset.mul_sum]
        exact Finset.sum_congr rfl fun nu _ => by ring
    _ = ∑ nu : Nat.Partition n,
          (kostkaMatrix n * inverseKostkaMatrix n) nu la * spechtModuleCharacter n nu σ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun nu _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
    _ = spechtModuleCharacter n la σ := by
        rw [mul_inverseKostkaMatrix]
        rw [Finset.sum_eq_single la]
        · rw [Matrix.one_apply_eq, one_mul]
        · intro b _ hb
          rw [Matrix.one_apply_ne hb, zero_mul]
        · intro h; exact absurd (Finset.mem_univ la) h

open Classical in
/-- **Remark 5.15.5** (character expansion, as displayed in the book): the sum may be
restricted to those `μ` with `μ ≽ λ`, because `K̃_{μλ}` vanishes off that range. -/
theorem spechtCharacter_eq_sum_inverseKostka_rootLe (la : Nat.Partition n)
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter n la σ =
      ∑ mu ∈ Finset.univ.filter (fun mu : Nat.Partition n => la.RootLe mu),
        inverseKostkaMatrix n mu la * (permModuleCharacter n mu σ : ℂ) := by
  rw [spechtCharacter_eq_sum_inverseKostka la σ]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro mu _ hmu
  rw [inverseKostkaMatrix_eq_zero_of_not_rootLe (by simpa using hmu), zero_mul]

end Kostka

end Etingof

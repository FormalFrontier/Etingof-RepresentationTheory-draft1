import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Remark 5.15.5: the positive-root order on partitions

For partitions `λ` and `μ` of `n`, the book writes `λ ≼ μ` when `μ - λ` is a sum of
vectors `e i - e j` with `i < j` (the *positive roots*). Remark 5.15.5 asserts that this
is a partial order, that `μ ≽ λ` implies `μ ≥ λ` in the dominance order, and that the
Kostka numbers `K_{μλ}` vanish unless `μ ≽ λ`.

This file formalizes those claims. The central result is
`Nat.Partition.rootLe_iff_dominates`: on partitions of a fixed `n` the positive-root
order and the dominance order *coincide*. The book only asserts one implication, but the
converse is what turns the existing dominance-order vanishing statement
(`Etingof.spechtMultiplicity_vanishing_general`) into the root-order vanishing statement
the remark records, so it is proved here rather than assumed.

## Main definitions

* `Nat.Partition.partAt` — the `i`-th part in non-increasing order, `0` past the end.
* `Nat.Partition.RootLe` — the positive-root order `λ ≼ μ`.

## Main results

* `Nat.Partition.RootLe.refl`, `.trans`, `.antisymm` — it is a partial order.
* `Nat.Partition.RootLe.dominates` — `μ ≽ λ` implies `μ ≥ λ` (the book's implication).
* `Nat.Partition.Dominates.rootLe` — the converse.
* `Nat.Partition.rootLe_iff_dominates` — the resulting equivalence.
* `Etingof.spechtMultiplicity_vanishing_rootOrder` — `K_{μλ} = 0` unless `μ ≽ λ`.
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

end Etingof

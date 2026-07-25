import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Lemma5_13_2

/-!
# Theorem 5.22.1, vanishing branch: `L_λ = 0 ↔ N < p`

Etingof's Theorem 5.22.1 opens with

> `L_λ = 0` if and only if `N < p`, where `p` is the number of parts of `λ`.

`Theorem5_22_1.lean` builds the Schur module from a weight `lam : Fin N → ℕ`.
That index type has already truncated the partition to at most `N` parts, so the
vanishing branch cannot even be *stated* there: `N < p` is unrepresentable.

This file removes the truncation. `partYoungSymEnd k N la` is the Young
symmetrizer of an **arbitrary** partition `la : Nat.Partition n` acting on
`(k^N)^{⊗n}`, and `SchurModuleP k N la` is its image as a `GL_N(k)`-representation.
The two constructions agree on the nose (`SchurModuleP_weightToPartition` is `rfl`),
so nothing downstream of `Theorem5_22_1.lean` changes; the partition-indexed version
is strictly more expressive.

## Main results

* `SchurModuleP_eq_bot_iff` — the headline vanishing criterion,
  `SchurModulePSubmodule k N la = ⊥ ↔ N < la.parts.card`, quantified over an
  arbitrary partition `la` with no bound relating its length to `N`.
* `SchurModuleP_ne_bot_iff` — the same statement phrased positively.
* `formalCharacter_SchurModuleP` / `finrank_SchurModuleP` — the character and
  dimension halves of Theorem 5.22.1, recovered on the nonvanishing branch
  `la.parts.card ≤ N` for the partition-indexed module.

## Proof of the vanishing branch

The Young symmetrizer factors as `c_λ = b_λ · a_λ` with `b_λ` the column
antisymmetrizer, so `range c_λ ≤ range b_λ` and it suffices to kill `b_λ`.

Fix a colouring `f : Fin n → Fin N` indexing a standard tensor basis vector.
The first column of the Young diagram of `λ` has exactly `p` cells, so when
`N < p` the pigeonhole principle produces two distinct first-column positions
`i ≠ j` with `f i = f j`. The transposition `τ = (i j)` then lies in the column
subgroup `Q_λ`, and right translation by `τ` is an involution of `Q_λ` that
negates the sign while fixing `f ∘ σ⁻¹`. Hence `b_λ · b_f = - b_λ · b_f`, which
in characteristic zero forces `b_λ · b_f = 0`.

## Proof of the nonvanishing branch

`partWeight N la` pads the sorted parts of `la` with zeros to length `N`. When
`la.parts.card ≤ N` this is an antitone weight with `weightToPartition` inverse to
it, so the module is the one `Theorem5_22_1.lean` already analysed and
`Theorem5_22_1_dim` gives `dim L_λ = weylDimension N (partWeight N la)`, a product
of strictly positive rationals.
-/

open MvPolynomial Finset CategoryTheory

noncomputable section

namespace Etingof

/-! ### The Young symmetrizer of an arbitrary partition, acting on `(k^N)^{⊗n}` -/

variable (k : Type*) [Field k]

/-- The Young symmetrizer `c_λ` of an **arbitrary** partition `la : Nat.Partition n`,
lifted to an endomorphism of `(k^N)^{⊗n}`.

Unlike `youngSymEndomorphism`, which reads its partition off a weight
`lam : Fin N → ℕ` and therefore only sees partitions with at most `N` parts, this
places no constraint at all between `la` and `N`. -/
def partYoungSymEnd (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.End k (TensorPower k (Fin N → k) n) :=
  symGroupAlgHom k (Fin N → k) n (YoungSymmetrizerK k n la)

/-- The column antisymmetrizer `b_λ = ∑_{g ∈ Q_λ} sign(g)·g`, lifted to an
endomorphism of `(k^N)^{⊗n}`. This is the left factor of `partYoungSymEnd`. -/
def colAntiEnd (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.End k (TensorPower k (Fin N → k) n) :=
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  symGroupAlgHom k (Fin N → k) n
    (∑ g : (ColumnSubgroup n la),
      ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • MonoidAlgebra.of k _ g.val)

/-- The row symmetrizer `a_λ = ∑_{g ∈ P_λ} g`, lifted to `End((k^N)^{⊗n})`. -/
def rowSymEnd (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.End k (TensorPower k (Fin N → k) n) :=
  haveI : DecidablePred (· ∈ RowSubgroup n la) := Classical.decPred _
  symGroupAlgHom k (Fin N → k) n
    (∑ g : (RowSubgroup n la), MonoidAlgebra.of k _ g.val)

/-- `c_λ = b_λ · a_λ`, transported to `End((k^N)^{⊗n})`: the Young symmetrizer
endomorphism factors through the column antisymmetrizer. -/
theorem partYoungSymEnd_eq_colAntiEnd_mul (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    partYoungSymEnd k N la = colAntiEnd k N la * rowSymEnd k N la := by
  rw [partYoungSymEnd, colAntiEnd, rowSymEnd, YoungSymmetrizerK, map_mul]

/-- The partition-indexed Young symmetrizer specialises to the weight-indexed one:
`partYoungSymEnd` at `weightToPartition N lam` *is* `youngSymEndomorphism` at `lam`. -/
theorem partYoungSymEnd_weightToPartition (N : ℕ) (lam : Fin N → ℕ) :
    partYoungSymEnd k N (weightToPartition N lam) = youngSymEndomorphism k N lam :=
  rfl

/-! ### Padding a partition to a weight vector of length `N` -/

/-- The sorted parts of `la`, padded with zeros to a weight vector of length `N`.
For `la.parts.card ≤ N` this is a faithful encoding: `weightToPartition` inverts it
(`weightToPartition_partWeight`). -/
def partWeight (N : ℕ) {n : ℕ} (la : Nat.Partition n) : Fin N → ℕ :=
  fun i => la.sortedParts.getD i.val 0

theorem partWeight_antitone (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Antitone (partWeight N la) := by
  intro i j hij
  have hsorted : la.sortedParts.Pairwise (· ≥ ·) := la.parts.pairwise_sort (· ≥ ·)
  have hij' : (i : ℕ) ≤ (j : ℕ) := hij
  simp only [partWeight]
  by_cases hj : (j : ℕ) < la.sortedParts.length
  · have hi : (i : ℕ) < la.sortedParts.length := lt_of_le_of_lt hij' hj
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    rcases eq_or_lt_of_le hij' with h | h
    · simp [h]
    · exact List.pairwise_iff_getElem.mp hsorted _ _ hi hj h
  · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
    exact Nat.zero_le _

/-- `la.sortedParts.length` is exactly the number of parts of `la`. -/
theorem sortedParts_length (n : ℕ) (la : Nat.Partition n) :
    la.sortedParts.length = Multiset.card la.parts := by
  rw [Nat.Partition.sortedParts, Multiset.length_sort]

/-- Listing `partWeight N la` reproduces the sorted parts followed by zero padding. -/
theorem ofFn_partWeight (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hcard : Multiset.card la.parts ≤ N) :
    List.ofFn (partWeight N la) =
      la.sortedParts ++ List.replicate (N - la.sortedParts.length) 0 := by
  have hlen : la.sortedParts.length ≤ N := by rw [sortedParts_length]; exact hcard
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro m h₁ h₂
    simp only [List.getElem_ofFn, partWeight]
    by_cases hm : m < la.sortedParts.length
    · rw [List.getD_eq_getElem _ _ hm, List.getElem_append_left hm]
    · rw [List.getD_eq_default _ _ (not_lt.mp hm),
        List.getElem_append_right (not_lt.mp hm), List.getElem_replicate]

theorem sum_partWeight (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hcard : Multiset.card la.parts ≤ N) :
    ∑ i, partWeight N la i = n := by
  have hsum : la.sortedParts.sum = n := by
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    have hcoe : (la.sortedParts : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
    rw [Multiset.sum_coe] at hcoe
    rw [hcoe, la.parts_sum]
  rw [← List.sum_ofFn, ofFn_partWeight N la hcard, List.sum_append, List.sum_replicate,
    smul_eq_mul, mul_zero, add_zero, hsum]

/-- Padding and un-padding are inverse: `weightToPartition N (partWeight N la) = la`
as multisets of parts, whenever `la` has at most `N` parts. -/
theorem weightToPartition_partWeight (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hcard : Multiset.card la.parts ≤ N) :
    (weightToPartition N (partWeight N la)).parts = la.parts := by
  have hpos : ∀ x ∈ la.sortedParts, 0 < x := fun x hx =>
    la.parts_pos ((Multiset.mem_sort _).mp hx)
  change Multiset.filter (0 < ·) (Multiset.map (partWeight N la) Finset.univ.val) = la.parts
  rw [Fin.univ_val_map, Multiset.filter_coe, ofFn_partWeight N la hcard, List.filter_append]
  have h₁ : List.filter (fun b => decide (0 < b)) la.sortedParts = la.sortedParts := by
    rw [List.filter_eq_self]
    exact fun x hx => decide_eq_true (hpos x hx)
  have h₂ : List.filter (fun b => decide (0 < b))
      (List.replicate (N - la.sortedParts.length) 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    simp
  rw [h₁, h₂, List.append_nil]
  exact Multiset.sort_eq la.parts (· ≥ ·)

end Etingof

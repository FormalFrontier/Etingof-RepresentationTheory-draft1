import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Lemma5_13_2

set_option backward.isDefEq.respectTransparency false

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

/-! ### The vanishing branch: too few colours to fill the first column -/

/-- A permutation reindexes the standard tensor basis: `σ · b_f = b_{f ∘ σ⁻¹}`.
(Public restatement of the `private` `symGroupAction_tensorStdBasis`.) -/
theorem symGroupAction_tensorStdBasis' (N n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin n → Fin N) :
    (symGroupAction k (Fin N → k) n σ) (tensorStdBasis k N n f) =
      tensorStdBasis k N n (f ∘ σ.symm) := by
  simp only [tensorStdBasis, _root_.Basis.piTensorProduct_apply, symGroupAction,
    PiTensorProduct.reindex_tprod, Function.comp, Pi.basisFun_apply]

/-- The column antisymmetrizer on a standard tensor basis vector is the signed sum over
the column subgroup of the reindexed basis vectors. -/
theorem colAntiEnd_apply_tensorStdBasis (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (f : Fin n → Fin N) :
    haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
    colAntiEnd k N la (tensorStdBasis k N n f) =
      ∑ g : (ColumnSubgroup n la),
        ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • tensorStdBasis k N n (f ∘ g.val.symm) := by
  haveI : DecidablePred (· ∈ ColumnSubgroup n la) := Classical.decPred _
  rw [colAntiEnd, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  congr 1
  change (symGroupAlgHom k (Fin N → k) n (MonoidAlgebra.single g.val 1))
      (tensorStdBasis k N n f) = _
  rw [symGroupAlgHom, MonoidAlgebra.lift_single, one_smul]
  exact symGroupAction_tensorStdBasis' k N n g.val f

/-- **Pigeonhole on the first column.** The first column of the Young diagram of `la`
contains one cell in each of its `p = card la.parts` rows. If a colouring
`f : Fin n → Fin N` has fewer than `p` colours available, two distinct first-column
positions must receive the same colour. -/
theorem exists_first_column_collision (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) (f : Fin n → Fin N) :
    ∃ i j : Fin n, i ≠ j ∧
      colOfPos la.sortedParts i.val = colOfPos la.sortedParts j.val ∧ f i = f j := by
  classical
  have hlsum : la.sortedParts.sum = n := by
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    have hcoe : (la.sortedParts : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
    rw [Multiset.sum_coe] at hcoe
    rw [hcoe, la.parts_sum]
  -- Every row `r` contributes a cell in column `0`.
  have hcell : ∀ r : Fin la.sortedParts.length,
      ∃ m, m < la.sortedParts.sum ∧ rowOfPos la.sortedParts m = r.val ∧
        colOfPos la.sortedParts m = 0 := by
    intro r
    refine exists_pos_of_cell la.sortedParts r.val 0 ?_
    rw [List.getD_eq_getElem _ _ r.isLt]
    exact la.parts_pos ((Multiset.mem_sort _).mp (List.getElem_mem r.isLt))
  choose F hFlt hFrow hFcol using hcell
  set G : Fin la.sortedParts.length → Fin n :=
    fun r => ⟨F r, by rw [← hlsum]; exact hFlt r⟩ with hG
  have hcard : Fintype.card (Fin N) < Fintype.card (Fin la.sortedParts.length) := by
    rw [Fintype.card_fin, Fintype.card_fin, sortedParts_length]
    exact hN
  obtain ⟨r, s, hrs, hfg⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun r => f (G r)) hcard
  refine ⟨G r, G s, fun h => hrs ?_, ?_, hfg⟩
  · have hval : F r = F s := congrArg Fin.val h
    exact Fin.ext (by rw [← hFrow r, ← hFrow s, hval])
  · change colOfPos la.sortedParts (F r) = colOfPos la.sortedParts (F s)
    rw [hFcol r, hFcol s]

variable [CharZero k]

/-- **The column antisymmetrizer annihilates `(k^N)^{⊗n}` when `N < p`.**

Fix a standard basis vector `b_f`. Pigeonhole gives two first-column cells `i ≠ j`
with `f i = f j`, so `τ = (i j)` lies in the column subgroup `Q_λ`. Right translation
by `τ` is an involution of `Q_λ` that flips the sign and fixes `f ∘ σ⁻¹`, so the signed
sum equals its own negative. -/
theorem colAntiEnd_eq_zero (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) : colAntiEnd k N la = 0 := by
  classical
  refine Module.Basis.ext (tensorStdBasis k N n) fun f => ?_
  rw [LinearMap.zero_apply, colAntiEnd_apply_tensorStdBasis]
  obtain ⟨i, j, hij, hcol, hf⟩ := exists_first_column_collision N la hN f
  set τ : Equiv.Perm (Fin n) := Equiv.swap i j with hτdef
  have hτmem : τ ∈ ColumnSubgroup n la := swap_mem_ColumnSubgroup hcol
  -- `f` is invariant under `τ`, since `τ` only swaps two equally-coloured positions.
  have hfτ : ∀ x, f (τ.symm x) = f x := by
    intro x
    rw [hτdef, Equiv.symm_swap]
    rcases eq_or_ne x i with rfl | hx
    · rw [Equiv.swap_apply_left]; exact hf.symm
    · rcases eq_or_ne x j with rfl | hx'
      · rw [Equiv.swap_apply_right]; exact hf
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  set S := ∑ g : (ColumnSubgroup n la),
    ((↑(Equiv.Perm.sign g.val) : ℤ) : k) • tensorStdBasis k N n (f ∘ g.val.symm) with hS
  -- Right translation by `τ` negates every summand.
  have hneg : S = -S := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulRight (⟨τ, hτmem⟩ : ColumnSubgroup n la))]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hcomp : f ∘ ((g * ⟨τ, hτmem⟩ : ColumnSubgroup n la) : Equiv.Perm (Fin n)).symm =
        f ∘ (g : Equiv.Perm (Fin n)).symm := by
      funext x
      exact hfτ ((g : Equiv.Perm (Fin n)).symm x)
    have hsign : Equiv.Perm.sign ((g * ⟨τ, hτmem⟩ : ColumnSubgroup n la) :
        Equiv.Perm (Fin n)) = -Equiv.Perm.sign (g : Equiv.Perm (Fin n)) := by
      change Equiv.Perm.sign ((g : Equiv.Perm (Fin n)) * τ) = _
      rw [map_mul, hτdef, Equiv.Perm.sign_swap hij]
      exact mul_neg_one _
    simp only [Equiv.coe_mulRight, hcomp, hsign, Int.cast_neg, Units.val_neg]
    exact @neg_smul k (TensorPower k (Fin N → k) n) inferInstance inferInstance
      inferInstance (((Equiv.Perm.sign (g : Equiv.Perm (Fin n)) : ℤ) : k))
      (tensorStdBasis k N n (f ∘ (g : Equiv.Perm (Fin n)).symm))
  have : (2 : k) • S = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    exact add_neg_cancel S
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  calc
    S = (2 : k)⁻¹ • ((2 : k) • S) := by
      rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    _ = 0 := by rw [this, smul_zero]

/-- **The Schur module vanishes when `N < p`.** The Young symmetrizer factors as
`c_λ = b_λ · a_λ`, and `b_λ` already acts by zero. -/
theorem partYoungSymEnd_eq_zero (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) : partYoungSymEnd k N la = 0 := by
  rw [partYoungSymEnd_eq_colAntiEnd_mul, colAntiEnd_eq_zero k N la hN, zero_mul]

-- Reopened to drop the `[CharZero k]` assumption: the representation-theoretic
-- construction below needs only a field, and reintroduces `CharZero` where it is used.
end Etingof

namespace Etingof

/-! ### The Schur module of an arbitrary partition -/

variable (k : Type*) [Field k]

/-- The `GL_N(k)`-diagonal action commutes with the Young symmetrizer of an arbitrary
partition. (Same argument as `glTensor_comm_youngSym`: the symmetrizer lies in
`symGroupImage`, which centralises `diagonalActionImage`.) -/
theorem glTensor_comm_partYoungSym (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    glTensorRep k N n g ∘ₗ partYoungSymEnd k N la =
      partYoungSymEnd k N la ∘ₗ glTensorRep k N n g := by
  set V := Fin N → k
  have h_sym : (partYoungSymEnd k N la : Module.End k (TensorPower k V n)) ∈
      (symGroupImage k V n : Set (Module.End k (TensorPower k V n))) := by
    rw [← symGroupAlgHom_range k V n]
    exact ⟨_, rfl⟩
  have h_diag : (glTensorRep k N n g : Module.End k (TensorPower k V n)) ∈
      (diagonalActionImage k V n : Set (Module.End k (TensorPower k V n))) :=
    Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩
  have hcent := diagonalActionImage_le_centralizer_symGroupImage k V n h_diag
  rw [Subalgebra.mem_centralizer_iff] at hcent
  exact (hcent _ h_sym).symm

theorem glTensorRep_mem_range_partYoungSym (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (v : TensorPower k (Fin N → k) n)
    (hv : v ∈ LinearMap.range (partYoungSymEnd k N la)) :
    (glTensorRep k N n g) v ∈ LinearMap.range (partYoungSymEnd k N la) := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨(glTensorRep k N n g) w,
    (LinearMap.ext_iff.mp (glTensor_comm_partYoungSym k N la g) w).symm⟩

/-- The Schur module of an arbitrary partition `la : Nat.Partition n`, as a submodule of
`(k^N)^{⊗n}`: the image of the Young symmetrizer `c_λ`. No relation is imposed between
the number of parts of `la` and `N`. -/
def SchurModulePSubmodule (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Submodule k (TensorPower k (Fin N → k) n) :=
  LinearMap.range (partYoungSymEnd k N la)

noncomputable local instance (priority := high) schurModulePSubmoduleAddCommGroup
    (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    AddCommGroup (SchurModulePSubmodule k N la) :=
  { Module.addCommMonoidToAddCommGroup k with
    toAddCommMonoid := (SchurModulePSubmodule k N la).addCommMonoid }

/-- The `GL_N(k)`-action on the partition-indexed Schur module. -/
def schurModulePRep (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k) (SchurModulePSubmodule k N la) where
  toFun g := (glTensorRep k N n g).restrict
    (p := SchurModulePSubmodule k N la) (q := SchurModulePSubmodule k N la)
    (fun v hv => glTensorRep_mem_range_partYoungSym k N la g v hv)
  map_one' := by
    ext ⟨v, hv⟩
    simp only [LinearMap.coe_restrict_apply]
    exact LinearMap.ext_iff.mp (map_one (glTensorRep k N _)) v
  map_mul' g₁ g₂ := by
    ext ⟨v, hv⟩
    have h_mul := LinearMap.ext_iff.mp (map_mul (glTensorRep k N n) g₁ g₂) v
    simp only [LinearMap.coe_restrict_apply, Module.End.mul_apply] at h_mul ⊢
    exact h_mul

instance schurModulePSubmodule_finite (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    Module.Finite k (SchurModulePSubmodule k N la) :=
  inferInstance

/-- **The Schur module `L_λ` of an arbitrary partition**, as a finite-dimensional
`GL_N(k)`-representation. For `la` with at most `N` parts this is the module of
`Theorem5_22_1.lean` (`SchurModuleP_weightToPartition`); for `la` with more than `N`
parts it is zero (`SchurModuleP_eq_bot_iff`). -/
@[reducible] def SchurModuleP (k : Type*) [Field k] [IsAlgClosed k]
    (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  @FDRep.of k (Matrix.GeneralLinearGroup (Fin N) k) inferInstance inferInstance
    (SchurModulePSubmodule k N la) inferInstance inferInstance inferInstance
    (schurModulePRep k N la)

/-- The partition-indexed Schur module agrees on the nose with the weight-indexed one. -/
theorem SchurModulePSubmodule_weightToPartition (N : ℕ) (lam : Fin N → ℕ) :
    SchurModulePSubmodule k N (weightToPartition N lam) = SchurModuleSubmodule k N lam :=
  rfl

theorem SchurModuleP_weightToPartition (k : Type*) [Field k] [IsAlgClosed k]
    (N : ℕ) (lam : Fin N → ℕ) :
    SchurModuleP k N (weightToPartition N lam) = SchurModule k N lam :=
  rfl

/-! ### `L_λ = 0 ↔ N < p` -/

variable [CharZero k]

/-- Half of Theorem 5.22.1's opening claim: too few colours forces `L_λ = 0`. -/
theorem SchurModulePSubmodule_eq_bot_of_lt (N : ℕ) {n : ℕ} (la : Nat.Partition n)
    (hN : N < Multiset.card la.parts) : SchurModulePSubmodule k N la = ⊥ := by
  rw [SchurModulePSubmodule, partYoungSymEnd_eq_zero k N la hN, LinearMap.range_zero]

/-- Every factor of the Weyl dimension product is positive for an antitone weight. -/
theorem weylDimension_pos (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    0 < weylDimension N lam := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  have h1 : (lam j : ℚ) ≤ (lam i : ℚ) := by exact_mod_cast hlam (le_of_lt hij)
  have h2 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (Fin.lt_def.mp hij)
  exact div_pos (by linarith) (by linarith)

/-- The other half: a partition with at most `N` parts has a nonzero Schur module.
The module is the one `Theorem5_22_1.lean` analysed, and its dimension is the Weyl
dimension product, a product of strictly positive rationals. -/
theorem SchurModulePSubmodule_ne_bot_of_le [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (hcard : Multiset.card la.parts ≤ N) :
    SchurModulePSubmodule k N la ≠ ⊥ := by
  obtain ⟨lam, hanti, hsum, hparts⟩ : ∃ lam : Fin N → ℕ, Antitone lam ∧
      (∑ i, lam i) = n ∧ (weightToPartition N lam).parts = la.parts :=
    ⟨partWeight N la, partWeight_antitone N la, sum_partWeight N la hcard,
      weightToPartition_partWeight N la hcard⟩
  clear hcard
  subst hsum
  have hla : weightToPartition N lam = la := Nat.Partition.ext hparts
  subst hla
  rw [SchurModulePSubmodule_weightToPartition]
  intro hbot
  have hdim : (Module.finrank k (SchurModule k N lam) : ℚ) = weylDimension N lam :=
    Theorem5_22_1_dim k N lam hanti
  have hzero : Module.finrank k (SchurModuleSubmodule k N lam) = 0 :=
    Submodule.finrank_eq_zero.mpr hbot
  rw [show Module.finrank k (SchurModule k N lam) =
      Module.finrank k (SchurModuleSubmodule k N lam) from rfl, hzero] at hdim
  exact absurd hdim.symm (ne_of_gt (weylDimension_pos N lam hanti))

/-- **Theorem 5.22.1, opening claim.** `L_λ = 0` exactly when `N` is smaller than the
number of parts `p` of `λ`. The statement quantifies over an arbitrary partition, with
no bound tying its length to `N`. -/
theorem SchurModuleP_eq_bot_iff [IsAlgClosed k] (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    SchurModulePSubmodule k N la = ⊥ ↔ N < Multiset.card la.parts := by
  refine ⟨fun hbot => ?_, SchurModulePSubmodule_eq_bot_of_lt k N la⟩
  by_contra hle
  exact SchurModulePSubmodule_ne_bot_of_le k N la (not_lt.mp hle) hbot

/-- Positive form of `SchurModuleP_eq_bot_iff`. -/
theorem SchurModuleP_ne_bot_iff [IsAlgClosed k] (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    SchurModulePSubmodule k N la ≠ ⊥ ↔ Multiset.card la.parts ≤ N := by
  rw [ne_eq, SchurModuleP_eq_bot_iff, not_lt]

/-- `dim L_λ = 0 ↔ N < p`: the vanishing criterion read off the dimension. -/
theorem finrank_SchurModuleP_eq_zero_iff [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) :
    Module.finrank k (SchurModuleP k N la) = 0 ↔ N < Multiset.card la.parts := by
  rw [show Module.finrank k (SchurModuleP k N la) =
      Module.finrank k (SchurModulePSubmodule k N la) from rfl,
    Submodule.finrank_eq_zero, SchurModuleP_eq_bot_iff]

/-! ### The character and dimension formulas on the nonvanishing branch -/

/-- **Weyl character formula for the partition-indexed Schur module.** On the
nonvanishing branch, presented by any antitone weight `lam` of `la`, the formal
character of `L_λ` is the Schur polynomial `S_λ(x₁, …, x_N)`. -/
theorem formalCharacter_SchurModuleP_of_weight [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (lam : Fin N → ℕ) (hanti : Antitone lam)
    (hsum : (∑ i, lam i) = n) (hparts : (weightToPartition N lam).parts = la.parts) :
    formalCharacter k N (SchurModuleP k N la) = schurPoly N lam := by
  subst hsum
  have hla : weightToPartition N lam = la := Nat.Partition.ext hparts
  subst hla
  rw [SchurModuleP_weightToPartition]
  exact Theorem5_22_1 k N lam hanti

/-- **Weyl dimension formula for the partition-indexed Schur module.** -/
theorem finrank_SchurModuleP_of_weight [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (lam : Fin N → ℕ) (hanti : Antitone lam)
    (hsum : (∑ i, lam i) = n) (hparts : (weightToPartition N lam).parts = la.parts) :
    (Module.finrank k (SchurModuleP k N la) : ℚ) = weylDimension N lam := by
  subst hsum
  have hla : weightToPartition N lam = la := Nat.Partition.ext hparts
  subst hla
  change (Module.finrank k
    (SchurModulePSubmodule k N (weightToPartition N lam)) : ℚ) = _
  rw [SchurModulePSubmodule_weightToPartition]
  exact Theorem5_22_1_dim k N lam hanti

/-- Character formula in terms of the canonical zero-padded weight of `la`. -/
theorem formalCharacter_SchurModuleP [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (hcard : Multiset.card la.parts ≤ N) :
    formalCharacter k N (SchurModuleP k N la) = schurPoly N (partWeight N la) :=
  formalCharacter_SchurModuleP_of_weight k N la (partWeight N la) (partWeight_antitone N la)
    (sum_partWeight N la hcard) (weightToPartition_partWeight N la hcard)

/-- Dimension formula in terms of the canonical zero-padded weight of `la`. -/
theorem finrank_SchurModuleP [IsAlgClosed k] (N : ℕ) {n : ℕ}
    (la : Nat.Partition n) (hcard : Multiset.card la.parts ≤ N) :
    (Module.finrank k (SchurModuleP k N la) : ℚ) = weylDimension N (partWeight N la) :=
  finrank_SchurModuleP_of_weight k N la (partWeight N la) (partWeight_antitone N la)
    (sum_partWeight N la hcard) (weightToPartition_partWeight N la hcard)

/-- **Etingof Theorem 5.22.1, assembled.** For an arbitrary partition `λ` of `n`:
`L_λ = 0` iff `N < p`, and otherwise the character is `S_λ` and the dimension is the
Weyl product `∏_{i<j} (λ_i − λ_j + j − i)/(j − i)`. -/
theorem Theorem5_22_1_full [IsAlgClosed k] (N : ℕ) {n : ℕ} (la : Nat.Partition n) :
    (SchurModulePSubmodule k N la = ⊥ ↔ N < Multiset.card la.parts) ∧
      (Multiset.card la.parts ≤ N →
        formalCharacter k N (SchurModuleP k N la) = schurPoly N (partWeight N la) ∧
          (Module.finrank k (SchurModuleP k N la) : ℚ) =
            weylDimension N (partWeight N la)) :=
  ⟨SchurModuleP_eq_bot_iff k N la,
    fun hcard => ⟨formalCharacter_SchurModuleP k N la hcard,
      finrank_SchurModuleP k N la hcard⟩⟩

/-! ### Non-vacuity: both branches are inhabited

`SchurModuleP_eq_bot_iff` would be worthless if one side never held. The partition
`(1,1)` of `2` has two parts, so `Λ²` of a line vanishes while `Λ²` of a plane does not:
the same partition lands on opposite sides of the criterion for `N = 1` and `N = 2`. -/

/-- The partition `(1,1)` of `2`, the smallest witness with more than one part. -/
def onePlusOne : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by decide
  parts_sum := by decide

theorem card_onePlusOne_parts : Multiset.card onePlusOne.parts = 2 := by decide

/-- `Λ²` of a line is zero: one colour cannot fill a two-cell column. -/
theorem SchurModuleP_onePlusOne_dim_one : SchurModulePSubmodule ℂ 1 onePlusOne = ⊥ := by
  rw [SchurModuleP_eq_bot_iff]
  decide

/-- `Λ²` of a plane is not zero. -/
theorem SchurModuleP_onePlusOne_dim_two : SchurModulePSubmodule ℂ 2 onePlusOne ≠ ⊥ := by
  rw [SchurModuleP_ne_bot_iff]
  decide

end Etingof

import Mathlib
import EtingofRepresentationTheory.Chapter5.SchurWeylPolynomialIdentity
import EtingofRepresentationTheory.Chapter5.Theorem5_17_1

/-!
# Frobenius route to `dim V_λ = #SYT` (Etingof Theorem 5.17.1) — bypasses Wall 3

PROTOTYPE / SKELETON for issue #4595. Etingof's book proves the Specht dimension
via the **Frobenius character formula** (Theorem 5.15.1), NOT via the Garnir
straightening (`SpechtModuleBasis.lean`, the open Wall 3 sorries). This file
scaffolds the book-faithful route, isolating the single genuinely-hard step
(the Vandermonde/determinant computation of `Discussion_hook_length_derivation`)
as `charValue_trivialCycleType_eq_hookFormula`. Everything else chains lemmas
that are already proven and sorry-free:

* `charValue_trivialCycleType_eq_spechtFinrank_rat` : `dim V_λ = charValue(λ, 1)`  (DONE)
* `card_standardYoungTableau_eq` : `#SYT = n!/∏hooks`  (FRT, DONE)

With the one hard lemma, `dim V_λ = charValue(λ,1) = n!/∏hooks = #SYT`, and the
entire Garnir straightening (`garnir_twisted_in_lower_span` #2703,
`twistedPolytabloid_pigeonhole_pair` #2543, the per-q / involution apparatus)
drops off the critical path.
-/

namespace Etingof
noncomputable section
open scoped BigOperators

/-! ## Young-diagram bookkeeping for the hook-length cancellation (#4616)

Pure combinatorics relating the hook lengths of
`(weightToPartition N lam.parts).toYoungDiagram` directly to `lam.parts : Fin N → ℕ`.
No representation theory. These feed the Frame–Robinson–Thrall cancellation
`hookLengthProduct_mul_vandermonde_eq_prod_factorial` (Part B, #4617). -/

/-- The `i`-th row length of a partition's Young diagram equals the `i`-th
sorted part (with `0` past the end). General, reusable. -/
theorem Nat.Partition.toYoungDiagram_rowLen_eq_getD {m : ℕ} (μ : Nat.Partition m) (i : ℕ) :
    μ.toYoungDiagram.rowLen i = μ.sortedParts.getD i 0 := by
  have key : ∀ j : ℕ, j < μ.toYoungDiagram.rowLen i ↔ j < μ.sortedParts.getD i 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i, j) ∈ YoungDiagram.ofRowLens μ.sortedParts _ ↔ _
    rw [YoungDiagram.mem_ofRowLens]
    by_cases hlen : i < μ.sortedParts.length
    · rw [List.getD_eq_getElem _ _ hlen]
      constructor
      · rintro ⟨_, hj⟩; exact hj
      · intro hj; exact ⟨hlen, hj⟩
    · rw [List.getD_eq_default _ _ (not_lt.mp hlen)]
      constructor
      · rintro ⟨h, -⟩; exact absurd h hlen
      · intro hj; exact absurd hj (Nat.not_lt_zero j)
  have h1 := key (μ.toYoungDiagram.rowLen i)
  have h2 := key (μ.sortedParts.getD i 0)
  omega

/-- The sorted-parts list of `weightToPartition N f` has length at most `N`. -/
theorem weightToPartition_sortedParts_length_le (N : ℕ) (f : Fin N → ℕ) :
    (weightToPartition N f).sortedParts.length ≤ N := by
  unfold Nat.Partition.sortedParts weightToPartition
  rw [Multiset.length_sort]
  calc Multiset.card (Multiset.filter (0 < ·) (Finset.univ.val.map f))
      ≤ Multiset.card (Finset.univ.val.map f) := Multiset.card_le_card (Multiset.filter_le _ _)
    _ = N := by
        rw [Multiset.card_map]
        have : Multiset.card (Finset.univ.val : Multiset (Fin N)) = Finset.univ.card := rfl
        rw [this, Finset.card_univ, Fintype.card_fin]

/-- Rows past index `N` of `weightToPartition N f` are empty. -/
theorem weightToPartition_rowLen_eq_zero (N : ℕ) (f : Fin N → ℕ) {x : ℕ} (hx : N ≤ x) :
    (weightToPartition N f).toYoungDiagram.rowLen x = 0 := by
  rw [Nat.Partition.toYoungDiagram_rowLen_eq_getD]
  exact List.getD_eq_default _ _ (le_trans (weightToPartition_sortedParts_length_le N f) hx)

/-- For an antitone weight, the `i`-th sorted part of `weightToPartition` is `f i`.
Local copy of the `private` `sortedParts_getD_eq_of_antitone` (`Theorem5_22_1.lean`). -/
private theorem weightToPartition_sortedParts_getD (N : ℕ) (f : Fin N → ℕ) (hf : Antitone f)
    (i : Fin N) :
    (weightToPartition N f).sortedParts.getD i.val 0 = f i := by
  unfold Nat.Partition.sortedParts weightToPartition
  simp only [Fin.univ_val_map]
  have h_sorted : ((List.ofFn f).filter (0 < ·)).SortedGE := by
    rw [List.sortedGE_iff_pairwise]
    exact List.Pairwise.filter _ (List.sortedGE_ofFn_iff.mpr hf).pairwise
  have h_sort_eq : ((↑(List.ofFn f) : Multiset ℕ).filter (0 < ·)).sort (· ≥ ·) =
      (List.ofFn f).filter (0 < ·) := by
    rw [Multiset.filter_coe]
    have h_perm : ((↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)).Perm
        ((List.ofFn f).filter (0 < ·)) :=
      Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
    have h_sort_sorted : (↑((List.ofFn f).filter (0 < ·)) : Multiset ℕ).sort (· ≥ ·)
        |>.SortedGE := by
      rw [List.sortedGE_iff_pairwise]
      exact Multiset.pairwise_sort _ _
    exact h_perm.eq_of_sortedGE h_sort_sorted h_sorted
  rw [h_sort_eq]
  suffices h_filter_eq : ∀ (m : ℕ) (g : Fin m → ℕ), Antitone g →
      ∀ j : Fin m, ((List.ofFn g).filter (0 < ·)).getD j.val 0 = g j by
    exact h_filter_eq N f hf i
  intro m g hg j
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    rw [List.ofFn_succ]
    by_cases hg0 : 0 < g 0
    · simp only [List.filter_cons, decide_eq_true_eq.mpr hg0, ↓reduceIte]
      cases j using Fin.cases with
      | zero => simp [List.getD]
      | succ j' =>
        simp only [List.getD]
        have hgs : Antitone (g ∘ Fin.succ) :=
          fun a b hab => hg (show Fin.succ a ≤ Fin.succ b from Fin.succ_le_succ_iff.mpr hab)
        exact ih (g ∘ Fin.succ) hgs j'
    · push_neg at hg0
      have hg0' : g 0 = 0 := Nat.le_zero.mp hg0
      simp only [List.filter_cons, show decide (0 < g 0) = false from
        decide_eq_false (not_lt.mpr hg0), Bool.false_eq_true, ↓reduceIte]
      have hall : ∀ k : Fin (m + 1), g k = 0 :=
        fun k => Nat.le_zero.mp (hg0' ▸ hg (Fin.zero_le k))
      have h_empty : List.filter (fun x => decide (0 < x))
          (List.ofFn (fun i : Fin m => g i.succ)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨k, rfl⟩ := hx
        simp [hall k.succ]
      rw [h_empty]; simp [hall j]

/-- **Deliverable (2):** the `i`-th row length of the weight's Young diagram is `lam.parts i`. -/
theorem weightToPartition_rowLen (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) (i : Fin N) :
    (weightToPartition N lam.parts).toYoungDiagram.rowLen i = lam.parts i := by
  rw [Nat.Partition.toYoungDiagram_rowLen_eq_getD]
  exact weightToPartition_sortedParts_getD N lam.parts lam.decreasing i

/-- **Deliverable (3):** the `c`-th column length is the number of rows whose
part exceeds `c`. -/
theorem weightToPartition_colLen (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) (c : ℕ) :
    (weightToPartition N lam.parts).toYoungDiagram.colLen c =
      (Finset.univ.filter (fun i : Fin N => c < lam.parts i)).card := by
  rw [← Finset.card_range ((weightToPartition N lam.parts).toYoungDiagram.colLen c),
      ← Finset.card_image_of_injective
        (Finset.univ.filter (fun i : Fin N => c < lam.parts i)) Fin.val_injective]
  congr 1
  ext x
  simp only [Finset.mem_range, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have hmem : ((x, c) : ℕ × ℕ) ∈ (weightToPartition N lam.parts).toYoungDiagram :=
      YoungDiagram.mem_iff_lt_colLen.mpr hx
    have hxN : x < N := by
      by_contra h
      push_neg at h
      rw [YoungDiagram.mem_iff_lt_rowLen, weightToPartition_rowLen_eq_zero N lam.parts h] at hmem
      exact absurd hmem (Nat.not_lt_zero c)
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    rw [YoungDiagram.mem_iff_lt_rowLen, weightToPartition_rowLen N lam ⟨x, hxN⟩] at hmem
    exact hmem
  · rintro ⟨i, hi, rfl⟩
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen,
        weightToPartition_rowLen N lam i]
    exact hi

/-- **Deliverable (4):** the hook length at `(i, c)` splits into the arm
(`lam.parts i - c`) plus the leg (rows below `i` whose part exceeds `c`). -/
theorem hookLength_eq_arm_add_leg (N : ℕ) {n : ℕ} (lam : BoundedPartition N n)
    (i : Fin N) {c : ℕ} (hc : c < lam.parts i) :
    (weightToPartition N lam.parts).toYoungDiagram.hookLength i c =
      lam.parts i - c +
        (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)).card := by
  have hAcard : (Finset.univ.filter (fun r : Fin N => r ≤ i)).card = i.val + 1 := by
    rw [← Finset.card_range (i.val + 1),
        ← Finset.card_image_of_injective _ Fin.val_injective]
    congr 1
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_range, Fin.le_iff_val_le_val]
    constructor
    · rintro ⟨r, hr, rfl⟩; omega
    · intro hx
      have hxi : x ≤ i.val := by omega
      have hxN : x < N := lt_of_le_of_lt hxi i.isLt
      exact ⟨⟨x, hxN⟩, hxi, rfl⟩
  have hdisj : Disjoint (Finset.univ.filter (fun r : Fin N => r ≤ i))
      (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)) := by
    rw [Finset.disjoint_left]
    intro r hrA hrB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrA hrB
    exact absurd hrB.1 (not_lt.mpr hrA)
  have hcol : (weightToPartition N lam.parts).toYoungDiagram.colLen c =
      (i.val + 1) + (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)).card := by
    rw [weightToPartition_colLen N lam c]
    have hunion : (Finset.univ.filter (fun r : Fin N => c < lam.parts r)) =
        (Finset.univ.filter (fun r : Fin N => r ≤ i)) ∪
        (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hr
        by_cases h : r ≤ i
        · exact Or.inl h
        · exact Or.inr ⟨not_le.mp h, hr⟩
      · rintro (h | ⟨_, h⟩)
        · exact lt_of_lt_of_le hc (lam.decreasing h)
        · exact h
    rw [hunion, Finset.card_union_of_disjoint hdisj, hAcard]
  rw [YoungDiagram.hookLength, weightToPartition_rowLen N lam i, hcol]
  omega

/-- **Deliverable (5):** the hook-length product reorganized as a product over rows. -/
theorem hookLengthProduct_eq_prod_rows (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    (weightToPartition N lam.parts).toYoungDiagram.hookLengthProduct =
      ∏ i : Fin N, ∏ c ∈ Finset.range (lam.parts i),
        (weightToPartition N lam.parts).toYoungDiagram.hookLength i c := by
  have hcell : ∀ p : ℕ × ℕ,
      p ∈ (weightToPartition N lam.parts).toYoungDiagram.cells → p.1 < N := by
    intro p hp
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hp
    by_contra h
    push_neg at h
    rw [weightToPartition_rowLen_eq_zero N lam.parts h] at hp
    exact absurd hp (Nat.not_lt_zero p.2)
  unfold YoungDiagram.hookLengthProduct
  rw [Finset.prod_sigma']
  refine Finset.prod_bij'
    (fun (c : ℕ × ℕ) (hc : c ∈ (weightToPartition N lam.parts).toYoungDiagram.cells) =>
      (⟨⟨c.1, hcell c hc⟩, c.2⟩ : (_ : Fin N) × ℕ))
    (fun (p : (_ : Fin N) × ℕ) _ => (p.1.val, p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    have hlt := hcell c hc
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_range, ← weightToPartition_rowLen N lam ⟨c.1, hlt⟩]
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc
    exact hc
  · intro p hp
    rw [Finset.mem_sigma, Finset.mem_range] at hp
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, weightToPartition_rowLen N lam p.1]
    exact hp.2
  · intro c hc; rfl
  · intro p hp; rfl
  · intro c hc; rfl

/-- **Part A, step 7 (algebraic / Vandermonde half, #4670).**

The falling-factorial alternant determinant with the *reflected* column exponents
`vandermondeExps N j = N-1-j` equals the genuine descending product
`∏_{i<j}(βᵢ − βⱼ)` of a strictly antitone node sequence `β`.

Proof: `descPochhammer ℤ k` is monic of degree `k`, so
`Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` identifies the *ascending*
falling-factorial matrix (columns `j ↦ (descPochhammer ℤ j).eval ·`) with a true
Vandermonde determinant. The reflected matrix is obtained from the ascending one of
the *reversed* node sequence `γ := β ∘ Fin.rev` by the `rev`-on-both-indices
submatrix, whose determinant is unchanged (`det_submatrix_equiv_self`) — so no
column-reflection sign survives. `Matrix.det_vandermonde` then gives
`∏_{i<j}(γⱼ − γᵢ)`, and the pair-involution `(i,j) ↦ (rev j, rev i)` rewrites this
as `∏_{i<j}(βᵢ − βⱼ)` (each difference a genuine positive `ℕ` subtraction since
`β` is strictly decreasing). -/
private theorem descPochhammer_alternant_det_eq_prod_sub
    (N : ℕ) (β : Fin N → ℕ) (hβ : StrictAnti β) :
    (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (vandermondeExps N j)).eval (β i : ℤ)).det =
      ((∏ i, ∏ j ∈ Finset.Ioi i, (β i - β j) : ℕ) : ℤ) := by
  classical
  set γ : Fin N → ℤ := fun i => (β (Fin.rev i) : ℤ) with hγ
  -- The Vandermonde determinant of the reversed nodes `γ` equals the determinant of
  -- the *ascending* falling-factorial matrix of `γ` (monic degree-`k` polynomials).
  have hBγ : (Matrix.vandermonde γ).det
      = (Matrix.of fun i j : Fin N => (descPochhammer ℤ (j : ℕ)).eval (γ i)).det :=
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde γ
      (fun i : Fin N => descPochhammer ℤ (i : ℕ))
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)
  -- The `rev`-on-both-indices submatrix of our reflected matrix is exactly that
  -- ascending falling-factorial matrix of `γ`.
  have hsub : (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (vandermondeExps N j)).eval (β i : ℤ)).submatrix
          Fin.revPerm Fin.revPerm
      = (Matrix.of fun i j : Fin N => (descPochhammer ℤ (j : ℕ)).eval (γ i)) := by
    ext i j
    have hvj : vandermondeExps N (Fin.rev j) = (j : ℕ) := by
      have hj := j.isLt
      simp only [vandermondeExps, Fin.val_rev]
      omega
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, hγ, hvj]
  -- Chain: det(reflected) = det(submatrix) = det(vandermonde γ) = ∏ (γ j − γ i).
  have hdet : (Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (vandermondeExps N j)).eval (β i : ℤ)).det
      = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (γ j - γ i) := by
    rw [← Matrix.det_submatrix_equiv_self Fin.revPerm
          (Matrix.of fun i j : Fin N =>
            (descPochhammer ℤ (vandermondeExps N j)).eval (β i : ℤ)),
        hsub, ← hBγ, Matrix.det_vandermonde]
  rw [hdet]
  -- Cast the `ℕ` target into a product of genuine `ℤ` differences.
  have hcast : ((∏ i, ∏ j ∈ Finset.Ioi i, (β i - β j) : ℕ) : ℤ)
      = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((β i : ℤ) - (β j : ℤ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    exact Nat.cast_sub (hβ (Finset.mem_Ioi.mp hj)).le
  rw [hcast, Finset.prod_sigma', Finset.prod_sigma']
  -- The pair involution `(i,j) ↦ (rev j, rev i)` matches `γ j − γ i` with `βᵢ − βⱼ`.
  apply Finset.prod_nbij'
    (fun x : Σ _ : Fin N, Fin N => (⟨Fin.rev x.2, Fin.rev x.1⟩ : Σ _ : Fin N, Fin N))
    (fun x : Σ _ : Fin N, Fin N => (⟨Fin.rev x.2, Fin.rev x.1⟩ : Σ _ : Fin N, Fin N))
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx ⊢
    exact Fin.rev_lt_rev.mpr hx
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx ⊢
    exact Fin.rev_lt_rev.mpr hx
  · intro x _; simp only [Fin.rev_rev]
  · intro x _; simp only [Fin.rev_rev]
  · intro x _; simp only [hγ]

/-- **Part A — Frobenius → Vandermonde determinant**
(book `Discussion_hook_length_derivation`, lines 1–18).

The Frobenius character value at the identity equals `n!` times the Vandermonde
product of the beta-numbers `l_j = λ_j + (N-1-j)` (here `shiftedExps N lam.parts`),
divided by `∏_j l_j!`.

`charValue N λ 1` is the coefficient of `x^{λ+ρ}` in `Δ(x)·(∑ᵢ Xᵢ)^n`
(`psumPart_trivialCycleType`). Expanding `Δ` as a signed monomial sum
(`vandermondePoly_eq_sum_sign_monomial`) and extracting the coefficient
(`coeff_vandermonde_mul`, multinomial coefficients of `(∑X)^n`) yields the
determinant `det(l_j^{N-i})`, which by `Matrix.det_vandermonde` equals
`∏_{i<j}(l_i − l_j)`. This is self-contained `MvPolynomial`/`Matrix.det`
algebra — no representation theory, no straightening.

For `i < j` the beta-numbers are strictly decreasing (`shiftedExps` is strictly
antitone, see `charValue_trivialCycleType_eq_hookFormula` below), so the ℕ
subtraction `l_i − l_j` is the genuine positive difference. -/
theorem charValue_trivialCycleType_eq_frobeniusDetForm
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    charValue N lam (trivialCycleType n) =
      (n.factorial : ℚ) *
        ((∏ i, ∏ j ∈ Finset.Ioi i,
            (shiftedExps N lam.parts i - shiftedExps N lam.parts j) : ℕ) : ℚ) /
        ((∏ j, (shiftedExps N lam.parts j).factorial : ℕ) : ℚ) := by
  sorry

/-- The descending product `∏_{x < k} (k - x)` equals `k!`. -/
private theorem prod_range_sub_eq_factorial (k : ℕ) :
    ∏ x ∈ Finset.range k, (k - x) = k.factorial := by
  rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect (fun x => x + 1) k]
  refine Finset.prod_congr rfl (fun x hx => ?_)
  rw [Finset.mem_range] at hx
  omega

/-- The hook-length product is invariant under transporting the partition along
an equality of its size index (the Young diagram, hence its hooks, does not
depend on the size). -/
private theorem hookLengthProduct_cast {a b : ℕ} (h : a = b) (p : Nat.Partition a) :
    (h ▸ p).toYoungDiagram.hookLengthProduct = p.toYoungDiagram.hookLengthProduct := by
  subst h; rfl

/-- **Per-row Frame–Robinson–Thrall identity (the combinatorial heart of Part B).**

For each row `i`, the row's hook lengths together with the first-column gaps
`βᵢ − βₖ` (`k > i`, `β = shiftedExps`) form exactly `{1, …, βᵢ}`:

  `(∏_{c < λᵢ} h(i,c)) · (∏_{k > i} (βᵢ − βₖ)) = βᵢ!`.

Proof: both index sets inject into `range βᵢ` (the gaps as `k ↦ βₖ`, the hooks as
`c ↦ βᵢ − h(i,c) = c + #{r > i : λᵣ ≤ c} =: g c`); they are disjoint and have
total size `λᵢ + (N−1−i) = βᵢ`, so they partition `range βᵢ`. Then
`∏_{x < βᵢ}(βᵢ − x) = βᵢ!`. Disjointness reduces to two monotone leg-count
bounds: for `k > i`, `g c > βₖ` when `λₖ ≤ c` and `g c < βₖ` when `c < λₖ`. -/
private theorem row_hook_gap_prod_eq_factorial (N : ℕ) {n : ℕ} (lam : BoundedPartition N n)
    (i : Fin N) :
    (∏ c ∈ Finset.range (lam.parts i),
        (weightToPartition N lam.parts).toYoungDiagram.hookLength i c) *
      (∏ k ∈ Finset.Ioi i,
        (shiftedExps N lam.parts i - shiftedExps N lam.parts k)) =
      (shiftedExps N lam.parts i).factorial := by
  classical
  set β := shiftedExps N lam.parts with hβdef
  have hβanti : StrictAnti β := by rw [hβdef]; exact shiftedExps_strictAnti lam
  have hβinj : Function.Injective β := hβanti.injective
  have hβi : β i = lam.parts i + (N - 1 - (i : ℕ)) := by rw [hβdef]; simp only [shiftedExps]
  set g : ℕ → ℕ :=
    fun c => c + ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card with hgdef
  have hg_sm : StrictMono g := by
    intro a b hab
    have hcard : ((Finset.Ioi i).filter (fun r => lam.parts r ≤ a)).card ≤
        ((Finset.Ioi i).filter (fun r => lam.parts r ≤ b)).card := by
      apply Finset.card_le_card
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, le_trans hr.2 hab.le⟩
    simp only [hgdef]
    omega
  have hg_inj : Function.Injective g := hg_sm.injective
  set SA := (Finset.Ioi i).image β with hSA
  set SB := (Finset.range (lam.parts i)).image g with hSB
  have hSA_sub : SA ⊆ Finset.range (β i) := by
    intro v hv
    rw [hSA, Finset.mem_image] at hv
    obtain ⟨k, hk, rfl⟩ := hv
    rw [Finset.mem_range]
    exact hβanti (Finset.mem_Ioi.mp hk)
  have hSB_sub : SB ⊆ Finset.range (β i) := by
    intro v hv
    rw [hSB, Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    rw [Finset.mem_range] at hc ⊢
    have hBle : ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card ≤ (Finset.Ioi i).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hIoii : (Finset.Ioi i).card = N - 1 - (i : ℕ) := Fin.card_Ioi i
    rw [hIoii] at hBle
    simp only [hgdef]
    rw [hβi]
    omega
  have hdisj : Disjoint SA SB := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    rw [hSA, Finset.mem_image] at hvA
    rw [hSB, Finset.mem_image] at hvB
    obtain ⟨k, hk, hkv⟩ := hvA
    obtain ⟨c, _, hcv⟩ := hvB
    rw [Finset.mem_Ioi] at hk
    have heq : β k = g c := by rw [hkv, hcv]
    have hβk : β k = lam.parts k + (N - 1 - (k : ℕ)) := by rw [hβdef]; simp only [shiftedExps]
    have hkN : (k : ℕ) < N := k.isLt
    rcases Nat.lt_or_ge c (lam.parts k) with hkc | hkc
    · -- `c < λₖ`: the leg count is at most `N − 1 − k`, so `g c < βₖ`.
      have hle : ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card ≤ N - 1 - (k : ℕ) := by
        have hIoik : (Finset.Ioi k).card = N - 1 - (k : ℕ) := Fin.card_Ioi k
        rw [← hIoik]
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_filter, Finset.mem_Ioi] at hs
        obtain ⟨_, hs2⟩ := hs
        rw [Finset.mem_Ioi]
        by_contra hcon
        push_neg at hcon
        have hmono := lam.decreasing hcon
        omega
      simp only [hgdef] at heq
      omega
    · -- `λₖ ≤ c`: the leg count is at least `N − k`, so `g c > βₖ`.
      have hge : (N : ℕ) - (k : ℕ) ≤
          ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card := by
        have hIci : (Finset.Ici k).card = N - (k : ℕ) := Fin.card_Ici k
        rw [← hIci]
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_Ici] at hs
        rw [Finset.mem_filter, Finset.mem_Ioi]
        exact ⟨lt_of_lt_of_le hk hs, le_trans (lam.decreasing hs) hkc⟩
      simp only [hgdef] at heq
      omega
  have hcardSA : SA.card = N - 1 - (i : ℕ) := by
    rw [hSA, Finset.card_image_of_injective _ hβinj]
    exact Fin.card_Ioi i
  have hcardSB : SB.card = lam.parts i := by
    rw [hSB, Finset.card_image_of_injective _ hg_inj, Finset.card_range]
  have hunion : SA ∪ SB = Finset.range (β i) := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hSA_sub hSB_sub)
    rw [Finset.card_range, Finset.card_union_of_disjoint hdisj, hcardSA, hcardSB, hβi]
    omega
  have hkey : ∀ c, c < lam.parts i →
      β i - g c = (weightToPartition N lam.parts).toYoungDiagram.hookLength i c := by
    intro c hc
    have hcompl : ((Finset.Ioi i).filter (fun r => c < lam.parts r)).card +
        ((Finset.Ioi i).filter (fun r => lam.parts r ≤ c)).card = N - 1 - (i : ℕ) := by
      have hIoii : (Finset.Ioi i).card = N - 1 - (i : ℕ) := Fin.card_Ioi i
      rw [← hIoii, ← Finset.card_filter_add_card_filter_not (s := Finset.Ioi i)
            (p := fun r => c < lam.parts r)]
      congr 1
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro r _
      simp only [not_lt]
    have hA : (Finset.univ.filter (fun r : Fin N => i < r ∧ c < lam.parts r)).card =
        ((Finset.Ioi i).filter (fun r => c < lam.parts r)).card := by
      congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    rw [hookLength_eq_arm_add_leg N lam i hc, hA]
    simp only [hgdef]
    rw [hβi]
    omega
  have hhook : (∏ c ∈ Finset.range (lam.parts i),
        (weightToPartition N lam.parts).toYoungDiagram.hookLength i c)
      = ∏ c ∈ Finset.range (lam.parts i), (β i - g c) := by
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    rw [← hkey c hc]
  rw [hhook, ← prod_range_sub_eq_factorial (β i), ← hunion, Finset.prod_union hdisj,
      hSA, hSB, Finset.prod_image (fun x _ y _ h => hβinj h),
      Finset.prod_image (fun x _ y _ h => hg_inj h)]
  exact mul_comm _ _

/-- **Part B — the hook-length identity**
(book `Discussion_hook_length_derivation`, lines 18–end).

The Vandermonde product of the beta-numbers `l_j = λ_j + (N-1-j)` times the
hook-length product of `λ` equals `∏_j l_j!`. This is the cancellation that turns
the determinant formula `n!·∏(l_i−l_j)/∏l_j!` into the hook-length formula
`n!/∏h(i,j)`. Pure combinatorics — independent of all representation theory and of
Part A. -/
theorem hookLengthProduct_mul_vandermonde_eq_prod_factorial
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    (∏ i, ∏ j ∈ Finset.Ioi i,
        (shiftedExps N lam.parts i - shiftedExps N lam.parts j) : ℕ) *
      (lam.sum_eq ▸ weightToPartition N lam.parts).toYoungDiagram.hookLengthProduct =
      (∏ j, (shiftedExps N lam.parts j).factorial : ℕ) := by
  rw [hookLengthProduct_cast lam.sum_eq, hookLengthProduct_eq_prod_rows,
      ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  exact row_hook_gap_prod_eq_factorial N lam i

/-- The arithmetic that combines Part A (`n!·V/L`) and Part B (`V·H = L`) into the
hook-length quotient `n!/H`, with the ℕ-division on the right cast to ℚ via
`H ∣ n!`. -/
private lemma frobeniusDetForm_eq_hookFormula_aux {nf V H L : ℕ}
    (hB : V * H = L) (hVpos : 0 < V) (hHpos : 0 < H) (hdvd : H ∣ nf) :
    (nf : ℚ) * (V : ℚ) / (L : ℚ) = ((nf / H : ℕ) : ℚ) := by
  have hV' : (V : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hVpos.ne'
  have hH' : (H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hHpos.ne'
  subst hB
  rw [Nat.cast_div hdvd hH']
  push_cast
  field_simp

/-- **(THE ONE HARD STEP — book's `Discussion_hook_length_derivation`.)**
The Frobenius character value at the identity equals the hook-length quotient.

Combines the two book steps: Part A
(`charValue_trivialCycleType_eq_frobeniusDetForm`, the Vandermonde determinant
computation `charValue = n!·∏(l_i−l_j)/∏l_j!`) and Part B
(`hookLengthProduct_mul_vandermonde_eq_prod_factorial`, the cancellation
`∏(l_i−l_j)·∏h = ∏l_j!`). The beta-numbers `l_j = λ_j + (N-1-j)` are strictly
decreasing, so the Vandermonde product is positive; with `H ∣ n!`
(`hookLengthProduct_dvd_factorial`) the ℕ-division casts cleanly to ℚ. -/
theorem charValue_trivialCycleType_eq_hookFormula
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    charValue N lam (trivialCycleType n) =
      ((n.factorial /
        (lam.sum_eq ▸ weightToPartition N lam.parts).toYoungDiagram.hookLengthProduct
          : ℕ) : ℚ) := by
  rw [charValue_trivialCycleType_eq_frobeniusDetForm N lam]
  have hVpos : 0 < (∏ i, ∏ j ∈ Finset.Ioi i,
      (shiftedExps N lam.parts i - shiftedExps N lam.parts j) : ℕ) := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : shiftedExps N lam.parts j < shiftedExps N lam.parts i := by
      simp only [shiftedExps]
      have h1 : lam.parts j ≤ lam.parts i := lam.decreasing hij.le
      have h2 : N - 1 - (j : ℕ) < N - 1 - (i : ℕ) := by
        have hjlt : (j : ℕ) < N := j.isLt
        have hij' : (i : ℕ) < (j : ℕ) := hij
        omega
      omega
    omega
  have hHpos : 0 < (lam.sum_eq ▸ weightToPartition N lam.parts).toYoungDiagram.hookLengthProduct :=
    YoungDiagram.hookLengthProduct_pos _
  have hdvd : (lam.sum_eq ▸ weightToPartition N lam.parts).toYoungDiagram.hookLengthProduct ∣
      n.factorial :=
    hookLengthProduct_dvd_factorial n (lam.sum_eq ▸ weightToPartition N lam.parts)
  exact frobeniusDetForm_eq_hookFormula_aux
    (hookLengthProduct_mul_vandermonde_eq_prod_factorial N lam) hVpos hHpos hdvd

/-- **Book route, payoff 1:** the Frobenius character value at the identity
equals the number of standard Young tableaux — via the hook-length quotient on
both sides (`charValue_trivialCycleType_eq_hookFormula` + the proven FRT
`card_standardYoungTableau_eq`). No Garnir straightening. -/
theorem charValue_trivialCycleType_eq_card_syt
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    charValue N lam (trivialCycleType n) =
      (Nat.card (StandardYoungTableau n
        (lam.sum_eq ▸ weightToPartition N lam.parts)) : ℚ) := by
  rw [charValue_trivialCycleType_eq_hookFormula,
      card_standardYoungTableau_eq]

/-- **Book route, payoff 2 (retires Wall 3):** `dim_ℂ V_λ = #SYT`, obtained from
the Frobenius character formula alone — chaining the proven
`charValue_trivialCycleType_eq_spechtFinrank_rat` with the route above. This
re-proves the content of `finrank_spechtModule_eq_card_syt'` WITHOUT
`generalizedPolytabloidTab_mem_span_polytabloidTab` (the Garnir straightening). -/
theorem finrank_spechtModule_eq_card_syt_via_frobenius
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    (Module.finrank ℂ
        (SpechtModule n (lam.sum_eq ▸ weightToPartition N lam.parts)) : ℚ) =
      (Nat.card (StandardYoungTableau n
        (lam.sum_eq ▸ weightToPartition N lam.parts)) : ℚ) := by
  rw [← charValue_trivialCycleType_eq_spechtFinrank_rat]
  exact charValue_trivialCycleType_eq_card_syt N lam

end
end Etingof

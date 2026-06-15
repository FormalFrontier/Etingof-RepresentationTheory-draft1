import Mathlib
import EtingofRepresentationTheory.Chapter5.SchurWeylPolynomialIdentity
import EtingofRepresentationTheory.Chapter5.FRTHelpers

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

/-! ### Part A, steps 1–6 (analytic / coefficient extraction half, #4669)

Reduce `charValue N λ 1` to a falling-factorial (`descPochhammer`) determinant,
over ℚ. The three lemmas below are the multinomial-coefficient extraction
(`coeff_sum_X_pow_eq_multinomial`), the per-permutation falling-factorial
bookkeeping (`multinomial_mul_prod_factorial_eq`), and their assembly
(`charValue_trivialCycleType_eq_descPochhammer_det`). The Vandermonde column
reduction (step 7) is `descPochhammer_alternant_det_eq_prod_sub` above; the
capstone combining the two is `charValue_trivialCycleType_eq_frobeniusDetForm`. -/

/-- **Step 4 (multinomial coefficient).** The coefficient of `x^γ` in `(∑ᵢ Xᵢ)ⁿ`
is the multinomial coefficient `multinomial univ γ`, whenever `∑ γ = n`. -/
private lemma coeff_sum_X_pow_eq_multinomial (N n : ℕ) (γ : Fin N → ℕ)
    (hγ : ∑ i, γ i = n) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm γ)
        ((∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n)
      = (Nat.multinomial Finset.univ γ : ℚ) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag, MvPolynomial.coeff_sum, Finset.sum_eq_single γ]
  · rw [show ((Nat.multinomial Finset.univ γ : ℕ) : MvPolynomial (Fin N) ℚ)
          = MvPolynomial.C ((Nat.multinomial Finset.univ γ : ℚ)) from
        (map_natCast MvPolynomial.C _).symm,
      MvPolynomial.coeff_C_mul, prod_X_pow_eq_monomial', MvPolynomial.coeff_monomial,
      if_pos rfl, mul_one]
  · intro k _ hkne
    rw [show ((Nat.multinomial Finset.univ k : ℕ) : MvPolynomial (Fin N) ℚ)
          = MvPolynomial.C ((Nat.multinomial Finset.univ k : ℚ)) from
        (map_natCast MvPolynomial.C _).symm,
      MvPolynomial.coeff_C_mul, prod_X_pow_eq_monomial', MvPolynomial.coeff_monomial,
      if_neg (fun h => hkne (Finsupp.equivFunOnFinite.symm.injective h)), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_piAntidiag.mpr ⟨hγ, fun i _ => Finset.mem_univ i⟩) hmem

/-- **Step 5 (falling-factorial bookkeeping).** For a permutation `τ`, after clearing
the `∏ βⱼ!` denominator the multinomial coefficient of `(βᵢ − e(τ i))ᵢ` becomes a
product of descending factorials (`= descPochhammer` evaluations). The `if` matches
the support gap: when some `e(τ i) > βᵢ` both sides vanish. -/
private lemma multinomial_mul_prod_factorial_eq
    (N n : ℕ) (β e : Fin N → ℕ) (τ : Equiv.Perm (Fin N))
    (hβ : ∑ i, β i = n + ∑ i, e i) :
    (if (∀ i, e (τ i) ≤ β i) then Nat.multinomial Finset.univ (fun i => β i - e (τ i)) else 0)
        * (∏ j, (β j).factorial)
      = n.factorial * ∏ i, (β i).descFactorial (e (τ i)) := by
  by_cases H : ∀ i, e (τ i) ≤ β i
  · rw [if_pos H]
    have hsum : ∑ i, (β i - e (τ i)) = n := by
      have hadd : ∑ i, ((β i - e (τ i)) + e (τ i)) = ∑ i, β i :=
        Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (H i))
      rw [Finset.sum_add_distrib, Equiv.sum_comp τ e] at hadd
      omega
    have hfac : ∏ j, (β j).factorial
        = (∏ i, (β i - e (τ i)).factorial) * ∏ i, (β i).descFactorial (e (τ i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => (Nat.factorial_mul_descFactorial (H i)).symm)
    rw [hfac, ← mul_assoc, mul_comm (Nat.multinomial _ _) _, Nat.multinomial_spec, hsum]
  · rw [if_neg H, zero_mul]
    obtain ⟨i, hi⟩ := not_forall.mp H
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hi)), mul_zero]

/-- **Part A, steps 1–6 (#4669): `charValue → descPochhammer determinant`.**

`charValue N λ 1` is the coefficient of `x^{λ+ρ}` in `Δ(x)·(∑ᵢ Xᵢ)ⁿ`
(`psumPart_trivialCycleType`). Expanding `Δ = det(alternantMatrix)` as a signed
monomial sum (`Matrix.det_apply`), the coefficient extraction shifts each monomial
(`coeff_monomial_mul'`) onto the multinomial coefficients of `(∑X)ⁿ`
(`coeff_sum_X_pow_eq_multinomial`), and the falling-factorial bookkeeping
(`multinomial_mul_prod_factorial_eq`) folds the signed sum back into the
determinant of the descending-factorial matrix
`Aᵢⱼ = (descPochhammer ℤ (N−1−j)).eval βᵢ`, with `β = shiftedExps`. -/
private theorem charValue_trivialCycleType_eq_descPochhammer_det
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    charValue N lam (trivialCycleType n) =
      (n.factorial : ℚ) / (∏ j, ((shiftedExps N lam.parts j).factorial : ℚ)) *
        ((Matrix.of fun i j : Fin N =>
            (descPochhammer ℤ (vandermondeExps N j)).eval
              (shiftedExps N lam.parts i : ℤ)).det : ℚ) := by
  classical
  rw [show charValue N lam (trivialCycleType n)
        = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts))
            ((alternantMatrix N (vandermondeExps N)).det *
              MvPolynomial.psumPart (Fin N) ℚ (trivialCycleType n)) from rfl,
    psumPart_trivialCycleType]
  set e := vandermondeExps N with he_def
  set β := shiftedExps N lam.parts with hβ_def
  have hβsum : ∑ i, β i = n + ∑ i, e i := by
    simp only [hβ_def, he_def, shiftedExps, vandermondeExps]
    rw [Finset.sum_add_distrib, lam.sum_eq]
  have hβfac_ne : (∏ j, ((β j).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  -- Expand the alternant determinant as a signed sum of monomials.
  have hD : (alternantMatrix N e).det
      = ∑ σ : Equiv.Perm (Fin N),
          Equiv.Perm.sign σ •
            MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ) := by
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    rw [show ∏ j, alternantMatrix N e (σ j) j
          = ∏ j, (MvPolynomial.X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j from rfl,
        show ∏ j, (MvPolynomial.X (σ j) : MvPolynomial (Fin N) ℚ) ^ e j
          = ∏ i, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) ^ (e (σ.symm i))
          from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial' _
  -- The descending-factorial determinant, cast to ℚ, as a signed sum.
  have hdet : ((Matrix.of fun i j : Fin N =>
        (descPochhammer ℤ (e j)).eval (β i : ℤ)).det : ℚ)
      = ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ •
          (∏ i, ((β i).descFactorial (e (σ.symm i)) : ℚ)) := by
    rw [Int.cast_det, Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    rw [← Equiv.prod_comp σ (fun k => ((β k).descFactorial (e (σ.symm k)) : ℚ))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [Matrix.map_apply, descPochhammer_eval_eq_descFactorial, Equiv.symm_apply_apply]
  rw [hD, Finset.sum_mul, MvPolynomial.coeff_sum, hdet, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [smul_mul_assoc, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial_mul', one_mul,
      mul_smul_comm]
  congr 1
  by_cases H : ∀ i, e (σ.symm i) ≤ β i
  · have hle : (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm))
        ≤ Finsupp.equivFunOnFinite.symm β := by
      rw [Finsupp.le_iff' _ _ (Finset.subset_univ _)]
      intro i _
      simpa [Finsupp.equivFunOnFinite] using H i
    have hsum : ∑ i, (β i - e (σ.symm i)) = n := by
      have hadd : ∑ i, ((β i - e (σ.symm i)) + e (σ.symm i)) = ∑ i, β i :=
        Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (H i))
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ.symm e] at hadd
      omega
    rw [if_pos hle,
      show (Finsupp.equivFunOnFinite.symm β - Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm))
          = Finsupp.equivFunOnFinite.symm (fun i => β i - e (σ.symm i)) from by
        ext i; rw [Finsupp.tsub_apply]; simp [Finsupp.equivFunOnFinite],
      coeff_sum_X_pow_eq_multinomial N n _ hsum,
      div_mul_eq_mul_div, eq_div_iff hβfac_ne]
    have hL2 := multinomial_mul_prod_factorial_eq N n β e σ.symm hβsum
    rw [if_pos H] at hL2
    exact_mod_cast hL2
  · have hnle : ¬ (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm))
        ≤ Finsupp.equivFunOnFinite.symm β := by
      rw [Finsupp.le_iff' _ _ (Finset.subset_univ _)]
      push_neg
      obtain ⟨i, hi⟩ := not_forall.mp H
      exact ⟨i, Finset.mem_univ i, by
        have := not_le.mp hi; simpa [Finsupp.equivFunOnFinite] using this⟩
    obtain ⟨i, hi⟩ := not_forall.mp H
    have hHσ : (∏ i, ((β i).descFactorial (e (σ.symm i)) : ℚ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hi)]; exact Nat.cast_zero)
    rw [if_neg hnle, hHσ, mul_zero]

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
  rw [charValue_trivialCycleType_eq_descPochhammer_det N lam,
    descPochhammer_alternant_det_eq_prod_sub N (shiftedExps N lam.parts)
      (shiftedExps_strictAnti lam)]
  push_cast
  ring

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

/-! ## Surjectivity: every partition is a `BoundedPartition n n` weight (issue #4595)

`finrank_spechtModule_eq_card_syt_via_frobenius` is stated for partitions of the
shape `weightToPartition n bp.parts`. To reach an *arbitrary* `Nat.Partition n`
we show every partition of `n` arises this way: pad its sorted parts with zeros
to length `n`. The helper lemmas reproduce the `private` `canonicalBP` machinery
of `Theorem5_22_1.lean`, specialised so the construction starts from the
partition itself rather than from another bounded partition. -/

/-- A list of positive naturals has length at most its sum. -/
private lemma list_length_le_sum_of_pos (m : List ℕ) (hm : ∀ x ∈ m, 0 < x) :
    m.length ≤ m.sum := by
  induction m with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    simp only [List.length_cons, List.sum_cons]
    have ha := hm a (by simp)
    have ht := ih (fun x hx => hm x (by simp [hx]))
    omega

/-- Summing `l.getD · 0` over `Fin n` recovers the list sum once `l.length ≤ n`. -/
private lemma sum_getD_eq_sum (l : List ℕ) (n : ℕ) (hlen : l.length ≤ n) :
    ∑ i : Fin n, l.getD i.val 0 = l.sum := by
  induction n generalizing l with
  | zero =>
    have := List.eq_nil_of_length_eq_zero (by omega : l.length = 0)
    subst this; rfl
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    cases l with
    | nil => simp [ih [] (Nat.zero_le _)]
    | cons a t =>
      simp only [List.getD_cons_zero, List.sum_cons, Fin.val_zero]
      congr 1
      have hstep : ∀ i : Fin n, (a :: t).getD i.succ.val 0 = t.getD i.val 0 := by
        intro ⟨i, _⟩; simp [List.getD_cons_succ]
      simp_rw [hstep]
      exact ih t (by simpa using hlen)

/-- `l.getD · 0` is antitone on `Fin n` when `l` is sorted in weakly decreasing order. -/
private lemma getD_antitone_of_pairwise {n : ℕ} (l : List ℕ) (h : l.Pairwise (· ≥ ·)) :
    Antitone (fun i : Fin n => l.getD i.val 0) := by
  intro i j hij
  show l.getD j.val 0 ≤ l.getD i.val 0
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · by_cases hj : j.val < l.length
    · have hi : i.val < l.length := by omega
      rw [List.getD_eq_getElem (hn := hj), List.getD_eq_getElem (hn := hi)]
      exact List.pairwise_iff_get.mp h ⟨i.val, hi⟩ ⟨j.val, hj⟩ hlt
    · rw [List.getD_eq_default (hn := by omega)]
      exact Nat.zero_le _

/-- Filtering the positive entries out of `ofFn (l.getD · 0)` on `Fin m` recovers `l`,
provided `l` has only positive entries and `l.length ≤ m`. -/
private lemma ofFn_getD_filter_pos :
    ∀ (m : ℕ) (ll : List ℕ), (∀ x ∈ ll, 0 < x) → ll.length ≤ m →
      (List.ofFn (fun i : Fin m => ll.getD i.val 0)).filter (fun x => decide (0 < x)) = ll := by
  intro m
  induction m with
  | zero => intro ll _ hlen; simp [List.eq_nil_of_length_eq_zero (by omega : ll.length = 0)]
  | succ m ih =>
    intro ll hll hlen
    simp only [List.ofFn_succ, Fin.val_zero, List.filter_cons]
    cases ll with
    | nil =>
      simp only [List.getD_nil, List.ofFn_const, List.filter_replicate,
        show ¬ decide (0 < 0) = true from by simp]
      simp
    | cons a t =>
      simp only [List.getD_cons_zero]
      have ha : 0 < a := hll a (by simp)
      rw [show decide (0 < a) = true from decide_eq_true ha]
      simp only [ite_true]
      congr 1
      show (List.ofFn (fun i : Fin m => t.getD i.val 0)).filter (fun x => decide (0 < x)) = t
      exact ih t (fun x hx => hll x (by simp [hx]))
        (by simp only [List.length_cons] at hlen; omega)

/-- **Surjectivity of the Schur-Weyl weight map.** Every `Nat.Partition n` is the
underlying partition of some `BoundedPartition n n` (its sorted parts, padded with
zeros to length `n`). This lets the Frobenius dimension result, stated for
`weightToPartition`-shaped partitions, descend to an arbitrary partition. -/
theorem exists_boundedPartition_weightToPartition_eq (n : ℕ) (la : Nat.Partition n) :
    ∃ bp : BoundedPartition n n,
      (bp.sum_eq ▸ weightToPartition n bp.parts : Nat.Partition n) = la := by
  have hpos : ∀ x ∈ la.sortedParts, 0 < x := by
    intro x hx
    refine la.parts_pos ?_
    have h := Multiset.sort_eq la.parts (· ≥ ·)
    rw [show la.parts.sort (· ≥ ·) = la.sortedParts from rfl] at h
    exact h ▸ Multiset.mem_coe.mpr hx
  have hlen : la.sortedParts.length ≤ n := by
    have hsum : la.sortedParts.sum = n := sortedParts_sum_eq n la
    have := list_length_le_sum_of_pos la.sortedParts hpos
    omega
  refine ⟨{ parts := fun i : Fin n => la.sortedParts.getD i.val 0
            decreasing := getD_antitone_of_pairwise la.sortedParts
              (by rw [show la.sortedParts = la.parts.sort (· ≥ ·) from rfl]
                  exact Multiset.pairwise_sort _ _)
            sum_eq := by
              rw [sum_getD_eq_sum la.sortedParts n hlen]; exact sortedParts_sum_eq n la }, ?_⟩
  have hrec : ∀ (p q : ℕ) (h : p = q) (P : Nat.Partition p), (h ▸ P).parts = P.parts := by
    intro p q h P; subst h; rfl
  apply Nat.Partition.ext
  rw [hrec _ _ _ (weightToPartition n (fun i : Fin n => la.sortedParts.getD i.val 0))]
  show (Finset.univ.val.map (fun i : Fin n => la.sortedParts.getD i.val 0)).filter (0 < ·) =
      la.parts
  rw [Fin.univ_val_map, Multiset.filter_coe, ofFn_getD_filter_pos n la.sortedParts hpos hlen]
  exact Multiset.sort_eq _ _

/-- **Book route, payoff 2 (general `λ`):** `dim_ℂ V_λ = #SYT` for an *arbitrary*
partition `λ`, from `finrank_spechtModule_eq_card_syt_via_frobenius` plus
surjectivity of `weightToPartition`. This is the Wall-3-free (no Garnir
straightening) replacement for the polytabloid-basis route. -/
theorem finrank_spechtModule_eq_card_syt_general (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (SpechtModule n la) = Nat.card (StandardYoungTableau n la) := by
  obtain ⟨bp, hbp⟩ := exists_boundedPartition_weightToPartition_eq n la
  have h := finrank_spechtModule_eq_card_syt_via_frobenius n bp
  rw [hbp] at h
  exact_mod_cast h

end
end Etingof

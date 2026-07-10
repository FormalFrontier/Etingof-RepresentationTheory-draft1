import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Irreducible
import EtingofRepresentationTheory.Chapter5.Definition5_14_2

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

/-- The coefficient of the identity permutation in `C · c_λ` equals the content `c(λ)`.

This is the combinatorial heart of the problem. Expanding `(C · c_λ)(e) = ∑_{i<j} c_λ((ij))`, the
coefficient of a transposition `(ab)` in the Young symmetrizer `c_λ = b_λ a_λ` is `+1` when `a, b`
lie in the same row, `-1` when they lie in the same column, and the remaining (cross) contributions
cancel in the signed sum. Summing gives
`∑_rows C(row_len, 2) − ∑_cols C(col_height, 2) = ∑_cells (col − row) = c(λ)`.

TODO: discharge this finite coefficient computation. The main theorem is otherwise complete. -/
private lemma sumTranspositions_youngSymmetrizer_coeff_one (n : ℕ) (la : Nat.Partition n) :
    (sumTranspositions n * YoungSymmetrizer n la : SymGroupAlgebra n) 1 = (content la : ℂ) := by
  sorry

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
    show sumTranspositions n * x ∈ V
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
    LinearMap.restrict_coe_apply LC hmaps _
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
    rw [Finsupp.smul_apply, smul_eq_mul, youngSymmetrizer_identity_coeff, mul_one] at h1
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

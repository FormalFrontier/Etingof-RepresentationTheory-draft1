import Mathlib
import EtingofRepresentationTheory.Chapter5.Proposition5_22_2

/-!
# The Cauchy character difference: the determinant shift removes the `ν_N ≥ 1` part

This file isolates the **combinatorial crux** of the Cauchy determinant-quotient
computation (issue #4905, part (a) of #4896). It is the identity, at the level of
formal characters in `MvPolynomial (Fin N) ℚ`, that underlies

  `formalCharacter (A/det)_d = formalCharacter A_d − formalCharacter (A_{d-N} ⊗ χ)`.

Each total-degree-`d` part of `k[Xᵢⱼ]` has formal character (the right-`GL_N`
Cauchy form, `polyRightDegreeFDRep_formalCharacter`, `CauchyCharacterRight.lean`)

  `∑_{ν : BoundedPartition N d} mult_ν • S_ν`,   `mult_ν = s_ν(1,…,1)`.

Multiplication by `det` shifts every constituent's highest weight by `(1,…,1)`
(`schurPoly_shift`: `S_{μ+1} = (∏ᵢ Xᵢ)·S_μ`), so the formal character of the
det-ideal slice `det · A_{d-N}` (`= A_{d-N} ⊗ χ`) is the original degree-`(d-N)`
character multiplied by `∏ᵢ Xᵢ`. The theorem `cauchyMult_mul_prodX_eq_lastPart_pos`
identifies that product with the part of the degree-`d` character supported on the
bounded partitions whose parts are **all `≥ 1`** (equivalently, those `ν` with
`0 ∉ Set.range ν.parts`). Subtracting it from the full degree-`d` character leaves
exactly the constituents with `ν_N = 0` (`0 ∈ Set.range ν.parts`) — the part-(a)
deliverable.

The bijection realizing the shift, `bddPartShift : BoundedPartition N (d-N) ≃
{ν : BoundedPartition N d // 0 ∉ Set.range ν.parts}`, is recorded explicitly
(`bddPartShift` / `bddPartUnshift`), since both directions are needed downstream.
-/

namespace Etingof

open MvPolynomial

/-- Two bounded partitions are equal once their parts agree (the `decreasing`
and `sum_eq` fields are propositions, hence proof-irrelevant). -/
theorem bddPart_ext {N n : ℕ} {a b : BoundedPartition N n} (h : a.parts = b.parts) :
    a = b := by
  cases a; cases b; simp only [BoundedPartition.mk.injEq]; exact h

/-- The all-ones shift `μ ↦ μ + (1,…,1)` sending a bounded partition of `d - N`
to one of `d`: every part is raised by one, so the sum rises by `N`. -/
def bddPartShift {N d : ℕ} (hd : N ≤ d) (μ : BoundedPartition N (d - N)) :
    BoundedPartition N d where
  parts i := μ.parts i + 1
  decreasing i j hij := Nat.add_le_add_right (μ.decreasing hij) 1
  sum_eq := by
    have h : ∑ i : Fin N, (μ.parts i + 1) = (∑ i : Fin N, μ.parts i) + N := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    rw [h, μ.sum_eq]; omega

/-- The inverse all-ones shift `ν ↦ ν − (1,…,1)`, defined when every part of `ν`
is `≥ 1` (recorded as `0 ∉ Set.range ν.parts`). -/
def bddPartUnshift {N d : ℕ} (hd : N ≤ d) (ν : BoundedPartition N d)
    (hν : (0 : ℕ) ∉ Set.range ν.parts) : BoundedPartition N (d - N) where
  parts i := ν.parts i - 1
  decreasing i j hij := Nat.sub_le_sub_right (ν.decreasing hij) 1
  sum_eq := by
    have h1 : ∀ i, 1 ≤ ν.parts i := by
      intro i
      rcases Nat.eq_zero_or_pos (ν.parts i) with h | h
      · exact absurd (Set.mem_range.2 ⟨i, h⟩) hν
      · exact h
    have hsum : ∑ i : Fin N, ν.parts i = (∑ i : Fin N, (ν.parts i - 1)) + N := by
      have hsplit : ∑ i : Fin N, ν.parts i = ∑ i : Fin N, ((ν.parts i - 1) + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := h1 i; omega
      rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    rw [ν.sum_eq] at hsum; omega

/-- The evaluation of `∏ᵢ Xᵢ` at the all-ones point is `1`. -/
theorem eval_one_prod_X (N : ℕ) :
    MvPolynomial.eval (fun _ => (1 : ℚ))
        (∏ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) = 1 := by
  rw [map_prod]; simp

/-- The Schur-polynomial multiplicity `s_ν(1,…,1)` is invariant under the all-ones
shift (`s_{μ+1}(1,…,1) = s_μ(1,…,1)`): multiplying by `∏ᵢ Xᵢ` and evaluating at the
all-ones point contributes a factor `1`. -/
theorem eval_one_schurPoly_bddPartShift {N d : ℕ} (hd : N ≤ d)
    (μ : BoundedPartition N (d - N)) :
    MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N (bddPartShift hd μ).parts)
      = MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N μ.parts) := by
  have hs : schurPoly N (bddPartShift hd μ).parts
      = (∏ i : Fin N, MvPolynomial.X i) * schurPoly N μ.parts := by
    change schurPoly N (fun i => μ.parts i + 1) = _
    rw [schurPoly_shift]
  rw [hs, map_mul, eval_one_prod_X, one_mul]

/-- **Cauchy character difference (combinatorial crux).** Multiplying the
degree-`(d - N)` Cauchy character `∑_μ mult_μ • S_μ` by `∏ᵢ Xᵢ` (the formal
character of the `det`-shift) yields exactly the part of the degree-`d` Cauchy
character supported on the bounded partitions all of whose parts are `≥ 1`, i.e.
those `ν` with `0 ∉ Set.range ν.parts`. Subtracting this from the full degree-`d`
character leaves the constituents with `ν_N = 0`. -/
theorem cauchyMult_mul_prodX_eq_lastPart_pos {N d : ℕ} (hd : N ≤ d) :
    (∑ μ : BoundedPartition N (d - N),
        (MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N μ.parts)) • schurPoly N μ.parts)
        * (∏ i : Fin N, MvPolynomial.X i)
      = ∑ ν ∈ Finset.univ.filter
            (fun ν : BoundedPartition N d => (0 : ℕ) ∉ Set.range ν.parts),
          (MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts)) • schurPoly N ν.parts := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_bij'
    (fun μ _ => bddPartShift hd μ)
    (fun ν hν => bddPartUnshift hd ν (Finset.mem_filter.1 hν).2)
    ?_ ?_ ?_ ?_ ?_
  · -- the shift lands in the filtered set (all parts `≥ 1`)
    intro μ _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rintro ⟨i, hi⟩
    have : μ.parts i + 1 = 0 := hi
    omega
  · -- the unshift lands in `univ`
    intro ν _; exact Finset.mem_univ _
  · -- `unshift ∘ shift = id`
    intro μ _
    apply bddPart_ext
    funext i
    change (μ.parts i + 1) - 1 = μ.parts i
    omega
  · -- `shift ∘ unshift = id`
    intro ν hν
    apply bddPart_ext
    funext i
    have hpos : 1 ≤ ν.parts i := by
      rcases Nat.eq_zero_or_pos (ν.parts i) with h | h
      · exact absurd (Set.mem_range.2 ⟨i, h⟩) (Finset.mem_filter.1 hν).2
      · exact h
    change (ν.parts i - 1) + 1 = ν.parts i
    omega
  · -- the summands match under the bijection
    intro μ _
    rw [eval_one_schurPoly_bddPartShift hd μ]
    have hs : schurPoly N (bddPartShift hd μ).parts
        = (∏ i : Fin N, MvPolynomial.X i) * schurPoly N μ.parts := by
      change schurPoly N (fun i => μ.parts i + 1) = _
      rw [schurPoly_shift]
    rw [hs, smul_mul_assoc, mul_comm (schurPoly N μ.parts) (∏ i : Fin N, MvPolynomial.X i)]

end Etingof

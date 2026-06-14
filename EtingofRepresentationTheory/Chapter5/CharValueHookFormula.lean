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
  sorry

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

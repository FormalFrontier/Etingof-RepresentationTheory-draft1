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

/-- **(THE ONE HARD STEP — book's `Discussion_hook_length_derivation`.)**
The Frobenius character value at the identity equals the hook-length quotient.

`charValue N λ (1)` is by definition the coefficient of `x^{λ+ρ}` in
`Δ(x) · (∑ᵢ Xᵢ)^n` (Vandermonde determinant times the trivial power-sum).
Expanding `Δ` as a signed monomial sum and extracting the coefficient
(`coeff_vandermonde_mul`, multinomial coefficients of `(∑X)^n`) yields the
determinant `det(l_j^{N-i})`, which by the Vandermonde formula equals
`n!/∏ l_j! · ∏_{i<j}(l_i - l_j) = n!/∏ h(i,j)`.

This is self-contained `MvPolynomial`/`Matrix.det` algebra — no representation
theory, no straightening. -/
theorem charValue_trivialCycleType_eq_hookFormula
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    charValue N lam (trivialCycleType n) =
      ((n.factorial /
        (lam.sum_eq ▸ weightToPartition N lam.parts).toYoungDiagram.hookLengthProduct
          : ℕ) : ℚ) := by
  sorry

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

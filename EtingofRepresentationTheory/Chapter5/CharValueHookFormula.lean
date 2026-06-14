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

/-- **ℚ analogue of `coeff_vandermonde_mul`.** The coefficient of `x^α` in
`(alternantMatrix N e).det · P` is the signed sum over permutations `σ` of the
shifted coefficients of `P`, where the shift `e ∘ σ⁻¹` is the exponent vector of
the monomial `∏ᵢ X_{σ i}^{e i}` appearing in the determinant expansion.

This mirrors `coeff_vandermonde_mul` (`Theorem5_15_1.lean`, stated over ℂ for the
`vandermondePoly`) but works directly with the ℚ-valued `alternantMatrix`
determinant that defines `charValue`, so no ℚ/ℂ transfer is needed. -/
private theorem coeff_alternant_mul {N : ℕ} (e : Fin N → ℕ)
    (P : MvPolynomial (Fin N) ℚ) (α : Fin N →₀ ℕ) :
    MvPolynomial.coeff α ((alternantMatrix N e).det * P) =
      ∑ σ : Equiv.Perm (Fin N),
        (Equiv.Perm.sign σ : ℤ) •
          (if Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm) ≤ α
            then MvPolynomial.coeff
              (α - Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) P
            else 0) := by
  rw [Matrix.det_apply, Finset.sum_mul, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hmon : (∏ i, alternantMatrix N e (σ i) i) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (e ∘ ⇑σ.symm)) (1 : ℚ) := by
    rw [show ∏ i, alternantMatrix N e (σ i) i =
        ∏ i, (MvPolynomial.X (σ i) : MvPolynomial (Fin N) ℚ) ^ e i from rfl,
      show ∏ i, (MvPolynomial.X (σ i) : MvPolynomial (Fin N) ℚ) ^ e i =
        ∏ i, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) ^ (e (σ.symm i)) from
          Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial' _
  rw [Units.smul_def, smul_mul_assoc, MvPolynomial.coeff_smul, hmon,
    MvPolynomial.coeff_monomial_mul', one_mul]

/-- **Multinomial coefficient of `(∑ᵢ Xᵢ)^n`.** For an exponent vector `β` with
`∑ᵢ βᵢ = n`, the coefficient of `x^β` in `(∑ᵢ Xᵢ)^n` is the multinomial
`n! / ∏ᵢ (βᵢ)!`. This is the rational-coefficient extraction step that evaluates
each term of the signed sum produced by `coeff_alternant_mul`. -/
private lemma coeff_sumXpow_multinomial {N : ℕ} (n : ℕ) (β : Fin N →₀ ℕ)
    (hβ : (∑ i, β i) = n) :
    ((∑ i : Fin N, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)) ^ n).coeff β =
      (n.factorial : ℚ) / ∏ i : Fin N, ((β i).factorial : ℚ) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag, MvPolynomial.coeff_sum]
  have hterm : ∀ k : Fin N → ℕ,
      MvPolynomial.coeff β
        ((Nat.multinomial Finset.univ k : MvPolynomial (Fin N) ℚ) *
          ∏ i, (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) ^ k i) =
        if k = Finsupp.equivFunOnFinite β then (Nat.multinomial Finset.univ k : ℚ) else 0 := by
    intro k
    rw [show (Nat.multinomial Finset.univ k : MvPolynomial (Fin N) ℚ) =
        MvPolynomial.C (Nat.multinomial Finset.univ k : ℚ) by push_cast; rfl,
      prod_X_pow_eq_monomial', MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    simp only [Equiv.symm_apply_eq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_ite_eq']
  have hmem : (Finsupp.equivFunOnFinite β : Fin N → ℕ) ∈
      Finset.piAntidiag Finset.univ n := by
    rw [Finset.mem_piAntidiag]; exact ⟨by simpa using hβ, by simp⟩
  rw [if_pos hmem]
  have hspec : (∏ i, (β i).factorial) * Nat.multinomial Finset.univ (⇑β) = n.factorial := by
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin N)) (⇑β)
    simpa [hβ] using h
  have hprod : (∏ i : Fin N, ((β i).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by positivity)
  rw [eq_div_iff hprod, ← Nat.cast_prod, ← Nat.cast_mul, Nat.cast_inj, mul_comm]
  exact hspec

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
  unfold charValue
  rw [psumPart_trivialCycleType, coeff_alternant_mul]
  -- Residual goal: the signed sum over `σ : Perm (Fin N)` of the coefficients
  -- `coeff (lF - (vandermondeExps ∘ σ⁻¹)) ((∑ X)^n)` equals
  -- `n! · ∏_{i<j}(l_i − l_j) / ∏_j l_j!`. Each nonzero coefficient is now the
  -- multinomial `n! / ∏_k (l_k − (N−1−σ⁻¹k))!` (`coeff_sumXpow_multinomial`, proven
  -- above; its sum-constraint `∑ (lF − vExpσ) = n` holds whenever `vExpσ ≤ lF`).
  -- What remains is the determinant assembly: reorganize the signed sum into
  -- `n!/∏l_j! · det(falling-factorial matrix Aⱼₖ = l_j‼/(l_j−(N−1−k))!)`, then
  -- column-reduce `det(A)` to `det(l_j^{N−i})` and apply `Matrix.det_vandermonde`
  -- to obtain `∏_{i<j}(l_i − l_j)`. (Tracked as a #4608 follow-up sub-issue.)
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

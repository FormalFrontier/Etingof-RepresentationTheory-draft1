# Proof route for `charValue_trivialCycleType_eq_frobeniusDetForm` (#4608)

This note records the complete, validated proof route for the Part-A crux of the
Frobenius dimension formula (#4595), together with the exact Mathlib lemmas that
make it tractable, and the decomposition into two self-contained sub-issues plus
a small capstone assembly. Written by session `cd407dc6` after a full
infrastructure audit (the original `sorry` is at
`Chapter5/CharValueHookFormula.lean:268`).

## The lemma

```lean
theorem charValue_trivialCycleType_eq_frobeniusDetForm
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) :
    charValue N lam (trivialCycleType n) =
      (n.factorial : ℚ) *
        ((∏ i, ∏ j ∈ Finset.Ioi i,
            (shiftedExps N lam.parts i - shiftedExps N lam.parts j) : ℕ) : ℚ) /
        ((∏ j, (shiftedExps N lam.parts j).factorial : ℕ) : ℚ)
```

Write `β := shiftedExps N lam.parts` (so `β j = λ_j + (N-1-j)`, strictly
*decreasing* by `shiftedExps_strictAnti`) and `e := vandermondeExps N` (so
`e j = N-1-j`).

## Definitions (all proven, sorry-free)

- `charValue N lam μ = MvPolynomial.coeff (equivFunOnFinite.symm β)`
  `((alternantMatrix N e).det * psumPart (Fin N) ℚ μ)`
  (`Proposition5_21_1.lean:334`).
- `alternantMatrix N e = Matrix.of fun i j => (X i)^(e j)` (`:35`).
- `vandermondeExps N j = N - 1 - j` (`:40`); `shiftedExps N lam j = lam j + (N-1-j)` (`:43`).

## The computation (validated by hand; matches `blobs/Chapter5/Discussion_hook_length_derivation.md` lines 1–18)

1. `psumPart_trivialCycleType` (`SchurWeylPolynomialIdentity.lean:42`, proven):
   `psumPart (Fin N) ℚ (trivialCycleType n) = (∑ i, X i)^n`. So
   `charValue = coeff_β ((alternantMatrix N e).det · (∑ X)^n)`.

2. Expand the alternant determinant with `Matrix.det_apply`:
   `(alternantMatrix N e).det = ∑_{σ∈S_N} sign σ · monomial (fun i => e (σ i)) 1`
   (each `∏_i X_i^{e(σ i)}` is the monomial at exponent `i ↦ e(σ i)`;
   `MvPolynomial.prod_X_pow_eq_monomial`, `Basic.lean:362`).

3. For each `σ`, `coeff_β (monomial (e∘σ) 1 · (∑X)^n)`
   `= coeff_{β - e∘σ} ((∑X)^n)` when `e∘σ ≤ β` else `0`
   (`MvPolynomial.coeff_monomial_mul` / `coeff_monomial_mul_shift`,
   `Theorem5_15_1.lean:236`). The exponent sums match: `∑(β - e∘σ) = ∑β - ∑e = n`
   always (since `∑β = n + ∑e`), so the support condition is automatic and the
   subtraction is the genuine one exactly when `e(σ i) ≤ β i ∀i`.

4. **Multinomial coefficient.** `coeff_γ ((∑ i, X i)^n) = n! / ∏_i (γ i)!` when
   `∑γ = n`. Mathlib route: `Finset.sum_pow`
   (`Mathlib/Data/Nat/Choose/Multinomial.lean`, expansion of `(s.sum x)^n` with
   multinomial coefficients) + `Nat.multinomial_spec`
   (`(∏ i∈s, (f i)!) * multinomial s f = (∑ i∈s, f i)!`). The project already has
   `sum_X_pow_coeff` (`FormalCharacterIso.lean:934`, over ℚ):
   `coeff μ ((∑X)^n) = #{f : Fin n → Fin N | tensorWeight N f = μ}` — the coloring
   count — so step 4 = "coloring count = multinomial coefficient = n!/∏γ!"; either
   reuse `sum_X_pow_coeff` then count, or go straight via `Finset.sum_pow`.

5. Collect: with `γ = β - e∘σ`,
   `charValue = ∑_σ sign σ · n!/∏_i (β i - e(σ i))!`
   `= n!/∏_i (β i)! · ∑_σ sign σ · ∏_i descFactorial (β i) (e (σ i))`
   (multiply/divide by `∏ β!`; `descFactorial (β i) (e(σi)) = (β i)!/(β i - e(σi))!`,
   and `= 0` when `e(σi) > β i`, matching the support gap).
   `Nat.descFactorial_eq_factorial_mul_choose`, `descPochhammer_eval_eq_descFactorial`.

6. Recognise the signed sum as a determinant (`Matrix.det_apply` backwards):
   `∑_σ sign σ ∏_i A(i, σ i) = (Matrix.of A).det` with
   `A i j = descFactorial (β i) (e j) = (descPochhammer ℤ (e j)).eval (β i : ℤ)`.

   ⇒ **`charValue = (n!/∏β!) · (det (of fun i j => (descPochhammer ℤ (N-1-j)).eval (β i)) : ℚ)`.**   [= Sub-A1]

7. **Vandermonde column reduction.** `e j = N-1-j` is the column reflection of the
   ascending `0,1,…,N-1`. `descPochhammer ℤ k` is monic of degree `k`
   (`monic_descPochhammer`, `descPochhammer_natDegree`), so by
   `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` (`Vandermonde.lean:278`)
   with `p k = descPochhammer ℤ k`:
   `det (of fun i j => (descPochhammer ℤ j).eval (β i)) = (Matrix.vandermonde β).det`
   `= ∏_i ∏_{j∈Ioi i} (β j - β i)` (`Matrix.det_vandermonde`, `:218`;
   `Matrix.vandermonde v = of fun i j => (v i)^(j:ℕ)`).
   Reflecting columns `j ↦ N-1-j` is a permutation of sign `(-1)^{C(N,2)}`, which
   cancels against `∏_{i<j}(β j - β i) = (-1)^{C(N,2)} ∏_{i<j}(β i - β j)` (β strictly
   decreasing ⇒ `β i - β j > 0` for `i<j`).

   ⇒ **`det (of fun i j => (descPochhammer ℤ (N-1-j)).eval (β i)) = ∏_{i<j} (β i - β j)`.**   [= Sub-A2]

8. Capstone: combine Sub-A1 + Sub-A2, cast ℤ→ℚ, and use `shiftedExps_strictAnti`
   to identify the ℤ product `∏_{i<j}(β i - β j)` with the ℕ product in the goal
   (`Nat.cast`, the differences are genuine positive ℕ subtractions). Then a
   `field_simp`/`ring`-style rearrangement (`∏β! ≠ 0`) yields the stated form
   `n! · (∏diff : ℕ) / (∏β! : ℕ)`.

## Decomposition (filed as sub-issues)

- **Sub-A1 (analytic / coefficient extraction):** steps 1–6. Reduce `charValue`
  to `(n!/∏β!) · det(descPochhammer falling-factorial matrix)`. The bulk
  (det expansion, multinomial coefficient, falling-factorial bookkeeping). Over ℚ.
- **Sub-A2 (algebraic / Vandermonde):** step 7. The pure determinant identity
  `det (of fun i j => (descPochhammer ℤ (N-1-j)).eval (β i)) = ∏_{i<j}(β i - β j)`
  for strictly antitone `β`. Near-mechanical via
  `det_eval_matrixOfPolynomials_eq_det_vandermonde` + `det_vandermonde`; the only
  real work is the `j ↦ N-1-j` reflection sign.
- **Capstone (#4608 residual):** step 8 — combine + cast. Small.

## Key Mathlib lemmas (verified present in the pinned Mathlib)

`Finset.sum_pow`, `Nat.multinomial_spec`, `Nat.descFactorial_eq_factorial_mul_choose`,
`descPochhammer_eval_eq_descFactorial`, `monic_descPochhammer`,
`descPochhammer_natDegree`, `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde`
(`Vandermonde.lean:278`), `Matrix.det_vandermonde` (`:218`),
`Matrix.vandermonde` (`:83`), `Matrix.det_apply`,
`MvPolynomial.prod_X_pow_eq_monomial` (`Basic.lean:362`).

## Project lemmas to reuse

`psumPart_trivialCycleType` (`SchurWeylPolynomialIdentity.lean:42`),
`coeff_monomial_mul_shift` (`Theorem5_15_1.lean:236`),
`sum_X_pow_coeff` (`FormalCharacterIso.lean:934`),
`shiftedExps_strictAnti` (`Proposition5_21_1.lean:440`),
`alternant_coeff_kronecker` (`Proposition5_21_1.lean:445`),
`prod_range_sub_eq_factorial` (`CharValueHookFormula.lean:271`).
</content>
</invoke>

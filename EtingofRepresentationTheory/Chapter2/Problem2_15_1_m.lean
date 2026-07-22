import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.Basic
import EtingofRepresentationTheory.Chapter2.Sl2Irrep

/-!
# Clebsch–Gordan decomposition (Problem 2.15.1(m))

We formalize the **character identity** underlying the Clebsch–Gordan decomposition
of the tensor product of two irreducible `sl(2)`-representations:
`V_λ ⊗ V_μ ≅ V_{λ+μ} ⊕ V_{λ+μ−2} ⊕ … ⊕ V_{|λ−μ|}`, i.e.
`V_λ ⊗ V_μ ≅ ⨁_{k=0}^{min(λ,μ)} V_{λ+μ−2k}`.

## The character approach (the book's hint)

For a finite dimensional `sl(2)`-representation `V` one introduces the character
`χ_V(x) = Tr(e^{xH})`. It is additive on direct sums and multiplicative on tensor
products: `χ_{V⊕W} = χ_V + χ_W`, `χ_{V⊗W} = χ_V · χ_W`. On `V_λ` the operator `H`
acts on the standard basis `e_0,…,e_λ` with the weights `λ, λ−2, …, −λ` (these are
the diagonal entries `d−1−2k` of `rhoH` with `d = λ+1`), so writing `q = e^x`,
```
  χ_{V_λ}(q) = q^λ + q^{λ−2} + ⋯ + q^{−λ} = q^{−λ} (1 + q² + ⋯ + q^{2λ}).
```
Substituting `X = q²` and clearing the common factor `q^{−(λ+μ)}`, the
Clebsch–Gordan identity `χ_{V_λ} · χ_{V_μ} = Σ_k χ_{V_{λ+μ−2k}}` becomes the
polynomial identity proved below as `clebsch_gordan_charPoly`:
```
  charPoly λ · charPoly μ = Σ_{k=0}^{min(λ,μ)} X^k · charPoly (λ+μ−2k),
```
where `charPoly n = 1 + X + ⋯ + X^n` is the (shifted) character of `V_n`. The
factor `X^k` records the weight shift introduced by clearing `q^{−(λ+μ)}`; the
irreducible components are exactly the `V_{λ+μ−2k}` for `k = 0,…,min(λ,μ)`.

Evaluating at `X = 1` recovers the dimension count
`(λ+1)(μ+1) = Σ_{k=0}^{min(λ,μ)} (λ+μ−2k+1)` as `clebsch_gordan_dim`.

## Scope

This file proves the character identity (the combinatorial heart of the
decomposition, equivalent to the book's character computation) and the dimension
count. Promoting this to a genuine `sl(2)`-module isomorphism — by exhibiting the
explicit highest-weight vectors in `V_λ ⊗ V_μ` annihilated by `E` and matching
dimensions — is tracked as follow-up work; see the module docstring of
`Chapter2/Sl2Irrep.lean` and the Problem 2.15.1(m) issue.

The base ring is `ℤ` (the identity holds over any commutative ring; integer
coefficients keep the dimension count over `ℤ`).
-/

open Polynomial Finset

namespace Etingof.Sl2Irrep

/-- The (shifted) character polynomial of `V_n`: `charPoly n = 1 + X + ⋯ + X^n`.
With `X = q²` this is `q^λ · χ_{V_n}(q)`, the character of the `(n+1)`-dimensional
irreducible `sl(2)`-representation up to the overall weight shift `q^{-n}`. -/
noncomputable def charPoly (n : ℕ) : Polynomial ℤ := ∑ j ∈ range (n + 1), X ^ j

/-- `charPoly n · (X − 1) = X^{n+1} − 1` (geometric sum). -/
theorem charPoly_mul_X_sub_one (n : ℕ) :
    charPoly n * (X - 1) = X ^ (n + 1) - 1 := by
  rw [charPoly]; exact geom_sum_mul X (n + 1)

/-- `X − 1` is a nonzero polynomial over `ℤ`. -/
theorem X_sub_one_ne_zero : (X - 1 : Polynomial ℤ) ≠ 0 := by
  rw [← C_1]; exact (monic_X_sub_C 1).ne_zero

/-- Folding `(X − 1)` into the Clebsch–Gordan sum once: the right-hand side times
`(X − 1)` telescopes to `charPoly (min λ μ) · (X^{λ+μ+1−min λ μ} − 1)`. -/
theorem rhs_mul_X_sub_one (lam mu : ℕ) :
    (∑ k ∈ range (min lam mu + 1), X ^ k * charPoly (lam + mu - 2 * k)) * (X - 1)
      = charPoly (min lam mu) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
  set m := min lam mu with hm
  rw [Finset.sum_mul]
  -- Each summand: X^k · charPoly(λ+μ−2k) · (X−1) = X^{λ+μ+1−k} − X^k.
  have hterm : ∀ k ∈ range (m + 1),
      X ^ k * charPoly (lam + mu - 2 * k) * (X - 1)
        = X ^ (lam + mu + 1 - k) - X ^ k := by
    intro k hk
    rw [mem_range] at hk
    have h2k : 2 * k ≤ lam + mu := by omega
    rw [mul_assoc, charPoly_mul_X_sub_one, mul_sub, mul_one, ← pow_add,
      show k + (lam + mu - 2 * k + 1) = lam + mu + 1 - k from by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  -- Reindex the first sum: ∑_{k=0}^m X^{λ+μ+1−k} = X^{λ+μ+1−m} · charPoly m.
  have hreidx : ∑ k ∈ range (m + 1), X ^ (lam + mu + 1 - k)
      = X ^ (lam + mu + 1 - m) * charPoly m := by
    rw [charPoly, Finset.mul_sum, ← Finset.sum_range_reflect
      (fun k => X ^ (lam + mu + 1 - k)) (m + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    rw [← pow_add, show lam + mu + 1 - (m + 1 - 1 - i) = lam + mu + 1 - m + i from by omega]
  -- ∑_{k=0}^m X^k = charPoly m, then factor.
  rw [hreidx, ← charPoly]
  ring

/-- **Clebsch–Gordan character identity (Problem 2.15.1(m)).**
The (shifted) character of `V_λ ⊗ V_μ` decomposes as the sum of the characters of
`V_{λ+μ−2k}`, `k = 0,…,min(λ,μ)`:
```
  charPoly λ · charPoly μ = Σ_{k=0}^{min(λ,μ)} X^k · charPoly (λ+μ−2k).
```
This is the polynomial form (`X = q²`, common factor `q^{−(λ+μ)}` cleared) of the
character identity `χ_{V_λ} · χ_{V_μ} = Σ_k χ_{V_{λ+μ−2k}}`, hence encodes the
decomposition `V_λ ⊗ V_μ ≅ ⨁_{k=0}^{min(λ,μ)} V_{λ+μ−2k}`. -/
theorem clebsch_gordan_charPoly (lam mu : ℕ) :
    charPoly lam * charPoly mu
      = ∑ k ∈ range (min lam mu + 1), X ^ k * charPoly (lam + mu - 2 * k) := by
  -- Multiply both sides by `(X−1)·(X−1)` (a nonzero divisor) and cancel.
  have key : charPoly lam * charPoly mu * ((X - 1) * (X - 1))
      = (∑ k ∈ range (min lam mu + 1), X ^ k * charPoly (lam + mu - 2 * k))
          * ((X - 1) * (X - 1)) := by
    have hL : charPoly lam * charPoly mu * ((X - 1) * (X - 1))
        = (X ^ (lam + 1) - 1) * (X ^ (mu + 1) - 1) := by
      calc charPoly lam * charPoly mu * ((X - 1) * (X - 1))
          = (charPoly lam * (X - 1)) * (charPoly mu * (X - 1)) := by ring
        _ = (X ^ (lam + 1) - 1) * (X ^ (mu + 1) - 1) := by
            rw [charPoly_mul_X_sub_one, charPoly_mul_X_sub_one]
    have hR : (∑ k ∈ range (min lam mu + 1), X ^ k * charPoly (lam + mu - 2 * k))
          * ((X - 1) * (X - 1))
        = (X ^ (min lam mu + 1) - 1) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
      rw [← mul_assoc, rhs_mul_X_sub_one]
      calc charPoly (min lam mu) * (X ^ (lam + mu + 1 - min lam mu) - 1) * (X - 1)
          = (charPoly (min lam mu) * (X - 1)) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
            ring
        _ = (X ^ (min lam mu + 1) - 1) * (X ^ (lam + mu + 1 - min lam mu) - 1) := by
            rw [charPoly_mul_X_sub_one]
    rw [hL, hR]
    rcases le_total lam mu with h | h
    · rw [min_eq_left h, show lam + mu + 1 - lam = mu + 1 from by omega]
    · rw [min_eq_right h, show lam + mu + 1 - mu = lam + 1 from by omega, mul_comm]
  exact mul_right_cancel₀ (mul_ne_zero X_sub_one_ne_zero X_sub_one_ne_zero) key

/-- `charPoly n` evaluated at `1` is `n + 1` (the dimension of `V_n`). -/
theorem charPoly_eval_one (n : ℕ) : (charPoly n).eval 1 = (n : ℤ) + 1 := by
  rw [charPoly, eval_finsetSum]
  simp [Finset.sum_const, Finset.card_range]

/-- **Clebsch–Gordan dimension count (Problem 2.15.1(m)).**
Specializing the character identity at `X = 1` gives the dimension identity
`(λ+1)(μ+1) = Σ_{k=0}^{min(λ,μ)} (λ+μ−2k+1)`, confirming that the irreducible
summands `V_{λ+μ−2k}` exhaust `V_λ ⊗ V_μ`. -/
theorem clebsch_gordan_dim (lam mu : ℕ) :
    ((lam : ℤ) + 1) * ((mu : ℤ) + 1)
      = ∑ k ∈ range (min lam mu + 1), (((lam + mu - 2 * k : ℕ) : ℤ) + 1) := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (clebsch_gordan_charPoly lam mu)
  rw [eval_mul, charPoly_eval_one, charPoly_eval_one, eval_finsetSum] at h
  simp only [eval_mul, eval_pow, eval_X, one_pow, charPoly_eval_one, one_mul] at h
  exact h

end Etingof.Sl2Irrep

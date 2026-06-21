import Mathlib

/-!
# Polynomials agreeing on `GL_N` are equal

`MvPolynomial.eq_of_eval_eq_on_gl` (two polynomials over an infinite field that
evaluate equally at every invertible matrix are equal — the Zariski-density of
`GL_N` in the matrix space) is now the upstream Mathlib lemma in
`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/MvPolynomial.lean`
(Mathlib PR https://github.com/leanprover-community/mathlib4/pull/38583).

This file retains the generic density primitive
`MvPolynomial.eq_zero_of_eval_eq_zero_off_zeroLocus`, which is not (yet)
upstream. It is kept in its own (Mathlib-only) file so that both the
polynomial-rep embedding (`PolynomialRepEmbedding`) and the `det⁻¹`-localization
stack (`DetLocalization` and downstream) can consume it without an import cycle:
the localization stack must sit *above* `PolynomialRepEmbedding` so that the
kernel lemma (#4694) can feed back into the embedding's
`detInv_elim_of_polynomial` (#4695).
-/

namespace MvPolynomial

/-- **Vanishing off the zero-locus of a nonzero polynomial forces vanishing
everywhere (Zariski-density engine).** Over an infinite integral domain, a
polynomial `P` that evaluates to `0` at every point where a *nonzero* polynomial
`Q` does not vanish is identically zero.

Proof: `P * Q` vanishes at every point — where `Q ≠ 0` we use the hypothesis on
`P`, and where `Q = 0` the product is `0` — so `P * Q = 0` as a polynomial by
`MvPolynomial.funext`. Since `MvPolynomial σ R` is a domain and `Q ≠ 0`, this
forces `P = 0`.

This is the generic form of the `(p - q) * det = 0` argument used in
`eq_of_eval_eq_on_gl` (there `Q` is the generic determinant). It is the density
primitive for "a regular function vanishing on a Zariski-dense set vanishes
everywhere": take `Q` cutting out the complement of the dense set (e.g.
`det · discr` for the distinct-eigenvalue locus in `GL_N`). -/
lemma eq_zero_of_eval_eq_zero_off_zeroLocus
    {σ R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {P Q : MvPolynomial σ R} (hQ : Q ≠ 0)
    (h : ∀ x : σ → R, MvPolynomial.eval x Q ≠ 0 → MvPolynomial.eval x P = 0) :
    P = 0 := by
  have hprod : P * Q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x Q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.mp hprod).resolve_right hQ

end MvPolynomial

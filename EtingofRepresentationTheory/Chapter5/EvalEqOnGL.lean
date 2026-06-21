import Mathlib

/-!
# Polynomials agreeing on `GL_N` are equal

`MvPolynomial.eq_of_eval_eq_on_gl`: over an infinite field, two polynomials in
`MvPolynomial (Fin N × Fin N) k` that evaluate equally at every invertible matrix
are equal. This is the Zariski-density of `GL_N` in the matrix space.

Relocated to its own (Mathlib-only) file so that both the polynomial-rep
embedding (`PolynomialRepEmbedding`) and the `det⁻¹`-localization stack
(`DetLocalization` and downstream) can consume it without an import cycle: the
localization stack must sit *above* `PolynomialRepEmbedding` so that the kernel
lemma (#4694) can feed back into the embedding's `detInv_elim_of_polynomial`
(#4695).
-/

namespace MvPolynomial

/-- **Polynomial-identity-from-GL-evaluation.** Two polynomials in
`MvPolynomial (Fin N × Fin N) k` over an infinite field agree as polynomials
whenever their evaluations agree at every invertible matrix.

Proof: consider `(p - q) * det(X)` where `det(X)` is the generic determinant
polynomial. At every square matrix `s : Fin N × Fin N → k`: if `det s ≠ 0`,
then `s` comes from a `GL_N`-element, so `eval s p = eval s q` by hypothesis;
if `det s = 0`, then `eval s (det X) = 0`. In either case the product
vanishes, so by `MvPolynomial.funext` the product is zero as a polynomial.
The determinant polynomial is nonzero by `Matrix.det_mvPolynomialX_ne_zero`,
and `MvPolynomial σ k` is an integral domain, so `p - q = 0`.

Upstream Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/38583
(once it merges, replace this lemma with the upstream `MvPolynomial.eq_of_eval_eq_on_gl`
and remove this local copy — see issue #2564). -/
lemma eq_of_eval_eq_on_gl
    {k : Type*} [Field k] [Infinite k] {N : ℕ}
    {p q : MvPolynomial (Fin N × Fin N) k}
    (h : ∀ g : Matrix.GeneralLinearGroup (Fin N) k,
           MvPolynomial.eval
             (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) p =
           MvPolynomial.eval
             (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) q) :
    p = q := by
  classical
  have hdet_ne : Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k) ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin N) k
  have hprod :
      (p - q) * Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k) = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul, map_sub, map_zero]
    have hdet_eval :
        MvPolynomial.eval s (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)) =
          Matrix.det (Matrix.of fun i j : Fin N => s (i, j)) := by
      rw [(MvPolynomial.eval s).map_det]
      congr 1
      ext i j
      simp [Matrix.mvPolynomialX]
    rw [hdet_eval]
    by_cases hdet_s :
        Matrix.det (Matrix.of fun i j : Fin N => s (i, j)) = 0
    · rw [hdet_s, mul_zero]
    · have hh := h (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (Matrix.of fun i j : Fin N => s (i, j)) hdet_s)
      have hs_eq :
          (fun ij : Fin N × Fin N =>
              (Matrix.GeneralLinearGroup.mkOfDetNeZero
                  (Matrix.of fun i j : Fin N => s (i, j)) hdet_s :
                Matrix (Fin N) (Fin N) k) ij.1 ij.2) = s := by
        funext ij
        rfl
      rw [hs_eq] at hh
      rw [hh, sub_self, zero_mul]
  have hpq_zero : p - q = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hdet_ne
  exact sub_eq_zero.mp hpq_zero

end MvPolynomial

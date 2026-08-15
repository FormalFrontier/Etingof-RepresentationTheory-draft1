/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib

namespace RepresentationTheory.MvPolynomial.Vanishing

/-- Over an infinite domain, a multivariate polynomial vanishing wherever a nonzero polynomial does not vanish is zero. -/
lemma eq_zero_of_eval_eq_zero_off_zero_locus
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

end RepresentationTheory.MvPolynomial.Vanishing

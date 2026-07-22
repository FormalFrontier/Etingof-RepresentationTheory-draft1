import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import EtingofRepresentationTheory.Chapter2.Corollary2_3_10

/-!
# Remark 2.3.11: Corollary 2.3.10 is false over the reals

Etingof remarks that Corollary 2.3.10 (Schur's lemma for algebraically closed fields: every
endomorphism of a finite-dimensional irreducible representation is a scalar) is **false** when
the base field is not algebraically closed. The explicit witness is `A = ℂ`, regarded as an
`ℝ`-algebra, and `V = A = ℂ`.

Over `ℝ`, the `ℂ`-module `ℂ` is irreducible (`ℂ` is a field, hence simple over itself) and
finite-dimensional (dimension `2` over `ℝ`). Its endomorphism ring as a `ℂ`-module is `ℂ`
itself, which is `2`-dimensional over `ℝ`. Multiplication by `i` is a `ℂ`-linear endomorphism
that is **not** a real scalar multiple of the identity, since `i ∉ ℝ`. This contradicts the
conclusion of Corollary 2.3.10, witnessing that the hypothesis `IsAlgClosed k` cannot be
dropped.

We record the failure in two forms:

* `Etingof.Remark_2_3_11_witness`: the concrete witness — multiplication by `i` on `ℂ` is a
  `ℂ`-linear endomorphism that is not of the form `c • id` for any real scalar `c`.
* `Etingof.Remark_2_3_11`: the statement of Corollary 2.3.10 with `k := ℝ` (every hypothesis
  except `IsAlgClosed`) is false.
-/

namespace Etingof

/-- The concrete witness for Remark 2.3.11: multiplication by `i` is a `ℂ`-linear endomorphism
of the irreducible `ℂ`-module `ℂ` that is not a real scalar operator. Here `ℂ` plays the role of
both the algebra `A` (over the non-algebraically-closed field `ℝ`) and the irreducible module
`V = A`. -/
theorem Remark_2_3_11_witness :
    ¬ ∃ c : ℝ, ∀ v : ℂ, (Complex.I • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) v = c • v := by
  rintro ⟨c, hc⟩
  have h1 := hc 1
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one,
    Complex.real_smul] at h1
  -- `h1 : Complex.I = ↑c * 1`, impossible since the imaginary parts disagree.
  have := congrArg Complex.im h1
  simp at this

/-- Remark 2.3.11: the statement of Corollary 2.3.10 is **false** over the field `ℝ`. That is,
once the hypothesis `IsAlgClosed k` is removed and `k := ℝ`, an endomorphism of a
finite-dimensional irreducible representation need not be a scalar. The witness is `A = ℂ`
(as an `ℝ`-algebra) and `V = A = ℂ`, with the non-scalar endomorphism being multiplication
by `i` (see `Etingof.Remark_2_3_11_witness`). -/
theorem Remark_2_3_11 :
    ¬ ∀ {A : Type} [Ring A] [Algebra ℝ A]
      {V : Type} [AddCommGroup V] [Module ℝ V] [Module A V] [IsScalarTower ℝ A V]
      [IsSimpleModule A V] [FiniteDimensional ℝ V]
      (φ : V →ₗ[A] V), ∃ c : ℝ, ∀ v : V, φ v = c • v := by
  intro h
  exact Remark_2_3_11_witness
    (h (A := ℂ) (V := ℂ) (φ := Complex.I • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)))

end Etingof

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Complex.Basic

/-!
# Remark 3.10.3: Failure of Theorem 3.10.2 for infinite dimensional representations

Theorem 3.10.2(i) states that if `V` is an irreducible finite dimensional representation
of `A` and `W` an irreducible finite dimensional representation of `B`, then `V ⊗ W` is an
irreducible representation of `A ⊗ B`. The finite dimensionality hypothesis is essential.

Etingof's Remark 3.10.3 gives an explicit counterexample: take
`A = B = V = W = ℂ(x)`, the field of rational functions. Each is irreducible as a module
over itself (a field has no nontrivial submodules), but part (i) fails because
`ℂ(x) ⊗_ℂ ℂ(x)` is **not** a field — so `V ⊗ W = ℂ(x) ⊗ ℂ(x)`, viewed as a module over
`A ⊗ B = ℂ(x) ⊗ ℂ(x)` itself, is not simple.

This file formalizes the core obstruction: `RatFunc ℂ ⊗[ℂ] RatFunc ℂ` is not a field.

## Proof strategy

The element `t := X ⊗ 1 - 1 ⊗ X` is nonzero but not a unit:

* **Not a unit.** The multiplication map `μ : ℂ(x) ⊗ ℂ(x) → ℂ(x)`, `a ⊗ b ↦ a * b`
  (`Algebra.TensorProduct.lmul'`), is a ring homomorphism sending `t` to `X - X = 0`.
  In a field every nonzero element is a unit, so if `t` were a unit `μ t = 0` would be a
  unit of `ℂ(x)` — impossible.

* **Nonzero.** The `ℂ`-algebra hom `Φ : ℂ(x) ⊗ ℂ(x) → ℂ(x)` built from the shift
  `f : X ↦ X + 1` on the left factor and the identity on the right sends `t` to
  `(X + 1) - X = 1 ≠ 0`, so `t ≠ 0`.
-/

open scoped TensorProduct
open Polynomial nonZeroDivisors

namespace EtingofRepresentationTheory.Chapter3.Remark3_10_3

noncomputable section

/-- `X + 1` is transcendental over `ℂ` inside `ℂ(x)`. -/
private lemma transcendental_X_add_one :
    Transcendental ℂ (RatFunc.X + 1 : RatFunc ℂ) := by
  have h : (RatFunc.X + 1 : RatFunc ℂ)
      = Polynomial.aeval (RatFunc.X : RatFunc ℂ) (Polynomial.X + 1 : ℂ[X]) := by
    simp
  rw [h]
  refine RatFunc.transcendental_X.aeval (Polynomial.X + 1 : ℂ[X]) ?_ ?_
  · rw [show (1 : ℂ[X]) = Polynomial.C 1 by simp, Polynomial.natDegree_X_add_C]
    exact one_ne_zero
  · rw [show (1 : ℂ[X]) = Polynomial.C 1 by simp, Polynomial.leadingCoeff_X_add_C]
    exact one_mem _

/-- The `ℂ`-algebra hom `ℂ[X] →ₐ[ℂ] ℂ(x)` sending `X` to `X + 1`. -/
private def φ : ℂ[X] →ₐ[ℂ] RatFunc ℂ := Polynomial.aeval (RatFunc.X + 1 : RatFunc ℂ)

private lemma hφ : (ℂ[X])⁰ ≤ (RatFunc ℂ)⁰.comap (φ : ℂ[X] →+* RatFunc ℂ) := by
  intro p hp
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  exact hp (transcendental_iff.mp transcendental_X_add_one p h)

/-- The shift automorphism `f : ℂ(x) →ₐ[ℂ] ℂ(x)`, `X ↦ X + 1`. -/
private def f : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ := RatFunc.liftAlgHom φ hφ

private lemma f_X : f (RatFunc.X : RatFunc ℂ) = RatFunc.X + 1 := by
  have h := RatFunc.liftAlgHom_apply_div φ hφ Polynomial.X 1
  simpa [f, φ, RatFunc.algebraMap_X] using h

/-- **Remark 3.10.3.** `ℂ(x) ⊗_ℂ ℂ(x)` is not a field: this is the obstruction to
Theorem 3.10.2(i) for infinite dimensional representations. -/
theorem ratFunc_tensor_ratFunc_not_isField :
    ¬ IsField (RatFunc ℂ ⊗[ℂ] RatFunc ℂ) := by
  intro hF
  set t : RatFunc ℂ ⊗[ℂ] RatFunc ℂ :=
    RatFunc.X ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] RatFunc.X with ht_def
  -- `Φ t = 1`, hence `t ≠ 0`.
  have hΦ :
      (Algebra.TensorProduct.lift f (AlgHom.id ℂ (RatFunc ℂ))
          (fun x y => Commute.all _ _)) t = 1 := by
    simp only [ht_def, map_sub, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one,
      f_X, mul_one, one_mul]
    ring
  have ht : t ≠ 0 := by
    intro h
    rw [h, map_zero] at hΦ
    exact one_ne_zero hΦ.symm
  -- `t` has an inverse in the supposed field.
  obtain ⟨s, hs⟩ := hF.mul_inv_cancel ht
  -- Applying the multiplication map `μ` gives `μ t * μ s = 1`, but `μ t = 0`.
  have hμt : Algebra.TensorProduct.lmul' (S := RatFunc ℂ) ℂ t = 0 := by
    simp [ht_def, map_sub, Algebra.TensorProduct.lmul'_apply_tmul]
  have hcontra := congrArg (Algebra.TensorProduct.lmul' (S := RatFunc ℂ) ℂ) hs
  rw [map_mul, map_one, hμt, zero_mul] at hcontra
  exact zero_ne_one hcontra

end

end EtingofRepresentationTheory.Chapter3.Remark3_10_3

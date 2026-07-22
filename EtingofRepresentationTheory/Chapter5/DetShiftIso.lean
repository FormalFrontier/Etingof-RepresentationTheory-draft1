import Mathlib
import EtingofRepresentationTheory.Chapter5.KernelLemmaKPrime

/-!
# The highest-weight shift isomorphism `det · A ≅ A ⊗ χ`

This file is **ingredient (2)** of the decomposition of the deep core
`kernelLemmaK'` (`Chapter5/KernelLemmaKPrime.lean`, route doc
`progress/kernel-lemma-K-route.md`, §"(K′) is the genuine representation-theoretic
core"). That core for `r ≥ 1` — every nonneg-weight right-`GL_N`-subrepresentation
of `(A/det) ⊗ χ⁻ʳ` is `⊥` — decomposes into two genuinely independent ingredients:

1. the `GL×GL`-equivariant **Cauchy decomposition** of `A = k[Xᵢⱼ]` (hard, far
   off, **not** attempted here), and
2. the **`det · A ≅ A ⊗ χ` highest-weight shift** (elementary, self-contained),
   formalized in this file.

The shift makes precise that multiplying by `detPoly = det(Xᵢⱼ)` carries the
right-translation representation `polyRightRep` twisted by the determinant
character `χ = detChar` *isomorphically* onto the principal ideal `(det)` inside
the untwisted `polyRightRep`. On highest weights this is the shift by `(1,…,1)`:
once the Cauchy half is available, it is what lets one read off that the
constituents of `A/det` have last highest-weight coordinate `ν_N = 0`.

## The objects

* `mulDet` — the `k`-linear multiplication-by-`detPoly` map `Q ↦ detPoly · Q`
  (`LinearMap.mulLeft k (detPoly k N)`).
* `detShiftSubrep` — the principal ideal `(det) = detSubmodule` packaged as a
  `Subrepresentation` of the untwisted right-translation rep `polyRightRep`
  (`(det)` is right-`GL_N`-stable: `polyRightRep_mem_detSubmodule`).
* `detShiftLinearEquiv` — the `k`-linear isomorphism `A ≃ₗ[k] ↥(det)` underlying
  the shift: `mulDet` is injective (`detPoly` is a nonzerodivisor) with range
  exactly `(det)`.

## The intertwining

* `mulDet_intertwine` — the entire mathematical content, immediate from the
  determinant semi-invariance `rTransAlgHom_det` (`R_g det = det(g)·det`):
  ```
  mulDet ((charTwistRep (detChar k N) (polyRightRep k N)) g Q)
    = polyRightRep k N g (mulDet Q).
  ```
  The `detChar` factor on the χ-twisted source cancels the `det(g)` that
  `R_g det` contributes on the right.
* `detShiftLinearEquiv_intertwine` — the same fact packaged at the level of the
  representation isomorphism `A ⊗ χ ≅ detShiftSubrep`.

## Consequence (for downstream wiring, not used here)

The short exact sequence of right-`GL_N`-modules
`0 → A ⊗ χ → A → A/det → 0` follows: `mulDet` is the injection (image `(det)`),
`Submodule.Quotient.mk` the surjection (cokernel `quotDetRep`, twist exponent
`0`). The **remaining** ingredient for `kernelLemmaK'` is the equivariant Cauchy
decomposition; wiring this shift into `kernelLemmaK'` is a separate follow-up that
also needs the Cauchy half, and is **not** done here.
-/

namespace Etingof.DetShiftIso

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
  Etingof.KernelLemmaKPrime

variable {k : Type*} [Field k] {N : ℕ}

/-! ### The multiplication-by-det map and its semi-invariance -/

/-- The right translation applied to the generic determinant `detPoly = det(Xᵢⱼ)`
is the determinant character times `detPoly` (`rTransAlgHom_det`, restated for the
`detPoly` spelling): `R_M detPoly = det(M) · detPoly`. -/
theorem rTransAlgHom_detPoly (M : Matrix (Fin N) (Fin N) k) :
    rTransAlgHom M (detPoly k N) = MvPolynomial.C M.det * detPoly k N :=
  rTransAlgHom_det M

/-- The **multiplication-by-det** `k`-linear map `mulDet : A →ₗ[k] A`,
`Q ↦ detPoly · Q`. Its image is the principal ideal `(det) = detSubmodule`, and
it intertwines the χ-twisted right-translation rep with the untwisted one
(`mulDet_intertwine`). -/
noncomputable def mulDet (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  LinearMap.mulLeft k (detPoly k N)

@[simp] theorem mulDet_apply (Q : MvPolynomial (Fin N × Fin N) k) :
    mulDet k N Q = detPoly k N * Q :=
  rfl

/-- **The equivariant shift, core computation.** `mulDet` intertwines the
right-translation rep `polyRightRep` twisted by the determinant character
`χ = detChar` with the *untwisted* `polyRightRep`:
`mulDet (χ(g) • R_g Q) = R_g (mulDet Q)`. This is immediate from the determinant
semi-invariance `R_g detPoly = det(g) · detPoly`: the `detChar` factor on the
source cancels the `det(g)` produced on the right. -/
theorem mulDet_intertwine (g : Matrix.GeneralLinearGroup (Fin N) k)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    mulDet k N (charTwistRep (detChar k N) (polyRightRep k N) g Q)
      = polyRightRep k N g (mulDet k N Q) := by
  have happ : ∀ f, polyRightRep k N g f = rTransAlgHom (↑g) f := fun _ => rfl
  have hdet : ((detChar k N g : kˣ) : k) = (↑g : Matrix (Fin N) (Fin N) k).det := by
    rw [detChar]; exact Matrix.GeneralLinearGroup.val_det_apply g
  simp only [mulDet_apply, charTwistRep_apply]
  rw [happ (detPoly k N * Q), map_mul, rTransAlgHom_detPoly, ← happ Q, hdet,
    MvPolynomial.smul_eq_C_mul]
  ring

/-! ### The shift isomorphism `det · A ≅ A ⊗ χ` -/

/-- `mulDet` is injective: `detPoly` is a nonzerodivisor (`A` is a domain). -/
theorem mulDet_injective : Function.Injective (mulDet k N) := by
  intro a b h
  exact mul_right_injective₀ detPoly_ne_zero (by simpa only [mulDet_apply] using h)

/-- The range of `mulDet` is exactly the determinant ideal `(det) = detSubmodule`:
`{detPoly · Q}` is the principal ideal `(detPoly)`. -/
theorem range_mulDet : LinearMap.range (mulDet k N) = detSubmodule k N := by
  ext x
  simp only [LinearMap.mem_range, mulDet_apply, detSubmodule, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨Q, rfl⟩; exact dvd_mul_right _ _
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩

/-- The principal ideal `(det) = detSubmodule` packaged as a **subrepresentation**
of the untwisted right-translation rep `polyRightRep`. `(det)` is right-`GL_N`-
stable (`polyRightRep_mem_detSubmodule`). -/
noncomputable def detShiftSubrep (k : Type*) [Field k] (N : ℕ) :
    Subrepresentation (polyRightRep k N) where
  toSubmodule := detSubmodule k N
  apply_mem_toSubmodule g _ hf := polyRightRep_mem_detSubmodule g hf

@[simp] theorem detShiftSubrep_toSubmodule :
    (detShiftSubrep k N).toSubmodule = detSubmodule k N :=
  rfl

/-- The **shift isomorphism** `A ≃ₗ[k] ↥(det)` underlying `det · A ≅ A ⊗ χ`:
`mulDet` is injective with range `(det)`. The `GL_N`-equivariance is recorded
separately in `detShiftLinearEquiv_intertwine`. -/
noncomputable def detShiftLinearEquiv (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) k ≃ₗ[k] ↥(detSubmodule k N) :=
  (LinearEquiv.ofInjective (mulDet k N) mulDet_injective).trans
    (LinearEquiv.ofEq _ _ range_mulDet)

@[simp] theorem detShiftLinearEquiv_coe (Q : MvPolynomial (Fin N × Fin N) k) :
    (detShiftLinearEquiv k N Q : MvPolynomial (Fin N × Fin N) k) = detPoly k N * Q := by
  simp only [detShiftLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply, mulDet_apply]

/-- **The shift isomorphism is `GL_N`-equivariant**: `detShiftLinearEquiv`
intertwines the χ-twisted source rep `A ⊗ χ = charTwistRep (detChar) (polyRightRep)`
with the subrepresentation `detShiftSubrep` carried by `(det)`. Together with
`detShiftLinearEquiv` being a `k`-linear isomorphism, this is the statement
`det · A ≅ A ⊗ χ` as right-`GL_N`-representations. -/
theorem detShiftLinearEquiv_intertwine (g : Matrix.GeneralLinearGroup (Fin N) k)
    (Q : MvPolynomial (Fin N × Fin N) k) :
    detShiftLinearEquiv k N (charTwistRep (detChar k N) (polyRightRep k N) g Q)
      = (detShiftSubrep k N).toRepresentation g (detShiftLinearEquiv k N Q) := by
  apply Subtype.ext
  change (detShiftLinearEquiv k N (charTwistRep (detChar k N) (polyRightRep k N) g Q)
        : MvPolynomial (Fin N × Fin N) k)
      = polyRightRep k N g (detShiftLinearEquiv k N Q)
  rw [detShiftLinearEquiv_coe, detShiftLinearEquiv_coe, ← mulDet_apply, ← mulDet_apply,
    mulDet_intertwine]

end Etingof.DetShiftIso

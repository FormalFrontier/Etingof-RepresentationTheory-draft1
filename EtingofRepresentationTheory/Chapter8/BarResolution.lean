import Mathlib

/-!
# The relative bar resolution of a representation of a `k`-algebra

For a field `k`, a `k`-algebra `A`, and a left `A`-module `W` (a representation of `A`), the
*relative* (`k`-split) **bar resolution** of `W` is the chain complex

`… → P₂ → P₁ → P₀ → W → 0`

with terms `Pₙ = A ⊗_k A^{⊗_k n} ⊗_k W`, the leading `A` factor carrying the left `A`-action,
augmentation `π : P₀ = A ⊗_k W → W`, `a ⊗ w ↦ a • w`, and the usual alternating-sum bar
differential.  Because `k` is a field every `A^{⊗n} ⊗_k W` is a free `k`-module, so each `Pₙ` is a
*free* `A`-module (`A ⊗_k (free k-module)`), hence projective.  This is what makes the relative
bar resolution an honest projective resolution over a field, and it is the missing piece needed to
compute `Ext_A` via `CategoryTheory.ProjectiveResolution.extAddEquivCohomologyClass` (see #6297,
consumed by `Problem_8_2_6_ii`).

## What is formalized here

This file provides the **terms** of the resolution as free/projective `A`-modules, together with
the **augmentation**:

* `Etingof.BarResolution.barCoeff k A W n` — the `k`-module `A^{⊗_k n} ⊗_k W` of bar coefficients.
* `Etingof.BarResolution.barModule k A W n = A ⊗_k (A^{⊗n} ⊗_k W)` — the `n`-th term, an
  `A`-module via left multiplication on the leading factor; a *free* `A`-module
  (`instance : Module.Free A (barModule …)`).
* `Etingof.BarResolution.barObj k A W n : ModuleCat A` — the term packaged as an object of
  `ModuleCat A`, with a `Projective` instance.
* `Etingof.BarResolution.ε k A W : barModule k A W 0 →ₗ[A] W` — the augmentation `a ⊗ w ↦ a • w`,
  proved surjective (`ε_surjective`); `barπ` is its packaging as a `ModuleCat` morphism.

The bar **differential**, the identity `d ∘ d = 0`, exactness via the `k`-linear contracting
homotopy `s(x) = 1 ⊗ x`, and the packaging into
`CategoryTheory.ProjectiveResolution (ModuleCat.of A W)` are follow-up work that builds on the
terms and augmentation defined here.
-/

universe u

namespace Etingof.BarResolution

open scoped TensorProduct
open CategoryTheory

variable (k A W : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

/-- The `k`-module of bar coefficients in degree `n`: `A^{⊗_k n} ⊗_k W`. -/
abbrev barCoeff (n : ℕ) : Type u := (⨂[k]^n A) ⊗[k] W

/-- The `n`-th term of the relative bar resolution, `Pₙ = A ⊗_k (A^{⊗n} ⊗_k W)`.

It is an `A`-module via left multiplication on the leading `A` factor (the
`TensorProduct.leftModule` instance), and — because `k` is a field, so `barCoeff k A W n` is a free
`k`-module — a *free* `A`-module. -/
abbrev barModule (n : ℕ) : Type u := A ⊗[k] barCoeff k A W n

/-- Each bar term is a free `A`-module: it is `A ⊗_k X` with `X` a free `k`-module. -/
instance instFreeBarModule (n : ℕ) : Module.Free A (barModule k A W n) :=
  inferInstanceAs (Module.Free A (A ⊗[k] barCoeff k A W n))

/-- Each bar term is a projective `A`-module (being free). -/
instance instProjectiveBarModule (n : ℕ) : Module.Projective A (barModule k A W n) :=
  inferInstance

/-- The `n`-th bar term packaged as an object of `ModuleCat A`. -/
noncomputable def barObj (n : ℕ) : ModuleCat.{u} A := ModuleCat.of A (barModule k A W n)

/-- Each bar term is projective as an object of `ModuleCat A`. -/
instance instProjectiveBarObj (n : ℕ) : Projective (barObj k A W n) :=
  inferInstanceAs (Projective (ModuleCat.of A (barModule k A W n)))

/-- The canonical `k`-linear identification `barCoeff k A W 0 = A^{⊗0} ⊗_k W ≃ₗ[k] W`
(the empty tensor power is `k`, and `k ⊗_k W ≃ W`). -/
noncomputable def barCoeffZeroEquiv : barCoeff k A W 0 ≃ₗ[k] W :=
  TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0)) (LinearEquiv.refl k W) ≪≫ₗ
    TensorProduct.lid k W

/-- The augmentation `ε : P₀ = A ⊗_k (A^{⊗0} ⊗_k W) →ₗ[A] W`, `a ⊗ (unit ⊗ w) ↦ a • w`.

It is `A`-linear via `TensorProduct.AlgebraTensorModule.lift` (valid for noncommutative `A`),
applied to the `k`-linear identification `barCoeff k A W 0 ≃ₗ[k] W`. -/
noncomputable def ε : barModule k A W 0 →ₗ[A] W :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton A (barCoeff k A W 0 →ₗ[k] W) (barCoeffZeroEquiv k A W).toLinearMap)

@[simp]
lemma ε_tmul (a : A) (c : barCoeff k A W 0) :
    ε k A W (a ⊗ₜ c) = a • barCoeffZeroEquiv k A W c := by
  simp [ε, LinearMap.toSpanSingleton_apply]

/-- The augmentation is surjective: `w = ε (1 ⊗ e⁻¹ w)`. -/
lemma ε_surjective : Function.Surjective (ε k A W) := by
  intro w
  refine ⟨(1 : A) ⊗ₜ (barCoeffZeroEquiv k A W).symm w, ?_⟩
  simp

/-- The augmentation packaged as a morphism `barObj k A W 0 ⟶ ModuleCat.of A W`. -/
noncomputable def barπ : barObj k A W 0 ⟶ ModuleCat.of A W :=
  ModuleCat.ofHom (ε k A W)

lemma barπ_surjective : Function.Surjective (barπ k A W) :=
  ε_surjective k A W

end Etingof.BarResolution

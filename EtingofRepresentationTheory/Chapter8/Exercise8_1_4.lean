import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Prod

/-!
# Exercise 8.1.4: Lifting maps along a short exact sequence

Let `A` be a ring, let `M₁, M₂` be left `A`-modules, let `P₁, P₂` be projective left
`A`-modules, and let `fᵢ : Pᵢ → Mᵢ` be homomorphisms. Let `M` be a left `A`-module containing
`M₁` such that `M / M₁ = M₂`. Show that there exists a homomorphism `f : P₁ ⊕ P₂ → M` such that
`f|_{P₁} = f₁` and the induced homomorphism `P₂ → M₂` is `f₂`.

## Formalization notes

"`M` contains `M₁` with `M / M₁ = M₂`" is a short exact sequence
`0 → M₁ →ᵢ M →ᵖ M₂ → 0`, encoded by an injective `ι : M₁ →ₗ[A] M`, a surjective
`π : M →ₗ[A] M₂`, and exactness in the middle (`range ι = ker π`).

The direct sum `P₁ ⊕ P₂` is the product module, with inclusions `LinearMap.inl` and
`LinearMap.inr`. The two conditions are:

* `f ∘ inl = ι ∘ f₁` (the restriction of `f` to `P₁` is `f₁`, viewed inside `M`);
* `π ∘ (f ∘ inr) = f₂` (the map `P₂ → M → M₂` induced by `f` is `f₂`).

This is a statement-level formalization (spec-first): the proof is deferred (`sorry`).
-/

namespace Etingof

/-- **Exercise 8.1.4.** Given a short exact sequence `0 → M₁ →ᵢ M →ᵖ M₂ → 0` of left
`A`-modules, projective modules `P₁, P₂`, and maps `fᵢ : Pᵢ → Mᵢ`, there is a map
`f : P₁ ⊕ P₂ → M` restricting to `f₁` on `P₁` and inducing `f₂` on `P₂`. -/
theorem Exercise_8_1_4 (A : Type*) [Ring A]
    (M₁ M₂ M : Type*)
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    [AddCommGroup M] [Module A M]
    (P₁ P₂ : Type*) [AddCommGroup P₁] [Module A P₁] [AddCommGroup P₂] [Module A P₂]
    [Module.Projective A P₁] [Module.Projective A P₂]
    (ι : M₁ →ₗ[A] M) (π : M →ₗ[A] M₂)
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hexact : LinearMap.range ι = LinearMap.ker π)
    (f₁ : P₁ →ₗ[A] M₁) (f₂ : P₂ →ₗ[A] M₂) :
    ∃ f : (P₁ × P₂) →ₗ[A] M,
      f.comp (LinearMap.inl A P₁ P₂) = ι.comp f₁ ∧
      π.comp (f.comp (LinearMap.inr A P₁ P₂)) = f₂ := by
  sorry

end Etingof

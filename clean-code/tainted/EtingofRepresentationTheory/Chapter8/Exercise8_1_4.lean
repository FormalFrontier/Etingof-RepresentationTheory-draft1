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

Proof: `P₂` projective lifts `f₂` through the surjection `π`,
and `f (p₁, p₂) = ι (f₁ p₁) + g₂ p₂` satisfies both conditions.
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
  -- `P₂` is projective and `π` is surjective, so lift `f₂ : P₂ → M₂` to `g₂ : P₂ → M`.
  obtain ⟨g₂, hg₂⟩ := Module.projective_lifting_property π f₂ hπ
  -- Assemble `f (p₁, p₂) = ι (f₁ p₁) + g₂ p₂`.
  refine ⟨(ι.comp f₁).comp (LinearMap.fst A P₁ P₂) + g₂.comp (LinearMap.snd A P₁ P₂), ?_, ?_⟩
  · -- On `(p₁, 0)` the `g₂ ∘ snd` term vanishes, leaving `ι (f₁ p₁)`.
    ext p₁
    simp
  · -- On `(0, p₂)` the `ι ∘ f₁ ∘ fst` term vanishes, leaving `π (g₂ p₂) = f₂ p₂`.
    ext p₂
    simpa using congrArg (fun h => h p₂) hg₂

end Etingof

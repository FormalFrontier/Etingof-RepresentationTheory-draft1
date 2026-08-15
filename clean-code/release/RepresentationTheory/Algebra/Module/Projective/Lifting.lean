/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Prod
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Algebra.Module.Projective.Lifting

/-- For an exact pair of linear maps and projective source modules, constructs a linear map from their direct sum with a prescribed restriction on the left summand and prescribed composite on the right summand. -/
@[source_ref "Chapter8/Exercise8.1.4" (role := primary)]
theorem LinearMap.exists_coprod_map_of_exact (A : Type*) [Ring A]
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
  obtain ⟨g₂, hg₂⟩ := Module.projective_lifting_property π f₂ hπ
  refine ⟨(ι.comp f₁).comp (LinearMap.fst A P₁ P₂) + g₂.comp (LinearMap.snd A P₁ P₂), ?_, ?_⟩
  · ext p₁
    simp
  · ext p₂
    simpa using congrArg (fun h => h p₂) hg₂

end RepresentationTheory.Algebra.Module.Projective.Lifting

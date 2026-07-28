import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Definition 2.3.6: Homomorphism (Intertwining Operator) of Representations

Let V₁, V₂ be two representations of an algebra A. A **homomorphism** (or
**intertwining operator**) φ : V₁ → V₂ is a linear operator which commutes with
the action of A, i.e., φ(av) = aφ(v) for any v ∈ V₁.

The set of all homomorphisms of representations V₁ → V₂ is denoted Hom_A(V₁, V₂).

## Mathlib correspondence

This is `LinearMap` (notation `V₁ →ₗ[A] V₂`), an A-module homomorphism.
-/

/-- A homomorphism of representations (intertwining operator),
in the sense of Etingof Definition 2.3.6.
This is `V₁ →ₗ[A] V₂` in Mathlib. -/
abbrev Etingof.RepresentationHom (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂] :=
  V₁ →ₗ[A] V₂

/-- An isomorphism of representations is an invertible `A`-linear map. Its inverse is again
`A`-linear, as witnessed by `LinearEquiv.symm`. -/
abbrev Etingof.RepresentationEquiv (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂] :=
  V₁ ≃ₗ[A] V₂

/-- Two representations are isomorphic when there exists an isomorphism between them. -/
abbrev Etingof.IsomorphicRepresentations (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂] : Prop :=
  Nonempty (Etingof.RepresentationEquiv A V₁ V₂)

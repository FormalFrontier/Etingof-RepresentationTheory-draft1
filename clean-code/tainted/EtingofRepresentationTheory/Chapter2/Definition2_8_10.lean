import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Definition 2.8.10: Homomorphism of Quiver Representations

A **homomorphism** of quiver representations (Vᵢ, xₕ) → (Wᵢ, yₕ) is a collection
of linear maps φᵢ : Vᵢ → Wᵢ such that yₕ ∘ φ_{h'} = φ_{h''} ∘ xₕ for every arrow h.

## Mathlib correspondence (partial)

These are natural transformations when viewing quiver representations as functors.
Mathlib has `NatTrans` but specific quiver representation morphism API is limited.
-/

/-- A homomorphism of quiver representations, in the sense of Etingof Definition 2.8.10.
A family of linear maps, one per vertex, that commute with the arrow maps. -/
structure Etingof.QuiverRepresentationHom (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q) where
  /-- The linear map at each vertex -/
  app : ∀ v, ρ₁.obj v →ₗ[k] ρ₂.obj v
  /-- The maps commute with the arrow maps -/
  naturality : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    app w (ρ₁.mapLinear e x) = ρ₂.mapLinear e (app v x)

/-- An equivalence (isomorphism) of quiver representations: a family of linear equivalences
at each vertex that commute with the arrow maps. This foundational placement makes the notion
available to constructions near Definition 2.8.10 without importing Gabriel's theorem. -/
structure Etingof.QuiverRepresentationEquiv (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] (ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q) where
  /-- A linear equivalence at each vertex. -/
  equivAt : ∀ v, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- The equivalences commute with the arrow maps. -/
  commutes : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    equivAt w (ρ₁.mapLinear e x) = ρ₂.mapLinear e (equivAt v x)

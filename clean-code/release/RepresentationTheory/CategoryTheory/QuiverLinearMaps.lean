/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import Mathlib.Algebra.Module.Equiv.Defs
import RepresentationTheory.Alignment.Attribute

/-! # Quiver linear maps -/

namespace RepresentationTheory.CategoryTheory.QuiverLinearMaps

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

/-- A vertexwise linear map between two quiver-indexed module systems. -/
@[source_ref "Chapter2/Definition2.8.10" (role := supporting)]
structure QuiverLinearHom (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] (ρ₁ ρ₂ : QuiverLinearDiagram k Q) where
  /-- Returns the linear map at a specified vertex. -/
  app : ∀ v, ρ₁.obj v →ₗ[k] ρ₂.obj v
  /-- The component maps of a quiver linear map commute with each arrow. -/
  naturality : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    app w (ρ₁.map e x) = ρ₂.map e (app v x)

/-- A vertexwise linear equivalence between two quiver-indexed module systems. -/
structure QuiverLinearEquiv (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] (ρ₁ ρ₂ : QuiverLinearDiagram k Q) where
  /-- Returns the linear equivalence at a chosen vertex. -/
  app : ∀ v, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- The component linear equivalences commute with each quiver arrow. -/
  naturality : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    app w (ρ₁.map e x) = ρ₂.map e (app v x)

end RepresentationTheory.CategoryTheory.QuiverLinearMaps

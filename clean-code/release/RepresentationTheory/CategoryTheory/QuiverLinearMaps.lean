/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import Mathlib.Algebra.Module.Equiv.Defs
import RepresentationTheory.Alignment.Attribute

/-! # Quiver linear maps -/

namespace RepresentationTheory.CategoryTheory.QuiverLinearMaps

/-- A second auxiliary data type associated with two objects over a quiver and a commutative semiring. -/
@[source_ref "Chapter2/Definition2.8.10" (role := supporting)]
structure AuxiliaryQuiverLinearMapData (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q]
    (ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) where
  /-- Returns the linear map at a specified vertex. -/
  app : ∀ v, ρ₁.obj v →ₗ[k] ρ₂.obj v
  /-- The component maps of a quiver linear map commute with each arrow. -/
  naturality : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    app w (ρ₁.map e x) = ρ₂.map e (app v x)

/-- Auxiliary data associated with two objects over a quiver and a commutative semiring. -/
structure AuxiliaryQuiverEquivData (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q]
    (ρ₁ ρ₂ : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) where
  /-- Returns the linear equivalence at a chosen vertex. -/
  app : ∀ v, ρ₁.obj v ≃ₗ[k] ρ₂.obj v
  /-- The component linear equivalences commute with each quiver arrow. -/
  naturality : ∀ {v w : Q} (e : v ⟶ w) (x : ρ₁.obj v),
    app w (ρ₁.map e x) = ρ₂.map e (app v x)

end RepresentationTheory.CategoryTheory.QuiverLinearMaps

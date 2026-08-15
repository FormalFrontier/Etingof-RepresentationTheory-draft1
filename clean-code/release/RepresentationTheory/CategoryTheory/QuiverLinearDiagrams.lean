/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Combinatorics.Quiver.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Quiver linear diagrams -/

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

/-- A quiver-indexed system of modules and linear maps. -/
@[source_ref "Chapter2/Definition2.8.3" (role := supporting),
  source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived2" (role := supporting)]
structure QuiverLinearDiagram (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] where
  /-- Returns the type assigned by a diagram to a vertex. -/
  obj : Q → Type*
  /-- Supplies the additive commutative monoid at a vertex of a diagram. -/
  {addCommMonoid : ∀ v, AddCommMonoid (obj v)}
  /-- Supplies the scalar module structure at a vertex of a diagram. -/
  {moduleInstance : ∀ v, Module k (obj v)}
  /-- Returns the linear map assigned to a quiver arrow. -/
  map : ∀ {v w : Q}, (v ⟶ w) → obj v →ₗ[k] obj w

attribute [instance] QuiverLinearDiagram.addCommMonoid
attribute [instance] QuiverLinearDiagram.moduleInstance

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

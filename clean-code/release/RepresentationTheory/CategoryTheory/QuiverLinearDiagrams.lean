/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Combinatorics.Quiver.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Quiver linear diagrams -/

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

/-- An auxiliary inductive type associated with a quiver over a commutative semiring. -/
@[source_ref "Chapter2/Definition2.8.3" (role := supporting),
  source_ref "Chapter2/Discussion_after_Theorem2.1.1/Derived2" (role := supporting)]
structure AuxiliaryQuiverModuleData (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] where
  /-- Returns the type associated with a vertex. -/
  obj : Q → Type*
  /-- Supplies the additive commutative monoid structure on the type at a vertex. -/
  {addCommMonoid : ∀ v, AddCommMonoid (obj v)}
  /-- Supplies the scalar module structure on the type at a vertex. -/
  {moduleInstance : ∀ v, Module k (obj v)}
  /-- Returns the linear map associated with a quiver arrow. -/
  map : ∀ {v w : Q}, (v ⟶ w) → obj v →ₗ[k] obj w

attribute [instance] AuxiliaryQuiverModuleData.addCommMonoid
attribute [instance] AuxiliaryQuiverModuleData.moduleInstance

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

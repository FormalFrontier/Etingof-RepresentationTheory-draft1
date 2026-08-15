/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Unitary representations -/

namespace RepresentationTheory.Group.UnitaryRepresentations

/-- A finite-dimensional complex inner-product representation of a group. -/
@[source_ref "Chapter4/Definition4.6.1" (role := primary)]
structure UnitaryRepresentation
    (G : Type*) [Group G]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] where
  /-- The representation associated to the displayed unitary representation. -/
  representation : Representation ℂ G V
  /-- The displayed group action preserves the inner product. -/
  inner_apply_eq : ∀ g : G, ∀ v w : V,
    @inner ℂ V _ (representation g v) (representation g w) = @inner ℂ V _ v w

noncomputable example (G : Type*) [Group G] (n : ℕ) :
    UnitaryRepresentation G (EuclideanSpace ℂ (Fin n)) where
  representation := 1
  inner_apply_eq g v w := by simp

end RepresentationTheory.Group.UnitaryRepresentations

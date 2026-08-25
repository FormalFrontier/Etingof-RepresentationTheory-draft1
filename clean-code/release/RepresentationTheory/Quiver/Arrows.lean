/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Combinatorics.Quiver.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Bundled quiver arrows -/

namespace RepresentationTheory.Quiver.Arrows

/-- The type of arrows in a quiver. -/
abbrev Arrow (Q : Type*) [Quiver Q] : Type _ :=
  Σ (source : Q) (target : Q), source ⟶ target

namespace Arrow

variable {Q : Type*} [Quiver Q]

/-- The source vertex of an arrow. -/
def source (h : Arrow Q) : Q := h.1

/-- The target vertex of an arrow. -/
def target (h : Arrow Q) : Q := h.2.1

/-- The morphism underlying an arrow. -/
def hom (h : Arrow Q) : source h ⟶ target h := h.2.2

/-- The source of the arrow built from a morphism is its domain. -/
@[simp] theorem source_mk {i j : Q} (h : i ⟶ j) : source ⟨i, j, h⟩ = i := rfl

/-- The target of the arrow built from a morphism is its codomain. -/
@[simp] theorem target_mk {i j : Q} (h : i ⟶ j) : target ⟨i, j, h⟩ = j := rfl

end Arrow

end RepresentationTheory.Quiver.Arrows

attribute [source_ref "Chapter2/Discussion_quiver_notation" (role := supporting)]
  RepresentationTheory.Quiver.Arrows.Arrow
  RepresentationTheory.Quiver.Arrows.Arrow.hom

attribute [source_ref "Chapter2/Discussion_quiver_notation" (role := primary)]
  RepresentationTheory.Quiver.Arrows.Arrow.source
  RepresentationTheory.Quiver.Arrows.Arrow.target

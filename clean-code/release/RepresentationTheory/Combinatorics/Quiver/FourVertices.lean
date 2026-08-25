/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Combinatorics.Quiver.Basic
import RepresentationTheory.Alignment.Attribute

/-! # A quiver on four vertices -/

namespace RepresentationTheory.Combinatorics.Quiver.FourVertices

/-- A quiver structure on the four-element type. -/
@[source_ref "Chapter2/Example2.8.2" (role := supporting)]
instance fourVertexQuiver : Quiver (Fin 4) where
  Hom a b :=
    if a = 0 ∧ b = 1 then Unit
    else if a = 2 ∧ b = 1 then Unit
    else if a = 3 ∧ b = 0 then Unit
    else Empty

namespace fourVertexQuiver

/-- The specified arrow from vertex zero to vertex one. -/
@[source_ref "Chapter2/Example2.8.2" (role := supporting)]
def arrow01 : (0 : Fin 4) ⟶ (1 : Fin 4) := by
  change (if (0 : Fin 4) = 0 ∧ (1 : Fin 4) = 1 then Unit else
    if (0 : Fin 4) = 2 ∧ (1 : Fin 4) = 1 then Unit else
    if (0 : Fin 4) = 3 ∧ (1 : Fin 4) = 0 then Unit else Empty)
  simpa using Unit.unit

/-- The specified arrow from vertex two to vertex one. -/
@[source_ref "Chapter2/Example2.8.2" (role := supporting)]
def arrow21 : (2 : Fin 4) ⟶ (1 : Fin 4) := by
  change (if (2 : Fin 4) = 0 ∧ (1 : Fin 4) = 1 then Unit else
    if (2 : Fin 4) = 2 ∧ (1 : Fin 4) = 1 then Unit else
    if (2 : Fin 4) = 3 ∧ (1 : Fin 4) = 0 then Unit else Empty)
  simpa using Unit.unit

/-- The specified arrow from vertex three to vertex zero. -/
@[source_ref "Chapter2/Example2.8.2" (role := supporting)]
def arrow30 : (3 : Fin 4) ⟶ (0 : Fin 4) := by
  change (if (3 : Fin 4) = 0 ∧ (0 : Fin 4) = 1 then Unit else
    if (3 : Fin 4) = 2 ∧ (0 : Fin 4) = 1 then Unit else
    if (3 : Fin 4) = 3 ∧ (0 : Fin 4) = 0 then Unit else Empty)
  simpa using Unit.unit

end fourVertexQuiver

attribute [nolint defsWithUnderscore]
  fourVertexQuiver.arrow01 fourVertexQuiver.arrow21 fourVertexQuiver.arrow30

end RepresentationTheory.Combinatorics.Quiver.FourVertices

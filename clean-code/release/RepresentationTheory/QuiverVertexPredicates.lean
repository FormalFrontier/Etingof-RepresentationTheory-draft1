/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Quiver Vertex Predicates

Auxiliary predicates on vertices of a quiver.
-/

/-- A property of a vertex in a quiver. -/
@[source_ref "Chapter6/Definition6.6.1" (role := supporting)]
def RepresentationTheory.QuiverVertexPredicates.vertexProperty
    (V : Type*) [Quiver V] (i : V) : Prop :=
  ∀ (j : V), IsEmpty (i ⟶ j)

/-- A condition on a vertex of a quiver. -/
@[source_ref "Chapter6/Definition6.6.1" (role := supporting)]
def RepresentationTheory.QuiverVertexPredicates.vertexCondition
    (V : Type*) [Quiver V] (i : V) : Prop :=
  ∀ (j : V), IsEmpty (j ⟶ i)

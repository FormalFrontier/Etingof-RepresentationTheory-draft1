import Mathlib

/-!
# Definition 6.6.1: Sink and Source Vertices

A **sink** is a vertex in a quiver where all edges connected to it point towards it
(no outgoing arrows). A **source** is a vertex in a quiver where all edges connected
to it point away from it (no incoming arrows).

## Mathlib correspondence

Mathlib has `Quiver` with `Hom : V → V → Sort*` giving arrow types between vertices.
Sink and source are not defined in Mathlib. We define them as predicates on vertices:
a sink has no outgoing arrows, a source has no incoming arrows.
-/

/-- A vertex `i` in a quiver is a **sink** if there are no arrows leaving `i`.
(Etingof Definition 6.6.1) -/
def Etingof.IsSink (V : Type*) [Quiver V] (i : V) : Prop :=
  ∀ (j : V), IsEmpty (i ⟶ j)

/-- A vertex `i` in a quiver is a **source** if there are no arrows entering `i`.
(Etingof Definition 6.6.1) -/
def Etingof.IsSource (V : Type*) [Quiver V] (i : V) : Prop :=
  ∀ (j : V), IsEmpty (j ⟶ i)

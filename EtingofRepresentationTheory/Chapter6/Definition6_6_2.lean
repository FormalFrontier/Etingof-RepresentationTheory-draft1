import Mathlib

/-!
# Definition 6.6.2: Reversed Quiver at a Vertex

Given a quiver Q and a sink (or source) vertex i, Q̄ᵢ is the quiver obtained from Q
by reversing all arrows pointing into i (for a sink) or pointing out of i (for a source).

## Mathlib correspondence

Mathlib has `Quiver.reverse` which reverses ALL edges, but not vertex-local reversal.
This requires a custom definition that selectively reverses edges at a single vertex.
-/

/-- The quiver obtained by reversing all arrows incident to vertex `i`.
For a sink, this reverses all incoming arrows; for a source, all outgoing arrows.
(Etingof Definition 6.6.2) -/
noncomputable def Etingof.reversedAtVertex
    (V : Type*) [DecidableEq V] [Quiver V] (i : V) : Quiver V :=
  sorry

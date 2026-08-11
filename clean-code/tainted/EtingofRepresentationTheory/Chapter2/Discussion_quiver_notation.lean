import Mathlib.Combinatorics.Quiver.Basic

/-!
# Quiver vertex and edge notation

The discussion after Example 2.8.2 denotes the vertex set by `I`, the edge set by `E`, and the
source and target of an edge `h` by `h'` and `h''`. In Lean the vertex type itself plays the role
of `I`; the sigma type below packages all arrows into the corresponding edge type `E`.
-/

namespace Etingof

/-- The type of all edges of a quiver, with both endpoints bundled. This is the book's `E`. -/
abbrev QuiverArrow (Q : Type*) [Quiver Q] : Type _ :=
  Σ (source : Q) (target : Q), source ⟶ target

namespace QuiverArrow

variable {Q : Type*} [Quiver Q]

/-- The source `h'` of a bundled quiver edge. -/
def src (h : QuiverArrow Q) : Q := h.1

/-- The target `h''` of a bundled quiver edge. -/
def tgt (h : QuiverArrow Q) : Q := h.2.1

/-- The arrow carried by a bundled edge, with its source and target exposed in the type. -/
def hom (h : QuiverArrow Q) : src h ⟶ tgt h := h.2.2

@[simp] theorem src_mk {i j : Q} (h : i ⟶ j) : src ⟨i, j, h⟩ = i := rfl

@[simp] theorem tgt_mk {i j : Q} (h : i ⟶ j) : tgt ⟨i, j, h⟩ = j := rfl

end QuiverArrow

end Etingof

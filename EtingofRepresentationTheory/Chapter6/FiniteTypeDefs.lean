import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs

/-!
# Finite Type Definitions for Quiver Representations

This file defines `AreIsomorphic` (isomorphism of quiver representations) and
`IsFiniteTypeQuiver` (finite representation type). These definitions live in their
own file so that the orbit-counting files can use them without an import cycle.

`IsFiniteTypeQuiver` is the book's literal definition (Etingof Problem 6.1.5):
an orientable graph with finitely many isomorphism classes of
(finite-dimensional) indecomposable representations for every orientation.
Recording orientability is essential: without it a matrix with a self-loop would
satisfy the universal clause vacuously, since no orientation of such a matrix
exists.
-/

section QuiverRepresentationIso

variable {k : Type*} [Field k] {n : ℕ} {Q : Quiver (Fin n)}

/-- Two quiver representations are isomorphic if there exist linear isomorphisms at
each vertex that intertwine the edge maps. -/
def Etingof.QuiverRepresentation.AreIsomorphic
    (V W : @Etingof.QuiverRepresentation k (Fin n) _ Q) : Prop :=
  ∃ (e : ∀ v, V.obj v ≃ₗ[k] W.obj v),
    ∀ {a b : Fin n} (f : a ⟶ b),
      (e b).toLinearMap ∘ₗ V.mapLinear f = W.mapLinear f ∘ₗ (e a).toLinearMap

end QuiverRepresentationIso

/-- A quiver on `n` vertices (with underlying graph given by adjacency matrix
`adj`) is of **finite type** if for every algebraically closed field `k` and
every orientation `Q` of the graph, there are only **finitely many isomorphism
classes of finite-dimensional indecomposable representations**.

We encode "finitely many iso classes" as the existence of a finite set `reps` of
indecomposable representatives such that every finite-dimensional indecomposable
is isomorphic (via `AreIsomorphic`) to one of them. This is the book's literal
definition (Etingof Problem 6.1.5) and the notion the orbit-counting argument
consumes. Uses `QuiverRepresentation.AreIsomorphic` and
`QuiverRepresentation.IsIndecomposable` (Proposition 6.6.5). -/
def Etingof.IsFiniteTypeQuiver (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∃ (Q : @Quiver.{0, 0} (Fin n)),
      (∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)) ∧
        @Etingof.IsOrientationOf n Q adj) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (Q : @Quiver.{0, 0} (Fin n))
      [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)],
      @Etingof.IsOrientationOf n Q adj →
        ∃ reps : Set (Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n)),
          reps.Finite ∧
          (∀ V ∈ reps, V.IsIndecomposable) ∧
          ∀ (W : Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n)),
            (∀ v, Module.Free k (W.obj v)) → (∀ v, Module.Finite k (W.obj v)) →
              W.IsIndecomposable → ∃ V ∈ reps, W.AreIsomorphic V

/-- A graph of finite representation type has no self-loops.  The explicit
orientation witness in `IsFiniteTypeQuiver` makes this source claim
nonvacuous. -/
theorem Etingof.IsFiniteTypeQuiver.no_self_loops {n : ℕ}
    {adj : Matrix (Fin n) (Fin n) ℤ} (hft : Etingof.IsFiniteTypeQuiver n adj)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1) : ∀ i, adj i i = 0 := by
  obtain ⟨Q, _, hQ⟩ := hft.1
  intro i
  rcases h01 i i with hii | hii
  · exact hii
  · exfalso
    rcases hQ.2.1 i i hii with hi | hi
    · exact hQ.2.2 i i hi hi
    · exact hQ.2.2 i i hi hi

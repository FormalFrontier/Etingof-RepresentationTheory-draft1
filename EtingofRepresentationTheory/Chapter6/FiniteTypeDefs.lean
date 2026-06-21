import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs

/-!
# Finite Type Definitions for Quiver Representations

This file defines `AreIsomorphic` (isomorphism of quiver representations) and
`IsFiniteTypeQuiver` (finite representation type), extracted from
`Problem6_1_5_theorem.lean` so that the orbit-counting files of directive #4777
can consume them without an import cycle.

`IsFiniteTypeQuiver` is the book's literal definition (Etingof Problem 6.1.5):
*finitely many isomorphism classes of (finite-dimensional) indecomposable
representations.* This is the notion the orbit-counting argument consumes, and
the only finite-type notion the project now uses: the old dimension-vector
auxiliary notion `IsFiniteTypeQuiverDimVec` was retired together with the
explicit-construction track (directive #4777).
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

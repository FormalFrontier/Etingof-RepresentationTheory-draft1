import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs

/-!
# Finite Type Definitions for Quiver Representations

This file defines `AreIsomorphic` (isomorphism of quiver representations) and
`IsFiniteTypeQuiver` (finite representation type). These are extracted from
`Problem6_1_5_theorem.lean` to break a circular import dependency with
`InfiniteTypeConstructions.lean`.

## The two finiteness notions

`IsFiniteTypeQuiver` is the book's literal definition (Etingof Problem 6.1.5):
*finitely many isomorphism classes of (finite-dimensional) indecomposable
representations.* This is the notion the orbit-counting argument (directive
#4777) consumes, so it is the canonical one.

`IsFiniteTypeQuiverDimVec` is the older, strictly weaker auxiliary notion: *the
set of dimension vectors supporting an indecomposable is finite.* The two are
**not** interchangeable — the orbit argument at a single dimension vector
produces infinitely many iso classes whose indecomposable summands share
finitely many dimension vectors, refuting the iso-class notion but not the
dimension-vector notion. `IsFiniteTypeQuiverDimVec` is retained only because the
(to-be-retired) explicit-construction track in `InfiniteTypeConstructions.lean`
and the `FieldGeneric*` files are stated against it.
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

/-- **Auxiliary (weaker) finiteness notion.** A quiver on `n` vertices (with
underlying graph given by adjacency matrix `adj`) is of *dimension-vector finite
type* if for every algebraically closed field `k` and every orientation `Q` of
the graph, the set of dimension vectors supporting an indecomposable
representation is finite.

This is implied by, but **not** equivalent to, the iso-class notion
`IsFiniteTypeQuiver`: infinitely many iso classes can share finitely many
dimension vectors. It is retained only for the explicit-construction track in
`InfiniteTypeConstructions.lean` and the `FieldGeneric*` files, which are slated
for retirement (directive #4777). Uses `QuiverRepresentation.IsIndecomposable`
from Proposition 6.6.5. -/
def Etingof.IsFiniteTypeQuiverDimVec (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)],
    @Etingof.IsOrientationOf n Q adj →
      Set.Finite
        {d : Fin n → ℕ |
          ∃ (V : Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n)),
            V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[k] (Fin (d v) → k))}

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

import Mathlib
import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Chapter6.ReflectionFunctorInfrastructure

/-!
# Theorem (Problem 6.1.5): Finite Type iff Dynkin

A connected quiver Q is of finite type if and only if the corresponding unoriented
graph (i.e., with directions of arrows forgotten) is a Dynkin diagram
(see Theorem 6.5.2 / Gabriel's theorem).

## Mathlib correspondence

Gabriel's theorem is NOT in Mathlib. Quiver representations have basic support
(`Quiver`, `Representation`), but Gabriel's classification is absent.
The definition of "finite type" for quivers requires quiver representation theory
infrastructure (indecomposable representations, isomorphism classes) not yet
available in Mathlib.

## Formalization note

The statement uses `IsDynkinDiagram` (Definition 6.1.4) for the combinatorial
condition. The representation-theoretic side (`IsFiniteTypeQuiver`) is defined using
`QuiverRepresentation`, `IsIndecomposable`, and `Iso` from the project's quiver
representation infrastructure.
The hypotheses unpack the connected simple graph conditions.
-/

/-- A quiver on n vertices (with underlying graph given by adjacency matrix adj) is of
**finite type** if for every algebraically closed field k and every orientation Q of the
underlying graph, the set of isomorphism classes of finite-dimensional indecomposable
k-representations of Q is finite.

Concretely: there exists a finite collection of indecomposables such that every
indecomposable representation is isomorphic to one of them. -/
def Etingof.IsFiniteTypeQuiver (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (Q : Quiver.{0} (Fin n)) (_hQ : @Etingof.IsOrientationOf n Q adj),
    ∃ (m : ℕ) (reps : Fin m → @Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n) _ Q),
      (∀ i, (reps i).IsIndecomposable) ∧
      ∀ (ρ : @Etingof.QuiverRepresentation.{0, 0, 0, 0} k (Fin n) _ Q),
        (∀ v, Module.Free k (ρ.obj v)) →
        (∀ v, Module.Finite k (ρ.obj v)) →
        ρ.IsIndecomposable →
        ∃ i, Nonempty (Etingof.QuiverRepresentation.Iso ρ (reps i))

/-- Gabriel's theorem: a connected quiver (given by its symmetric adjacency matrix)
is of finite type (finitely many indecomposable representations up to isomorphism)
if and only if its underlying unoriented graph is a Dynkin diagram.
(Etingof Problem 6.1.5 / Theorem 6.5.2) -/
theorem Etingof.Theorem_6_1_5 (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : ∀ i j : Fin n, ∃ path : List (Fin n),
      path.head? = some i ∧ path.getLast? = some j ∧
      ∀ k, (h : k + 1 < path.length) →
        adj (path.get ⟨k, by omega⟩) (path.get ⟨k + 1, h⟩) = 1) :
    Etingof.IsFiniteTypeQuiver n adj ↔ Etingof.IsDynkinDiagram n adj := sorry

import EtingofRepresentationTheory.Chapter2.Definition2_8_8
import EtingofRepresentationTheory.Chapter2.Definition2_8_9
import EtingofRepresentationTheory.Chapter2.Definition2_8_10

/-!
# Irreducible and indecomposable quiver representations

The discussion after Definition 2.8.9 carries the familiar notions from algebra representations
to quiver representations. The definitions below include the book's nonzero condition explicitly.
-/

namespace Etingof

universe u v w q

namespace QuiverSubrepresentation

variable {k : Type u} {Q : Type v} [CommSemiring k] [Quiver.{w} Q]
variable {ρ : QuiverRepresentation.{u, v, q, w} k Q}

/-- The zero subrepresentation `(0)`. -/
noncomputable def bot (ρ : QuiverRepresentation.{u, v, q, w} k Q) :
    QuiverSubrepresentation k Q ρ where
  carrier := fun _ => ⊥
  map_mem := by simp

/-- The full subrepresentation `(V_i)`. -/
noncomputable def top (ρ : QuiverRepresentation.{u, v, q, w} k Q) :
    QuiverSubrepresentation k Q ρ where
  carrier := fun _ => ⊤
  map_mem := by simp

/-- A subrepresentation is zero when every one of its vertex subspaces is zero. -/
def BookIsZero (S : QuiverSubrepresentation k Q ρ) : Prop :=
  ∀ i, S.carrier i = ⊥

/-- A subrepresentation is the whole representation when every vertex subspace is full. -/
def BookIsFull (S : QuiverSubrepresentation k Q ρ) : Prop :=
  ∀ i, S.carrier i = ⊤

theorem bot_bookIsZero : BookIsZero (bot ρ) := fun _ => rfl

theorem top_bookIsFull : BookIsFull (top ρ) := fun _ => rfl

end QuiverSubrepresentation

namespace QuiverRepresentation

variable {k : Type u} {Q : Type v} [CommSemiring k] [Quiver.{w} Q]

/-- A quiver representation is zero when every vector in every vertex space is zero. -/
def BookIsZero (ρ : QuiverRepresentation.{u, v, q, w} k Q) : Prop :=
  ∀ (i : Q) (x : ρ.obj i), x = 0

/-- A quiver representation is nonzero when at least one vertex space has a nonzero vector. -/
def BookIsNonzero (ρ : QuiverRepresentation.{u, v, q, w} k Q) : Prop :=
  ¬BookIsZero ρ

/-- A nonzero quiver representation is **irreducible** when its only subrepresentations are the
zero and full subrepresentations. -/
def BookIsIrreducible (ρ : QuiverRepresentation.{u, v, q, w} k Q) : Prop :=
  BookIsNonzero ρ ∧ ∀ S : QuiverSubrepresentation k Q ρ,
    S.BookIsZero ∨ S.BookIsFull

/-- A nonzero quiver representation is **indecomposable** when any isomorphism with a direct sum
has a zero summand; equivalently, it is not isomorphic to a direct sum of two nonzero
representations. -/
def BookIsIndecomposable (ρ : QuiverRepresentation.{u, v, q, w} k Q) : Prop :=
  BookIsNonzero ρ ∧ ∀ (ρ₁ ρ₂ : QuiverRepresentation.{u, v, q, w} k Q),
    QuiverRepresentationEquiv k Q ρ (directSum k Q ρ₁ ρ₂) →
      BookIsZero ρ₁ ∨ BookIsZero ρ₂

end QuiverRepresentation

end Etingof

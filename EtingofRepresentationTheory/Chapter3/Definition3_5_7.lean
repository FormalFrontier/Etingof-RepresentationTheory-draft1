import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import EtingofRepresentationTheory.Chapter3.Definition3_5_1

/-!
# Definition 3.5.7: Semisimple Algebra

A finite dimensional algebra A is said to be **semisimple** if Rad(A) = 0.

## Mathlib correspondence

We use the book's definition literally. For an Artinian ring—and hence for a
finite-dimensional algebra—Mathlib proves that vanishing of the Jacobson radical
is equivalent to `IsSemisimpleRing A`.
-/

/-- A semisimple algebra in the sense of Etingof Definition 3.5.7: a finite-dimensional
algebra whose radical vanishes. -/
abbrev Etingof.IsSemisimpleAlgebra (k A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] :=
  Etingof.Radical A = ⊥

/-- Mathlib-sem simplicity implies the book's radical-vanishing condition. The implication
itself does not use Artinianity; that instance is present because it is part of the book
predicate's domain. -/
theorem Etingof.isSemisimpleAlgebra_of_isSemisimpleRing (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] (h : IsSemisimpleRing A) :
    Etingof.IsSemisimpleAlgebra k A := by
  rw [Etingof.IsSemisimpleAlgebra, Etingof.Radical, Ideal.jacobson_bot]
  exact h.jacobson_eq_bot

/-- The book's radical-vanishing condition implies Mathlib-sem simplicity for an Artinian
ring. -/
theorem Etingof.IsSemisimpleAlgebra.isSemisimpleRing {k A : Type*} [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] (h : Etingof.IsSemisimpleAlgebra k A) :
    IsSemisimpleRing A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  rw [Etingof.IsSemisimpleAlgebra, Etingof.Radical, Ideal.jacobson_bot,
    ← IsArtinianRing.isSemisimpleRing_iff_jacobson] at h
  exact h

/-- For an Artinian ring, the book's radical-vanishing definition is equivalent to
Mathlib's module-theoretic notion of a semisimple ring. -/
theorem Etingof.isSemisimpleAlgebra_iff_isSemisimpleRing (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] :
    Etingof.IsSemisimpleAlgebra k A ↔ IsSemisimpleRing A :=
  ⟨Etingof.IsSemisimpleAlgebra.isSemisimpleRing,
    Etingof.isSemisimpleAlgebra_of_isSemisimpleRing k A⟩

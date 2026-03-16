import Mathlib.RingTheory.Idempotents

/-!
# Definition 9.1.2: Complete system of orthogonal idempotents

A collection of elements e₁, …, eₙ in a unital algebra B is said to be a **complete
system of orthogonal idempotents** if eᵢeⱼ = δᵢⱼeᵢ (i.e., the eᵢ are pairwise orthogonal
idempotents) and ∑ eᵢ = 1.

## Mathlib correspondence

Mathlib has `OrthogonalIdempotents` and `CompleteOrthogonalIdempotents` in
`Mathlib.RingTheory.Idempotents`. `CompleteOrthogonalIdempotents` requires a `Fintype` index
and bundles the conditions that elements are pairwise orthogonal idempotents summing to 1.
-/

/-- A complete system of orthogonal idempotents in the sense of Etingof Definition 9.1.2.
This is `CompleteOrthogonalIdempotents` in Mathlib. -/
abbrev Etingof.IsCompleteOrthogonalIdempotents {B : Type*} [Ring B] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι → B) : Prop :=
  CompleteOrthogonalIdempotents e

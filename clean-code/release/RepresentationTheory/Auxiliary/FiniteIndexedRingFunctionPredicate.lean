import Mathlib.RingTheory.Idempotents

namespace RepresentationTheory.Auxiliary.FiniteIndexedRingFunctionPredicate

/-- An auxiliary predicate on functions from a finite decidable index type to a ring. -/
abbrev isFiniteIndexedRingFunctionAuxiliary {B : Type*} [Ring B] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι → B) : Prop :=
  CompleteOrthogonalIdempotents e

end RepresentationTheory.Auxiliary.FiniteIndexedRingFunctionPredicate

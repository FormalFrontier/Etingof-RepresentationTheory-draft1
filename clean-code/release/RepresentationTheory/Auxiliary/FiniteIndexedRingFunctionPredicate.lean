/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.Idempotents

namespace RepresentationTheory.Auxiliary.FiniteIndexedRingFunctionPredicate

/-- An auxiliary predicate on functions from a finite decidable index type to a ring. -/
abbrev isFiniteIndexedRingFunctionAuxiliary {B : Type*} [Ring B] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : ι → B) : Prop :=
  CompleteOrthogonalIdempotents e

end RepresentationTheory.Auxiliary.FiniteIndexedRingFunctionPredicate

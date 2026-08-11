/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Basic

/-! # Predicates for Lie modules -/

namespace RepresentationTheory.Algebra.Lie.Module.Predicates

/-- An auxiliary predicate for an additive group equipped with scalar and Lie-ring module
structures. -/
abbrev LieModule.AuxiliaryPredicate (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L] [AddCommGroup V] [Module k V]
    [LieRingModule L V] :=
  LieModule k L V

end RepresentationTheory.Algebra.Lie.Module.Predicates

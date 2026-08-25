/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Predicates for Lie modules -/

namespace RepresentationTheory.Algebra.Lie.Module.Predicates

/-- An auxiliary predicate for an additive group equipped with scalar and Lie-ring module
structures. -/
@[source_ref "Chapter2/Definition2.9.7" (role := supporting)]
abbrev LieModule.AuxiliaryPredicate (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L] [AddCommGroup V] [Module k V]
    [LieRingModule L V] :=
  LieModule k L V

end RepresentationTheory.Algebra.Lie.Module.Predicates

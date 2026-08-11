/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.UniversalEnveloping

/-! # Types associated to Lie algebras -/

namespace RepresentationTheory.Algebra.Lie.AssociatedTypes

/-- An auxiliary type depending on a Lie algebra over a commutative ring. -/
abbrev LieAlgebra.AuxiliaryType (k : Type*) (L : Type*) [CommRing k]
    [LieRing L] [LieAlgebra k L] :=
  UniversalEnvelopingAlgebra k L

end RepresentationTheory.Algebra.Lie.AssociatedTypes

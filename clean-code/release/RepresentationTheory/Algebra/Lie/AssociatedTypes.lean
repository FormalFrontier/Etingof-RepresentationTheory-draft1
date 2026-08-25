/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.UniversalEnveloping
import RepresentationTheory.Alignment.Attribute

/-! # Types associated to Lie algebras -/

namespace RepresentationTheory.Algebra.Lie.AssociatedTypes

/-- An auxiliary type depending on a Lie algebra over a commutative ring. -/
@[source_ref "Chapter2/Definition2.9.9/Derived2" (role := supporting)]
abbrev LieAlgebra.AuxiliaryType (k : Type*) (L : Type*) [CommRing k]
    [LieRing L] [LieAlgebra k L] :=
  UniversalEnvelopingAlgebra k L

end RepresentationTheory.Algebra.Lie.AssociatedTypes

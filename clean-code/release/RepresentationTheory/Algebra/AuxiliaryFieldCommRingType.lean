/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Algebras with commutative carriers

Basic names for algebra structures on commutative rings over fields.
-/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.AuxiliaryFieldCommRingType

/-- An auxiliary type depending on a field and a commutative ring. -/
@[source_ref "Chapter2/Definition2.2.5" (role := primary)]
abbrev AuxiliaryFieldCommRingType (k : Type*) (A : Type*) [Field k] [CommRing A] :=
  Algebra k A

end RepresentationTheory.Algebra.AuxiliaryFieldCommRingType

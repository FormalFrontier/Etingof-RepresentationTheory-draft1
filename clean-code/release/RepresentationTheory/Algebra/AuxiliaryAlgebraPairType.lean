/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Hom
import RepresentationTheory.Alignment.Attribute

/-!
# Maps between a pair of algebras

Basic names for homomorphisms between two algebras over a common base ring.
-/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.AuxiliaryAlgebraPairType

/-- An auxiliary type depending on two algebras over a commutative ring. -/
@[source_ref "Chapter2/Definition2.2.6" (role := supporting)]
abbrev AuxiliaryAlgebraPairType (k : Type*) (A B : Type*) [CommRing k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] :=
  A →ₐ[k] B

end RepresentationTheory.Algebra.AuxiliaryAlgebraPairType

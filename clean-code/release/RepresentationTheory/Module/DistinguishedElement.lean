/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.DesignatedElements
import RepresentationTheory.Alignment.Attribute

/-! # Distinguished elements -/

namespace RepresentationTheory.Module.DistinguishedElement

/-- Any two elements satisfying the displayed distinguished-element predicate are equal. -/
@[source_ref "Chapter2/Proposition2.2.3" (role := primary)]
theorem distinguishedElement_unique (k : Type*) {A : Type*} [Field k] [AddCommGroup A]
    [Module k A]
    [RepresentationTheory.Algebra.NonUnitalStructure.NonUnitalAlgebraStructure k A]
    {e e' : A}
    (he : RepresentationTheory.Algebra.NonUnitalStructure.NonUnitalAlgebraStructure.DesignatedElement
      k e)
    (he' : RepresentationTheory.Algebra.NonUnitalStructure.NonUnitalAlgebraStructure.DesignatedElement
      k e') : e = e' :=
  RepresentationTheory.Algebra.NonUnitalStructure.NonUnitalAlgebraStructure.DesignatedElement.eq
    k he he'

end RepresentationTheory.Module.DistinguishedElement

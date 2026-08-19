/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.AuxiliaryPredicates

/-! # Distinguished elements -/

namespace RepresentationTheory.Module.DistinguishedElement

/-- Any two elements satisfying the displayed distinguished-element predicate are equal. -/
theorem distinguishedElement_unique (k : Type*) {A : Type*} [Field k] [AddCommGroup A]
    [Module k A]
    [RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure k A]
    {e e' : A}
    (he : RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure.auxiliaryPredicate
      k e)
    (he' : RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure.auxiliaryPredicate
      k e') : e = e' :=
  RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure.auxiliaryPredicate_unique
    k he he'

end RepresentationTheory.Module.DistinguishedElement

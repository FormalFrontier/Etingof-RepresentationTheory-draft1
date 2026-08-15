/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import RepresentationTheory.Algebra.NonUnitalStructure

/-!
# Designated identity elements

Two-sided identity elements for an associative bilinear multiplication.
-/

set_option linter.style.whitespace false

namespace RepresentationTheory.Algebra.NonUnitalStructure.NonUnitalAlgebraStructure

variable (k : Type*) {A : Type*} [Field k] [AddCommGroup A] [Module k A]
  [inst : NonUnitalAlgebraStructure k A]

/-- A predicate on elements of a vector space equipped with an associative bilinear multiplication
structure. -/
@[source_ref "Chapter2/Definition2.2.2" (role := primary),
  source_ref "Chapter2/Discussion_2.1_overview/Derived2" (role := supporting)]
def DesignatedElement (e : A) : Prop :=
  ∀ a : A, inst.mul e a = a ∧ inst.mul a e = a

namespace DesignatedElement

/-- Any two elements satisfying the designated-element predicate are equal. -/
theorem eq {e e' : A} (he : DesignatedElement k e) (he' : DesignatedElement k e') : e = e' := by
  have h1 := (he' e).2
  have h2 := (he e').1
  exact h1.symm.trans h2

end DesignatedElement
end RepresentationTheory.Algebra.NonUnitalStructure.NonUnitalAlgebraStructure

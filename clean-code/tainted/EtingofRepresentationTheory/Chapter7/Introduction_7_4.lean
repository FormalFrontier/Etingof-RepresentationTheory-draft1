import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.IsoCat
import EtingofRepresentationTheory.Chapter7.Discussion_after_Definition7_4_1

/-!
# Introduction to Section 7.4: `C₁` and `C₂` are "the same for all practical purposes"

The text motivates the notion of *equivalence* (rather than isomorphism) of
categories with the two toy categories `C₁` (one object, only its identity) and
`C₂` (two objects with a unique isomorphism between them, defined in
`Discussion_after_Definition7_4_1`). It observes:

> For any category `D`, there is a natural bijection between the collections of
> isomorphism classes of functors `C₁ → D` and `C₂ → D` (both are identified with
> the collection of isomorphism classes of objects of `D`).

This is the precise sense in which `C₁` and `C₂` are "the same for all practical
purposes", even though they are not isomorphic.

## Formalization

Isomorphism classes of objects of a category `A` are `Quotient (isIsomorphicSetoid A)`,
where `IsIsomorphic X Y := Nonempty (X ≅ Y)` (Mathlib's `CategoryTheory.IsIsomorphic`).
We show:

* `isoClassesEquivOfEquivalence`: any equivalence of categories `A ≌ B` descends to a
  bijection of isomorphism classes of objects.
* `functorIsoClassesEquiv`: applying this to the equivalence `C₁ ≌ C₂` precomposed into
  the functor category (`Equivalence.congrLeft`) gives the natural bijection between
  isomorphism classes of functors `C₁ → D` and `C₂ → D`.

The text stresses that this bijection is the sense in which `C₁` and `C₂` are "the same",
*even though* they are not isomorphic as categories: a strict isomorphism of categories
would require a bijection between their object types, which is impossible since `C₁` has one
object and `C₂` has two. Mathlib's strict (on-the-nose) notion of isomorphism of categories
is `CategoryTheory.IsoCat`. We record the negative claim:

* `isEmpty_isoCat_cat₁_cat₂`: there is no `IsoCat Cat₁ Cat₂`, i.e. `C₁` and `C₂` are *not*
  isomorphic as categories.
-/

open CategoryTheory

attribute [local instance] CategoryTheory.isIsomorphicSetoid

namespace Etingof

/-- An equivalence of categories `e : A ≌ B` induces a bijection between the
isomorphism classes of objects of `A` and of `B`. -/
def isoClassesEquivOfEquivalence {A B : Type*} [Category A] [Category B] (e : A ≌ B) :
    Quotient (isIsomorphicSetoid A) ≃ Quotient (isIsomorphicSetoid B) where
  toFun := Quotient.map e.functor.obj (fun _ _ ⟨f⟩ => ⟨e.functor.mapIso f⟩)
  invFun := Quotient.map e.inverse.obj (fun _ _ ⟨f⟩ => ⟨e.inverse.mapIso f⟩)
  left_inv := Quotient.ind fun X => Quotient.sound ⟨(e.unitIso.app X).symm⟩
  right_inv := Quotient.ind fun Y => Quotient.sound ⟨e.counitIso.app Y⟩

/-- Introduction to Section 7.4: for any category `D`, there is a natural bijection
between the isomorphism classes of functors `C₁ → D` and the isomorphism classes of
functors `C₂ → D`, induced by the equivalence `C₁ ≌ C₂`. This is the precise sense in
which `C₁` and `C₂` are "the same for all practical purposes". -/
def functorIsoClassesEquiv (D : Type*) [Category D] :
    Quotient (isIsomorphicSetoid (Cat₁ ⥤ D)) ≃ Quotient (isIsomorphicSetoid (Cat₂ ⥤ D)) :=
  isoClassesEquivOfEquivalence (cat₁EquivCat₂.congrLeft (E := D))

/-- Introduction to Section 7.4: although `C₁` and `C₂` are equivalent (`cat₁EquivCat₂`) and
have the "same" functor-isomorphism classes into any `D` (`functorIsoClassesEquiv`), they are
**not isomorphic as categories**. A strict isomorphism of categories (`CategoryTheory.IsoCat`)
has a forward functor that is bijective on objects, hence would give a bijection `Cat₁ ≃ Cat₂`;
but `Cat₁` (one object) is a subsingleton while `Cat₂` (two objects) is not. This is the
contrast between equivalence and the naive strict notion of isomorphism the text draws. -/
theorem isEmpty_isoCat_cat₁_cat₂ : IsEmpty (IsoCat Cat₁ Cat₂) := by
  refine ⟨fun e => ?_⟩
  -- The forward functor of an isomorphism of categories is bijective on objects, so it
  -- induces an equivalence of object types `Cat₁ ≃ Cat₂`, i.e. `PUnit ≃ Bool`.
  let f : PUnit ≃ Bool := e.functor.objEquiv
  -- `PUnit` is a subsingleton, so `f.symm` collapses `true` and `false`; injectivity of
  -- `f.symm` then forces `true = false`, a contradiction.
  have : (true : Bool) = false :=
    f.symm.injective (Subsingleton.elim (f.symm true) (f.symm false))
  exact absurd this (by decide)

end Etingof

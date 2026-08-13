import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.IsoCat
import RepresentationTheory.AbstractTypeEquivalence

open CategoryTheory

attribute [local instance] CategoryTheory.isIsomorphicSetoid

namespace RepresentationTheory.CategoryTheory.IsomorphismClasses

/-- Transports isomorphism classes of objects along a categorical equivalence. -/
def Equivalence.isomorphismClassesEquiv {A B : Type*} [Category A] [Category B]
    (e : A ≌ B) :
    Quotient (isIsomorphicSetoid A) ≃ Quotient (isIsomorphicSetoid B) where
  toFun := Quotient.map e.functor.obj (fun _ _ ⟨f⟩ => ⟨e.functor.mapIso f⟩)
  invFun := Quotient.map e.inverse.obj (fun _ _ ⟨f⟩ => ⟨e.inverse.mapIso f⟩)
  left_inv := Quotient.ind fun X => Quotient.sound ⟨(e.unitIso.app X).symm⟩
  right_inv := Quotient.ind fun Y => Quotient.sound ⟨e.counitIso.app Y⟩

/-- A packaged equivalence between the isomorphism-class quotients of two displayed functor
categories into a common category. -/
def auxiliaryFunctorIsomorphismClassesEquiv (D : Type*) [Category D] :
    Quotient (isIsomorphicSetoid (RepresentationTheory.AbstractTypeEquivalence.Left ⥤ D)) ≃
      Quotient (isIsomorphicSetoid (RepresentationTheory.AbstractTypeEquivalence.Right ⥤ D)) :=
  Equivalence.isomorphismClassesEquiv
    (RepresentationTheory.AbstractTypeEquivalence.equivalence.congrLeft (E := D))

/-- The displayed category of isomorphisms between two fixed categories has no objects. -/
theorem auxiliaryIsoCatIsEmpty : IsEmpty
    (IsoCat RepresentationTheory.AbstractTypeEquivalence.Left
      RepresentationTheory.AbstractTypeEquivalence.Right) := by
  refine ⟨fun e => ?_⟩
  let f : PUnit ≃ Bool := e.functor.objEquiv
  have : (true : Bool) = false :=
    f.symm.injective (Subsingleton.elim (f.symm true) (f.symm false))
  exact absurd this (by decide)

end RepresentationTheory.CategoryTheory.IsomorphismClasses

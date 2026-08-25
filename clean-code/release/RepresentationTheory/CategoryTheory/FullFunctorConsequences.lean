/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.SimpleRepresentationModules
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Simple

open CategoryTheory

universe u

namespace RepresentationTheory.CategoryTheory.FullFunctorConsequences

namespace CategoryTheory

attribute [local instance] CategoryTheory.isIsomorphicSetoid

/-- A functor sends an isomorphism class of objects in its source category to an isomorphism class in its target category. -/
def mapIsoClassQuotient {A B : Type*} [Category A] [Category B] (F : A ⥤ B) :
    Quotient (isIsomorphicSetoid A) → Quotient (isIsomorphicSetoid B) :=
  Quotient.map F.obj (fun _ _ ⟨e⟩ => ⟨F.mapIso e⟩)

/-- The map on object isomorphism classes induced by a full and faithful functor is injective. -/
theorem injective_mapIsoClassQuotient_of_full_faithful
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.Faithful] :
    Function.Injective (mapIsoClassQuotient F) := by
  refine fun a b => Quotient.inductionOn₂ a b fun X Y h => ?_
  simp only [mapIsoClassQuotient, Quotient.map_mk] at h
  obtain ⟨e⟩ := Quotient.exact h
  exact Quotient.sound ⟨F.preimageIso e⟩

end CategoryTheory

namespace ModuleCat

/-- Restriction of scalars along a surjective ring homomorphism is a full functor. -/
lemma full_restrictScalars_of_surjective {R S : Type*} [Ring R] [Ring S] {f : R →+* S}
    (hf : Function.Surjective f) : (ModuleCat.restrictScalars.{u} f).Full where
  map_surjective {M M'} g := by
    refine ⟨ModuleCat.ofHom
      { toFun := g.hom
        map_add' := g.hom.map_add
        map_smul' := fun s x => ?_ }, ?_⟩
    · obtain ⟨r, rfl⟩ := hf s
      exact g.hom.map_smul r x
    · ext x
      rfl

end ModuleCat

attribute [local instance] CategoryTheory.isIsomorphicSetoid

/-- A surjective ring homomorphism from a finite algebra bounds the cardinality of the target auxiliary type by that of the source auxiliary type. -/
theorem natCard_auxiliaryType_le_of_surjective_ringHom
    (k : Type u) {R T : Type*} [Field k] [Ring R] [Ring T] [Algebra k R]
    [Module.Finite k R] (f : R →+* T) (hf : Function.Surjective f) :
    Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} T) ≤
      Nat.card (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} R) := by
  classical
  haveI : RingHomSurjective f := ⟨hf⟩
  haveI := ModuleCat.full_restrictScalars_of_surjective.{u} (f := f) hf
  haveI : Finite (RepresentationTheory.SimpleRepresentationModules.AuxiliaryRingType.{u} R) :=
    RepresentationTheory.SimpleRepresentationModules.finite_auxiliaryRingType_of_module_finite k
  have hF : ∀ X :
      (RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty
        (ModuleCat.{u} T)).FullSubcategory,
      (RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty
        (ModuleCat.{u} R)) ((ModuleCat.restrictScalars f).obj X.obj) := by
    intro X
    haveI : Simple X.obj := X.property
    haveI : IsSimpleModule T X.obj := isSimpleModule_of_simple X.obj
    change Simple ((ModuleCat.restrictScalars f).obj X.obj)
    rw [simple_iff_isSimpleModule']
    let l : (ModuleCat.restrictScalars f).obj X.obj →ₛₗ[f] X.obj :=
      { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hl : Function.Bijective ⇑l := Function.bijective_id
    exact (l.isSimpleModule_iff_of_bijective hl).mpr inferInstance
  let L := (RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty
      (ModuleCat.{u} R)).lift
    ((RepresentationTheory.SimpleRepresentationModules.AuxiliaryObjectProperty
      (ModuleCat.{u} T)).ι ⋙ ModuleCat.restrictScalars f) hF
  exact Nat.card_le_card_of_injective (CategoryTheory.mapIsoClassQuotient L)
    (CategoryTheory.injective_mapIsoClassQuotient_of_full_faithful L)

end RepresentationTheory.CategoryTheory.FullFunctorConsequences

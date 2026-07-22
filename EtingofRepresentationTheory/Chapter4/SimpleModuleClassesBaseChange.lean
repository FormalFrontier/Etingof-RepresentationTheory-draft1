import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# A surjective algebra map decreases the number of simple modules

This file proves that a surjective ring homomorphism `f : R ↠ T` between finite-dimensional
`k`-algebras only decreases the number of isomorphism classes of simple modules:

  `Nat.card (SimpleModuleClasses T) ≤ Nat.card (SimpleModuleClasses R)`.

It is one of the three separability-free ingredients of the field-general base-change monotonicity
`#(simple k[G]-modules) ≤ #(simple K[G]-modules)`: the counting chain
factors through the semisimple quotient `k[G]/rad` and the surjection
`K[G] ↠ K ⊗_k (k[G]/rad)`, and this is the surjection step.

## Main results

* `Etingof.isoClassesMap` / `Etingof.isoClassesMap_injective`: a fully faithful functor induces an
  injection on isomorphism classes of objects.
* `ModuleCat.restrictScalars_full_of_surjective`: restriction of scalars along a surjective
  ring hom is a full functor (every `R`-linear map between `T`-modules is `T`-linear, because every
  scalar of `T` is `f` of a scalar of `R`).
* `Etingof.natCard_simpleModuleClasses_le_of_surjective`: the count inequality.
-/

open CategoryTheory

universe u

namespace Etingof

attribute [local instance] CategoryTheory.isIsomorphicSetoid

/-- A functor `F : A ⥤ B` induces a map on isomorphism classes of objects, `[X] ↦ [F X]`. -/
def isoClassesMap {A B : Type*} [Category A] [Category B] (F : A ⥤ B) :
    Quotient (isIsomorphicSetoid A) → Quotient (isIsomorphicSetoid B) :=
  Quotient.map F.obj (fun _ _ ⟨e⟩ => ⟨F.mapIso e⟩)

/-- A fully faithful functor induces an injection on isomorphism classes of objects: if
`F X ≅ F Y` then `X ≅ Y` by `Functor.preimageIso`. -/
theorem isoClassesMap_injective {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    [F.Full] [F.Faithful] : Function.Injective (isoClassesMap F) := by
  refine fun a b => Quotient.inductionOn₂ a b fun X Y h => ?_
  simp only [isoClassesMap, Quotient.map_mk] at h
  obtain ⟨e⟩ := Quotient.exact h
  exact Quotient.sound ⟨F.preimageIso e⟩

end Etingof

namespace ModuleCat

/-- **Restriction of scalars along a surjective ring hom is full.** If `f : R →+* S` is surjective,
then every `R`-linear map between the restrictions of two `S`-modules is already `S`-linear: for
`s = f r` we have `g (s • x) = g (r • x) = r • g x = s • g x`. Combined with the always-available
`Faithful` instance this makes `restrictScalars f` fully faithful. -/
lemma restrictScalars_full_of_surjective {R S : Type*} [Ring R] [Ring S] {f : R →+* S}
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

namespace Etingof

attribute [local instance] CategoryTheory.isIsomorphicSetoid

/-- **A surjective algebra map decreases the number of simple modules.** For finite-dimensional
`k`-algebras and a surjective ring hom `f : R ↠ T`, restriction of scalars along `f` sends simple
`T`-modules to simple `R`-modules (submodule lattices agree under a surjection) and is fully
faithful, so it induces an injection on isomorphism classes of simple modules. Hence

  `Nat.card (SimpleModuleClasses T) ≤ Nat.card (SimpleModuleClasses R)`.

No semisimplicity or separability is required. -/
theorem natCard_simpleModuleClasses_le_of_surjective
    (k : Type u) {R T : Type*} [Field k] [Ring R] [Ring T] [Algebra k R]
    [Module.Finite k R] (f : R →+* T) (hf : Function.Surjective f) :
    Nat.card (SimpleModuleClasses.{u} T) ≤ Nat.card (SimpleModuleClasses.{u} R) := by
  classical
  haveI : RingHomSurjective f := ⟨hf⟩
  haveI := ModuleCat.restrictScalars_full_of_surjective.{u} (f := f) hf
  haveI : Finite (SimpleModuleClasses.{u} R) := finite_simpleModuleClasses k
  -- Restriction of scalars sends a simple `T`-module to a simple `R`-module.
  have hF : ∀ X : (simpleProp (ModuleCat.{u} T)).FullSubcategory,
      (simpleProp (ModuleCat.{u} R)) ((ModuleCat.restrictScalars f).obj X.obj) := by
    intro X
    haveI : Simple X.obj := X.property
    haveI : IsSimpleModule T X.obj := isSimpleModule_of_simple X.obj
    change Simple ((ModuleCat.restrictScalars f).obj X.obj)
    rw [simple_iff_isSimpleModule']
    -- the identity is `f`-semilinear from the restricted `R`-module to the `T`-module
    let l : (ModuleCat.restrictScalars f).obj X.obj →ₛₗ[f] X.obj :=
      { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hl : Function.Bijective ⇑l := Function.bijective_id
    exact (l.isSimpleModule_iff_of_bijective hl).mpr inferInstance
  -- The induced functor on the full subcategories of simples, and its iso-class injection.
  let L := (simpleProp (ModuleCat.{u} R)).lift
    ((simpleProp (ModuleCat.{u} T)).ι ⋙ ModuleCat.restrictScalars f) hF
  exact Nat.card_le_card_of_injective (isoClassesMap L) (isoClassesMap_injective L)

end Etingof

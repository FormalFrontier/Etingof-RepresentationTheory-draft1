/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Torsion.Basic
import RepresentationTheory.Alignment.Attribute

universe v u

open CategoryTheory

namespace RepresentationTheory.RingTheory.Module.ParameterAssociated

variable (R : Type u) [Ring R]

section Corner

variable (e : RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.ringAuxiliaryType R)

/-- The ideal associated with an element of the opaque parameter space for R. -/
def parameterAssociatedIdeal : Ideal R where
  carrier := {x : R | e.1 * x = 0}
  add_mem' := by
    intro a b ha hb
    change e.1 * (a + b) = 0
    rw [mul_add, show e.1 * a = 0 from ha, show e.1 * b = 0 from hb, add_zero]
  zero_mem' := mul_zero _
  smul_mem' := by
    intro r x hx
    change e.1 * (r • x) = 0
    rw [smul_eq_mul, ← mul_assoc, e.2.2 r, mul_assoc, show e.1 * x = 0 from hx, mul_zero]

/-- An element belongs to the parameter-associated ideal exactly when its left multiple by the underlying parameter is zero. -/
theorem mem_parameterAssociatedIdeal_iff {x : R} :
    x ∈ parameterAssociatedIdeal R e ↔ e.1 * x = 0 := Iff.rfl

/-- The parameter-associated ideal is two-sided. -/
instance parameterAssociatedIdeal_isTwoSided : (parameterAssociatedIdeal R e).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    change e.1 * (a * b) = 0
    rw [← mul_assoc, show e.1 * a = 0 from ha, zero_mul]

/-- The type associated with an element of the opaque parameter space for R. -/
abbrev parameterAssociatedType : Type u := R ⧸ parameterAssociatedIdeal R e

/-- The ring homomorphism from R to the parameter-associated type. -/
def toParameterAssociatedRingHom : R →+* parameterAssociatedType R e :=
  Ideal.Quotient.mk (parameterAssociatedIdeal R e)

/-- The homomorphism from R to the parameter-associated type is surjective. -/
theorem toParameterAssociatedRingHom_surjective :
    Function.Surjective (toParameterAssociatedRingHom R e) :=
  Ideal.Quotient.mk_surjective

/-- The homomorphism to the parameter-associated type carries the surjective ring-homomorphism property. -/
instance toParameterAssociatedRingHom_ringHomSurjective :
    RingHomSurjective (toParameterAssociatedRingHom R e) :=
  ⟨toParameterAssociatedRingHom_surjective R e⟩

/-- Two elements have the same image under the homomorphism exactly when their left multiples by the parameter agree. -/
theorem toParameterAssociatedRingHom_eq_iff {x y : R} :
    toParameterAssociatedRingHom R e x = toParameterAssociatedRingHom R e y ↔
      e.1 * x = e.1 * y := by
  rw [toParameterAssociatedRingHom, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    mem_parameterAssociatedIdeal_iff, mul_sub, sub_eq_zero]

/-- The parameter-associated homomorphism sends the underlying parameter to one. -/
@[simp]
theorem toParameterAssociatedRingHom_parameter : toParameterAssociatedRingHom R e e.1 = 1 := by
  rw [show (1 : parameterAssociatedType R e) = toParameterAssociatedRingHom R e 1 from rfl,
    toParameterAssociatedRingHom_eq_iff, mul_one, e.2.1.eq]

/-- The R-linear endomorphism associated with an opaque parameter. -/
def parameterAssociatedLinearMap : R →ₗ[R] R where
  toFun x := e.1 * x
  map_add' := mul_add _
  map_smul' r x := by
    simp only [smul_eq_mul, RingHom.id_apply, ← mul_assoc, e.2.2 r]

/-- The R-linear map from the parameter-associated type to R. -/
def parameterTypeToBaseLinearMap : parameterAssociatedType R e →ₗ[R] R :=
  (parameterAssociatedIdeal R e).liftQ (parameterAssociatedLinearMap R e) (fun _ hx => hx)

/-- Mapping an element into the parameter-associated type and back to R gives left multiplication by the underlying parameter. -/
@[simp]
theorem parameterTypeToBaseLinearMap_toParameterAssociatedRingHom (x : R) :
    parameterTypeToBaseLinearMap R e (toParameterAssociatedRingHom R e x) = e.1 * x := rfl

/-- The R-linear map from the parameter-associated type to R is injective. -/
theorem parameterTypeToBaseLinearMap_injective :
    Function.Injective (parameterTypeToBaseLinearMap R e) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := toParameterAssociatedRingHom_surjective R e a
  obtain ⟨y, rfl⟩ := toParameterAssociatedRingHom_surjective R e b
  rw [parameterTypeToBaseLinearMap_toParameterAssociatedRingHom,
    parameterTypeToBaseLinearMap_toParameterAssociatedRingHom] at hab
  exact (toParameterAssociatedRingHom_eq_iff R e).mpr hab

/-- The image of one under the parameter-type-to-base linear map is the underlying parameter in R. -/
theorem parameterTypeToBaseLinearMap_one : parameterTypeToBaseLinearMap R e 1 = e.1 := by
  rw [show (1 : parameterAssociatedType R e) = toParameterAssociatedRingHom R e 1 from rfl,
    parameterTypeToBaseLinearMap_toParameterAssociatedRingHom, mul_one]

/-- The linear map from the parameter-associated type to R preserves multiplication. -/
theorem parameterTypeToBaseLinearMap_mul (a b : parameterAssociatedType R e) :
    parameterTypeToBaseLinearMap R e (a * b) =
      parameterTypeToBaseLinearMap R e a * parameterTypeToBaseLinearMap R e b := by
  obtain ⟨x, rfl⟩ := toParameterAssociatedRingHom_surjective R e a
  obtain ⟨y, rfl⟩ := toParameterAssociatedRingHom_surjective R e b
  have key : (e.1 * x) * (e.1 * y) = e.1 * (x * y) := by
    calc (e.1 * x) * (e.1 * y) = e.1 * (x * (e.1 * y)) := by rw [mul_assoc]
      _ = e.1 * ((x * e.1) * y) := by rw [mul_assoc x e.1 y]
      _ = e.1 * ((e.1 * x) * y) := by rw [← e.2.2 x]
      _ = (e.1 * e.1) * (x * y) := by rw [mul_assoc e.1 x y, ← mul_assoc]
      _ = e.1 * (x * y) := by rw [e.2.1.eq]
  rw [← map_mul (toParameterAssociatedRingHom R e),
    parameterTypeToBaseLinearMap_toParameterAssociatedRingHom,
    parameterTypeToBaseLinearMap_toParameterAssociatedRingHom,
    parameterTypeToBaseLinearMap_toParameterAssociatedRingHom, key]

/-- The range of the parameter-type-to-base linear map consists exactly of left multiples by the underlying parameter. -/
theorem range_parameterTypeToBaseLinearMap :
    Set.range (parameterTypeToBaseLinearMap R e) = {y : R | ∃ x : R, y = e.1 * x} := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := toParameterAssociatedRingHom_surjective R e a
    exact ⟨x, (parameterTypeToBaseLinearMap_toParameterAssociatedRingHom R e x)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨toParameterAssociatedRingHom R e x,
      parameterTypeToBaseLinearMap_toParameterAssociatedRingHom R e x⟩

end Corner

section RestrictScalars

variable {A B : Type*} [Ring A] [Ring B]

/-- Restriction of scalars along a surjective ring homomorphism is full. -/
theorem restrictScalars_full_of_surjective (f : A →+* B) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{v} f).Full where
  map_surjective {M N} g := by
    refine ⟨ModuleCat.ofHom (X := M) (Y := N)
      { toFun := g.hom
        map_add' := g.hom.map_add
        map_smul' := ?_ }, ?_⟩
    · intro b m
      obtain ⟨a, rfl⟩ := hf b
      exact g.hom.map_smul a m
    · rfl

/-- The scalar-compatible linear map from the carrier of a restricted module to its original carrier. -/
def restrictScalarsCarrierLinearMap (f : A →+* B) (N : ModuleCat.{v} B) :
    ((ModuleCat.restrictScalars f).obj N) →ₛₗ[f] (N : Type v) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Along a surjective ring homomorphism, a module has finite length exactly when its restriction of scalars does. -/
theorem isFiniteLength_restrictScalars_iff (f : A →+* B) [RingHomSurjective f]
    (N : ModuleCat.{v} B) :
    IsFiniteLength A (((ModuleCat.restrictScalars f).obj N) : Type v) ↔
      IsFiniteLength B (N : Type v) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian, isFiniteLength_iff_isNoetherian_isArtinian,
    (restrictScalarsCarrierLinearMap f N).isNoetherian_iff_of_bijective Function.bijective_id,
    (restrictScalarsCarrierLinearMap f N).isArtinian_iff_of_bijective Function.bijective_id]

end RestrictScalars

section BlockCategory

variable [Small.{v} R]

/-- The type produced from an R-module by the associated construction. -/
abbrev associatedModuleType (S : ModuleCat.{v} R) : Type (max u (v + 1)) :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{v} R =>
      RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''' R S M)

variable (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R]
variable {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)

include k

/-- An opaque parameter associated with a simple module over a finite-dimensional algebra. -/
noncomputable def simpleModuleParameter :
    RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.ringAuxiliaryType R :=
  ⟨(RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1,
    (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).2.2.1,
    (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).2.2.2.1⟩

omit [Small.{v} R] in
/-- The underlying value of the simple-module parameter equals that of the displayed comparison term. -/
@[simp]
theorem simpleModuleParameter_value_eq :
    (simpleModuleParameter R k hS).1 =
      (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1 :=
  rfl

/-- A module satisfying the displayed condition is torsion with respect to the parameter-associated ideal. -/
theorem isTorsionBy_parameterAssociatedIdeal_of_condition {M : ModuleCat.{v} R}
    (hM : RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''' R S M) :
    Module.IsTorsionBySet R (M : Type v)
      (parameterAssociatedIdeal R (simpleModuleParameter R k hS) : Set R) :=
  fun m a => by
    have h1 :
        (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1 • m = m :=
      (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.relation_iff_property_element_smul_eq R k hS M).mp hM m
    have ha :
        (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1 * (a : R) = 0 :=
      a.2
    calc (a : R) • m =
          (a : R) •
            ((RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1 • m) := by
            rw [h1]
      _ = ((a : R) *
            (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1) • m :=
          (mul_smul _ _ m).symm
      _ = ((RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1 *
            (a : R)) • m := by
            rw [(RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).2.2.2.1 (a : R)]
      _ = 0 := by rw [ha, zero_smul]

/-- Restricting scalars from the parameter-associated type yields a module satisfying the displayed condition. -/
theorem restrictScalars_satisfies_condition
    (N : ModuleCat.{v} (parameterAssociatedType R (simpleModuleParameter R k hS))) :
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''' R S
      ((ModuleCat.restrictScalars
        (toParameterAssociatedRingHom R (simpleModuleParameter R k hS))).obj N) := by
  rw [RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.relation_iff_property_element_smul_eq R k hS]
  intro m
  rw [ModuleCat.restrictScalars.smul_def]
  rw [show
      (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module R k hS).1 =
        (simpleModuleParameter R k hS).1 from rfl,
    toParameterAssociatedRingHom_parameter, one_smul]

/-- The functor from modules over the parameter-associated type to the category associated with the chosen simple module. -/
noncomputable def parameterModuleFunctor :
    ModuleCat.{v} (parameterAssociatedType R (simpleModuleParameter R k hS)) ⥤
      associatedModuleType R S :=
  ObjectProperty.lift _
    (ModuleCat.restrictScalars
      (toParameterAssociatedRingHom R (simpleModuleParameter R k hS)))
    (restrictScalars_satisfies_condition R k hS)

/-- The parameter-module functor is faithful. -/
instance parameterModuleFunctor_faithful : (parameterModuleFunctor R k hS).Faithful := by
  unfold parameterModuleFunctor; infer_instance

/-- The parameter-module functor is full. -/
instance parameterModuleFunctor_full : (parameterModuleFunctor R k hS).Full := by
  haveI := restrictScalars_full_of_surjective.{v}
    (toParameterAssociatedRingHom R (simpleModuleParameter R k hS))
    (toParameterAssociatedRingHom_surjective R _)
  unfold parameterModuleFunctor; infer_instance

/-- The parameter-module functor is essentially surjective. -/
instance parameterModuleFunctor_essSurj : (parameterModuleFunctor R k hS).EssSurj where
  mem_essImage M := by
    letI := (isTorsionBy_parameterAssociatedIdeal_of_condition R k hS M.property).module
    refine ⟨ModuleCat.of _ (M.obj : Type v), ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact LinearEquiv.toModuleIso
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- The parameter-module functor is an equivalence. -/
instance parameterModuleFunctor_isEquivalence :
    (parameterModuleFunctor R k hS).IsEquivalence where

/-- An equivalence from a module category determined by the parameter to the category determined by the simple module. -/
@[source_ref "Chapter9/Problem9.5.3" (role := supporting)]
noncomputable def parameterModuleEquivalence :
    ModuleCat.{v} (parameterAssociatedType R (simpleModuleParameter R k hS)) ≌
      associatedModuleType R S :=
  (parameterModuleFunctor R k hS).asEquivalence

/-- The forward functor of the parameter-module equivalence equals the displayed functor. -/
@[simp]
theorem parameterModuleEquivalence_functor_eq :
    (parameterModuleEquivalence R k hS).functor = parameterModuleFunctor R k hS :=
  rfl

/-- The functor between finite-length parameter-associated modules and finite-length modules satisfying the displayed condition. -/
noncomputable def finiteLengthParameterModuleFunctor :
    ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{v} (parameterAssociatedType R (simpleModuleParameter R k hS)) =>
          IsFiniteLength (parameterAssociatedType R (simpleModuleParameter R k hS))
            (N : Type v)) ⥤
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{v} R =>
          RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''' R S M ∧
            IsFiniteLength R (M : Type v)) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ ModuleCat.restrictScalars
      (toParameterAssociatedRingHom R (simpleModuleParameter R k hS)))
    (fun N => ⟨restrictScalars_satisfies_condition R k hS N.obj,
      (isFiniteLength_restrictScalars_iff _ N.obj).mpr N.property⟩)

/-- The finite-length parameter-module functor is faithful. -/
instance finiteLengthParameterModuleFunctor_faithful :
    (finiteLengthParameterModuleFunctor R k hS).Faithful := by
  unfold finiteLengthParameterModuleFunctor; infer_instance

/-- The finite-length parameter-module functor is full. -/
instance finiteLengthParameterModuleFunctor_full :
    (finiteLengthParameterModuleFunctor R k hS).Full := by
  haveI := restrictScalars_full_of_surjective.{v}
    (toParameterAssociatedRingHom R (simpleModuleParameter R k hS))
    (toParameterAssociatedRingHom_surjective R _)
  unfold finiteLengthParameterModuleFunctor; infer_instance

/-- The finite-length parameter-module functor is essentially surjective. -/
instance finiteLengthParameterModuleFunctor_essSurj :
    (finiteLengthParameterModuleFunctor R k hS).EssSurj where
  mem_essImage M := by
    letI := (isTorsionBy_parameterAssociatedIdeal_of_condition R k hS M.property.1).module
    refine ⟨⟨ModuleCat.of _ (M.obj : Type v), ?_⟩, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    · exact (isFiniteLength_restrictScalars_iff
        (toParameterAssociatedRingHom R (simpleModuleParameter R k hS))
        (ModuleCat.of _ (M.obj : Type v))).mp M.property.2
    · have e :
          ((ModuleCat.restrictScalars
            (toParameterAssociatedRingHom R (simpleModuleParameter R k hS))).obj
              (ModuleCat.of _ (M.obj : Type v))) ≅ M.obj :=
        LinearEquiv.toModuleIso
          { toFun := id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := id
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      exact e

/-- The finite-length parameter-module functor is an equivalence. -/
instance finiteLengthParameterModuleFunctor_isEquivalence :
    (finiteLengthParameterModuleFunctor R k hS).IsEquivalence where

/-- An equivalence between finite-length parameter-associated modules and finite-length modules satisfying the displayed condition. -/
@[source_ref "Chapter9/Problem9.5.3" (role := supporting)]
noncomputable def finiteLengthParameterEquivalence :
    ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{v} (parameterAssociatedType R (simpleModuleParameter R k hS)) =>
          IsFiniteLength (parameterAssociatedType R (simpleModuleParameter R k hS))
            (N : Type v)) ≌
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{v} R =>
          RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''' R S M ∧
            IsFiniteLength R (M : Type v)) :=
  (finiteLengthParameterModuleFunctor R k hS).asEquivalence

/-- Under the parameter-module equivalence, the underlying carrier of an object is unchanged. -/
theorem parameterModuleEquivalence_obj_carrier
    (N : ModuleCat.{v} (parameterAssociatedType R (simpleModuleParameter R k hS))) :
    (((parameterModuleEquivalence R k hS).functor.obj N).obj : Type v) = (N : Type v) :=
  rfl

end BlockCategory

end RepresentationTheory.RingTheory.Module.ParameterAssociated

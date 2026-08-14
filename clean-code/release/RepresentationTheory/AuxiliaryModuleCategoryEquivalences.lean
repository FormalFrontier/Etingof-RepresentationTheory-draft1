/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Auxiliary.SimpleModuleRelations
import RepresentationTheory.RingTheory.Module.ParameterAssociated
import RepresentationTheory.ModuleCat.FiniteUnderEquivalence
import RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ExtProperties
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

universe u

open CategoryTheory
open RepresentationTheory.Auxiliary.SimpleModuleRelations
open RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ExtProperties
open RepresentationTheory.ModuleCat.Auxiliary
open RepresentationTheory.ModuleCat.FiniteUnderEquivalence
open RepresentationTheory.RingTheory.Module.ParameterAssociated

namespace RepresentationTheory.AuxiliaryModuleCategoryEquivalences

variable (R : Type u) [Ring R] [Small.{u} R]
variable (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R]
variable {S : ModuleCat.{u} R} (hS : IsSimpleModule R S)

include k

private noncomputable instance cornerNontrivial :
    Nontrivial (parameterAssociatedType R (simpleModuleParameter R k hS)) := by
  let e := simpleModuleParameter R k hS
  refine ⟨⟨1, 0, fun h =>
    (RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions.property_element_of_simple_module
      R k hS).2.1 ?_⟩⟩
  change e.1 = 0
  rw [← parameterTypeToBaseLinearMap_one R e, h]
  exact map_zero (parameterTypeToBaseLinearMap R e)

/-- The displayed ring formed from the given simple module data is simple. -/
theorem isSimpleRing_auxiliary [IsSemisimpleRing R] :
    IsSimpleRing (parameterAssociatedType R (simpleModuleParameter R k hS)) := by
  let e := simpleModuleParameter R k hS
  let C := parameterAssociatedType R e
  let q := toParameterAssociatedRingHom R e
  let F := ModuleCat.restrictScalars.{u} q
  letI : RingHomSurjective q := ⟨toParameterAssociatedRingHom_surjective R e⟩
  letI : IsSemisimpleRing C :=
    RingHom.isSemisimpleRing_of_surjective q (toParameterAssociatedRingHom_surjective R e)
  have h_isotypic : IsIsotypic C C := by
    intro I hI J hJ
    let XI : ModuleCat.{u} C := ModuleCat.of C I
    let XJ : ModuleCat.{u} C := ModuleCat.of C J
    have hRI : IsSimpleModule R (F.obj XI) := by
      rw [(restrictScalarsCarrierLinearMap q XI).isSimpleModule_iff_of_bijective
        Function.bijective_id]
      exact hI
    have hRJ : IsSimpleModule R (F.obj XJ) := by
      rw [(restrictScalarsCarrierLinearMap q XJ).isSimpleModule_iff_of_bijective
        Function.bijective_id]
      exact hJ
    have hXI : auxiliaryModuleRelation'''' R S (F.obj XI) :=
      restrictScalars_satisfies_condition R k hS XI
    have hXJ : auxiliaryModuleRelation'''' R S (F.obj XJ) :=
      restrictScalars_satisfies_condition R k hS XJ
    have hlinkedI : auxiliaryModuleRelation R (F.obj XI) S :=
      hXI (F.obj XI) (selfCondition_of_isSimpleModule hRI)
    have hlinkedJ : auxiliaryModuleRelation R (F.obj XJ) S :=
      hXJ (F.obj XJ) (selfCondition_of_isSimpleModule hRJ)
    have hlinkedJI : auxiliaryModuleRelation R (F.obj XJ) (F.obj XI) :=
      (auxiliaryModuleRelation_equivalence R).trans hlinkedJ
        ((auxiliaryModuleRelation_equivalence R).symm hlinkedI)
    obtain ⟨isoR⟩ :=
      (auxiliary_relation_iff_nonemptyIso_of_simpleModules R (F.obj XJ) (F.obj XI) hRJ hRI).mp
        hlinkedJI
    letI : F.Full :=
      restrictScalars_full_of_surjective q (toParameterAssociatedRingHom_surjective R e)
    haveI : F.Faithful := inferInstance
    exact ⟨(F.preimageIso isoR).toLinearEquiv⟩
  exact (isSimpleRing_isArtinianRing_iff.mpr
    ⟨inferInstance, h_isotypic, inferInstance⟩).1

/-- Constructs an equivalence from modules over the field to modules over the displayed simple ring. -/
noncomputable def auxiliarySimpleRingModuleCategoryEquivalence [IsAlgClosed k]
    [IsSemisimpleRing R] :
    ModuleCat.{u} k ≌
      ModuleCat.{u} (parameterAssociatedType R (simpleModuleParameter R k hS)) := by
  let e := simpleModuleParameter R k hS
  let C := parameterAssociatedType R e
  letI : IsSemisimpleRing C :=
    RingHom.isSemisimpleRing_of_surjective
      (toParameterAssociatedRingHom R e) (toParameterAssociatedRingHom_surjective R e)
  letI : IsSimpleRing C := isSimpleRing_auxiliary R k hS
  have hW : Nonempty
      {n : ℕ // NeZero n ∧ Nonempty (C ≃ₐ[k] Matrix (Fin n) (Fin n) k)} := by
    obtain ⟨n, hn, hφ⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k C
    exact ⟨⟨n, hn, hφ⟩⟩
  let W := Classical.choice hW
  letI : NeZero W.1 := W.2.1
  let φ := W.2.2.some
  exact (ModuleCat.matrixEquivalence k (0 : Fin W.1)).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv φ.toRingEquiv)

/-- Constructs an equivalence from the module category over the field to the displayed module category. -/
noncomputable def auxiliaryModuleCategoryEquivalence [IsAlgClosed k] [IsSemisimpleRing R] :
    ModuleCat.{u} k ≌ associatedModuleType R S :=
  (auxiliarySimpleRingModuleCategoryEquivalence R k hS).trans
    (parameterModuleEquivalence R k hS)

/-- An auxiliary type associated with a field. -/
abbrev AuxiliaryFieldCategory : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{u} k => IsFiniteLength k (M : Type u))

/-- An auxiliary type associated with a small ring and one of its module-category objects. -/
abbrev AuxiliaryModuleCategory : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{u} R =>
      auxiliaryModuleRelation'''' R S M ∧ IsFiniteLength R (M : Type u))

/-- Constructs an equivalence from the displayed field-associated auxiliary type to the displayed ring-and-module-associated auxiliary type. -/
noncomputable def auxiliaryFieldCategoryEquivalence [IsAlgClosed k]
    [IsSemisimpleRing R] :
    AuxiliaryFieldCategory k ≌ AuxiliaryModuleCategory R (S := S) := by
  let e := simpleModuleParameter R k hS
  let C := parameterAssociatedType R e
  letI : IsSemisimpleRing C :=
    RingHom.isSemisimpleRing_of_surjective
      (toParameterAssociatedRingHom R e) (toParameterAssociatedRingHom_surjective R e)
  let E : ModuleCat.{u} k ≌ ModuleCat.{u} C :=
    auxiliarySimpleRingModuleCategoryEquivalence R k hS
  let Q : ObjectProperty (ModuleCat.{u} C) :=
    fun N => IsFiniteLength C (N : Type u)
  let P : ObjectProperty (ModuleCat.{u} k) :=
    fun M => IsFiniteLength k (M : Type u)
  letI : Q.IsClosedUnderIsomorphisms :=
    ⟨fun iso h => iso.toLinearEquiv.isFiniteLength h⟩
  have hobj : Q.inverseImage E.functor = P := by
    funext M
    apply propext
    exact ((IsArtinianRing.tfae C (E.functor.obj M)).out 0 3).symm.trans
      ((moduleFinite_equivalence_functor_obj_iff E M).trans
        ((IsArtinianRing.tfae k M).out 0 3))
  exact (E.congrFullSubcategory hobj).trans (finiteLengthParameterEquivalence R k hS)

end RepresentationTheory.AuxiliaryModuleCategoryEquivalences

/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.ModuleCat.Auxiliary
import RepresentationTheory.InvolutiveSquareZeroAlgebra
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

universe v u

open CategoryTheory

namespace RepresentationTheory.Auxiliary.SimpleModuleRelations

/-- Shows that the displayed auxiliary relation does not hold between two module-category objects over a semisimple ring. -/
theorem auxiliary_not_relation_of_semisimpleRing
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (A B : ModuleCat.{v} R) :
    ¬ RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'' R A B := by
  intro h
  rcases h with h | h
  · haveI : Module.Projective R A := Module.projective_of_isSemisimpleRing R A
    haveI := Abelian.Ext.subsingleton_of_projective A B 0
    exact not_nontrivial _ h
  · haveI : Module.Projective R B := Module.projective_of_isSemisimpleRing R B
    haveI := Abelian.Ext.subsingleton_of_projective B A 0
    exact not_nontrivial _ h

/-- Characterizes the displayed auxiliary relation between simple module-category objects over a semisimple ring by the existence of an isomorphism. -/
theorem auxiliary_relation_iff_nonemptyIso_of_simpleModules
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R) (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) :
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation R X Y ↔ Nonempty (X ≅ Y) := by
  refine ⟨fun hlinked => ?_, fun e =>
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_of_iso R hX hY e.some⟩
  clear hX hY
  induction hlinked with
  | rel _ _ h =>
    obtain ⟨_, _, h⟩ := h
    rcases h with h | h
    · exact absurd h (auxiliary_not_relation_of_semisimpleRing R _ _)
    · exact h
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨e.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨e₁ ≪≫ e₂⟩

/-- Produces an isomorphism between simple module-category objects over a semisimple ring from the displayed auxiliary relation. -/
theorem nonemptyIso_of_auxiliary_relation_of_simpleModules
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R)
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y)
    (hlinked : RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation R X Y) :
    Nonempty (X ≅ Y) :=
  (auxiliary_relation_iff_nonemptyIso_of_simpleModules R X Y hX hY).mp hlinked

/-- Provides the displayed auxiliary relation between two simple module-category objects over a local Artinian commutative ring. -/
theorem auxiliary_relation_of_simpleModules_of_localArtinian
    (R : Type u) [CommRing R] [Small.{v} R] [IsLocalRing R] [IsArtinianRing R]
    (X Y : ModuleCat.{v} R)
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) :
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation R X Y := by
  obtain ⟨I, hI, ⟨eX⟩⟩ := isSimpleModule_iff_quot_maximal.mp hX
  obtain ⟨J, hJ, ⟨eY⟩⟩ := isSimpleModule_iff_quot_maximal.mp hY
  have hIm : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
  have hJm : J = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hJ
  subst hIm; subst hJm
  have e : X ≃ₗ[R] Y := eX.trans eY.symm
  exact RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_of_iso R hX hY
    { hom := ModuleCat.ofHom e.toLinearMap
      inv := ModuleCat.ofHom e.symm.toLinearMap
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by ext x; exact e.apply_symm_apply x }

/-- Establishes the displayed auxiliary relation between the two specified module-category objects. -/
theorem auxiliary_relation_between_fixed :
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation
      RepresentationTheory.InvolutiveSquareZeroAlgebra.Algebra
      (ModuleCat.of _ RepresentationTheory.InvolutiveSquareZeroAlgebra.PositiveSimple)
      (ModuleCat.of _ RepresentationTheory.InvolutiveSquareZeroAlgebra.NegativeSimple) :=
  RepresentationTheory.InvolutiveSquareZeroAlgebra.positiveNegativeSimple_property

open RepresentationTheory.InvolutiveSquareZeroAlgebra in
/-- Establishes the displayed auxiliary relation from a simple module-category object to the specified fixed object. -/
theorem auxiliary_relation_of_simpleModule_to_fixed
    (Z : Type) [AddCommGroup Z] [Module ℂ Z] [Module Algebra Z] [IsScalarTower ℂ Algebra Z]
    [IsSimpleModule Algebra Z] :
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation Algebra
      (ModuleCat.of Algebra Z) (ModuleCat.of Algebra PositiveSimple) := by
  have hZ : IsSimpleModule Algebra (ModuleCat.of Algebra Z) := inferInstanceAs (IsSimpleModule Algebra Z)
  have hP : IsSimpleModule Algebra (ModuleCat.of Algebra PositiveSimple) :=
    inferInstanceAs (IsSimpleModule Algebra PositiveSimple)
  have hM : IsSimpleModule Algebra (ModuleCat.of Algebra NegativeSimple) :=
    inferInstanceAs (IsSimpleModule Algebra NegativeSimple)
  rcases simpleModule_equiv_positive_or_negative Z with h | h
  · obtain ⟨e⟩ := h
    exact RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_of_iso Algebra hZ hP
      { hom := ModuleCat.ofHom e.toLinearMap
        inv := ModuleCat.ofHom e.symm.toLinearMap
        hom_inv_id := by ext z; exact e.symm_apply_apply z
        inv_hom_id := by ext z; exact e.apply_symm_apply z }
  · obtain ⟨e⟩ := h
    refine Relation.EqvGen.trans _ _ _
      (RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_of_iso Algebra hZ hM
        { hom := ModuleCat.ofHom e.toLinearMap
          inv := ModuleCat.ofHom e.symm.toLinearMap
          hom_inv_id := by ext z; exact e.symm_apply_apply z
          inv_hom_id := by ext z; exact e.apply_symm_apply z })
      (Relation.EqvGen.symm _ _ auxiliary_relation_between_fixed)

open RepresentationTheory.InvolutiveSquareZeroAlgebra in
/-- Establishes the displayed auxiliary relation between module-category objects induced by two simple modules. -/
theorem auxiliary_relation_of_simpleModules
    (X Y : Type) [AddCommGroup X] [Module ℂ X] [Module Algebra X] [IsScalarTower ℂ Algebra X]
    [IsSimpleModule Algebra X] [AddCommGroup Y] [Module ℂ Y] [Module Algebra Y]
    [IsScalarTower ℂ Algebra Y] [IsSimpleModule Algebra Y] :
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation Algebra
      (ModuleCat.of Algebra X) (ModuleCat.of Algebra Y) :=
  Relation.EqvGen.trans _ _ _ (auxiliary_relation_of_simpleModule_to_fixed X)
    (Relation.EqvGen.symm _ _ (auxiliary_relation_of_simpleModule_to_fixed Y))

end RepresentationTheory.Auxiliary.SimpleModuleRelations

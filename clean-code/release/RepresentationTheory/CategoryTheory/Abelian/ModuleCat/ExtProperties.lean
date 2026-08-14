/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.FiniteLength
import RepresentationTheory.Algebra.Module.SimpleQuotient

/-!
# Extension properties of finite-length module objects

This module establishes subsingleton criteria for extension spaces of module objects under
finite-length and relation-exclusion hypotheses.
-/

universe v u

open CategoryTheory CategoryTheory.Limits
open RepresentationTheory.ModuleCat.Auxiliary
open RepresentationTheory.Algebra.Module.SimpleQuotient

namespace RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ExtProperties

variable {R : Type u} [Ring R] [Small.{v} R]

/-- Extensions in every degree with a zero module object as the left argument form a subsingleton. -/
theorem extSubsingleton_of_isZero_left {Z Y : ModuleCat.{v} R} (hZ : IsZero Z) (n : ℕ) :
    Subsingleton (Abelian.Ext Z Y n) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Abelian.Ext Z Y n, x = 0 := by
    intro x
    rw [← Abelian.Ext.mk₀_id_comp x, hZ.eq_of_src (𝟙 Z) 0]
    simp
  rw [key a, key b]

/-- Extensions in every degree with a zero module object as the right argument form a subsingleton. -/
theorem extSubsingleton_of_isZero_right {X Z : ModuleCat.{v} R} (hZ : IsZero Z) (n : ℕ) :
    Subsingleton (Abelian.Ext X Z n) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : Abelian.Ext X Z n, x = 0 := by
    intro x
    rw [← Abelian.Ext.comp_mk₀_id x, hZ.eq_of_src (𝟙 Z) 0]
    simp
  rw [key a, key b]

omit [Small.{v} R] in
/-- A simple module object satisfies the displayed condition relating it to itself. -/
theorem selfCondition_of_isSimpleModule {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    auxiliaryModuleRelationOverRing R S S :=
  simple_target_iff.mpr ⟨hS, ⊤, Submodule.topEquiv.toLinearMap, Submodule.topEquiv.surjective⟩

/-- The short exact sequence associated with a submodule. -/
private def submoduleSES {Y : Type v} [AddCommGroup Y] [Module R Y] (N : Submodule R Y) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by ext x; simp)

omit [Small.{v} R] in
private theorem submoduleSES_shortExact {Y : Type v} [AddCommGroup Y] [Module R Y]
    (N : Submodule R Y) : (submoduleSES N).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N) N.subtype_injective
    N.mkQ_surjective

/-- The degree-one extension space between the indicated objects has at most one element under the given simplicity, finite-length, and exclusion hypotheses. -/
theorem extOneSubsingleton_of_simpleModule_of_finiteLength_of_exclusion
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    ∀ {Y : Type v} [AddCommGroup Y] [Module R Y], IsFiniteLength R Y →
      (∀ V : ModuleCat.{v} R, auxiliaryModuleRelationOverRing R (ModuleCat.of R Y) V →
        ¬ auxiliaryModuleRelation R S V) →
      Subsingleton (Abelian.Ext S (ModuleCat.of R Y) 1) := by
  intro Y _ _ hY
  induction hY with
  | @of_subsingleton Y _ _ _ =>
      intro _
      exact extSubsingleton_of_isZero_right
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R Y)) 1
  | @of_simple_quotient Y _ _ N _ hN ih =>
      intro h
      set T : ModuleCat.{v} R := ModuleCat.of R (Y ⧸ N) with hT_def
      have hT : IsSimpleModule R T := ‹IsSimpleModule R (Y ⧸ N)›
      have hcfT : auxiliaryModuleRelationOverRing R (ModuleCat.of R Y) T :=
        auxiliaryModuleRelationOverRing.of_surjective N.mkQ N.mkQ_surjective
          (selfCondition_of_isSimpleModule hT)
      have hExtN : Subsingleton (Abelian.Ext S (ModuleCat.of R N) 1) :=
        ih (fun V hcf => h V (auxiliaryModuleRelationOverRing.of_submodule N hcf))
      have hExtT : Subsingleton (Abelian.Ext S T 1) := by
        rw [← not_nontrivial_iff_subsingleton]
        intro hnt
        exact h T hcfT
          (auxiliaryModuleRelation_of_auxiliaryModuleRelation'' R hS hT (Or.inl hnt))
      have hSE := submoduleSES_shortExact N
      haveI : Subsingleton (Abelian.Ext S (submoduleSES N).X₁ 1) := hExtN
      haveI : Subsingleton (Abelian.Ext S (submoduleSES N).X₃ 1) := hExtT
      have hX₂ : Subsingleton (Abelian.Ext S (submoduleSES N).X₂ 1) := by
        refine ⟨fun a b => ?_⟩
        suffices key : ∀ x : Abelian.Ext S (submoduleSES N).X₂ 1, x = 0 by rw [key a, key b]
        intro x
        obtain ⟨x₁, hx₁⟩ :=
          Abelian.Ext.covariant_sequence_exact₂ S hSE x (Subsingleton.elim _ _)
        rw [← hx₁, Subsingleton.elim x₁ 0, Abelian.Ext.zero_comp]
      exact hX₂

/-- After forming the module object from the specified finite-length carrier, its degree-one extension space with the other finite-length object has at most one element under the displayed exclusion condition. -/
theorem extOneSubsingleton_of_finiteLengthCarrier_of_exclusion
    {Y : ModuleCat.{v} R} (hY : IsFiniteLength R Y) :
    ∀ {X : Type v} [AddCommGroup X] [Module R X], IsFiniteLength R X →
      (∀ U V : ModuleCat.{v} R,
        auxiliaryModuleRelationOverRing R (ModuleCat.of R X) U →
        auxiliaryModuleRelationOverRing R Y V → ¬ auxiliaryModuleRelation R U V) →
      Subsingleton (Abelian.Ext (ModuleCat.of R X) Y 1) := by
  intro X _ _ hX
  induction hX with
  | @of_subsingleton X _ _ _ =>
      intro _
      exact extSubsingleton_of_isZero_left
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R X)) 1
  | @of_simple_quotient X _ _ N _ hN ih =>
      intro h
      set S₀ : ModuleCat.{v} R := ModuleCat.of R (X ⧸ N) with hS₀_def
      have hS₀ : IsSimpleModule R S₀ := ‹IsSimpleModule R (X ⧸ N)›
      have hcfS₀ : auxiliaryModuleRelationOverRing R (ModuleCat.of R X) S₀ :=
        auxiliaryModuleRelationOverRing.of_surjective N.mkQ N.mkQ_surjective
          (selfCondition_of_isSimpleModule hS₀)
      have hExtN : Subsingleton (Abelian.Ext (ModuleCat.of R N) Y 1) :=
        ih (fun U V hU hV => h U V (auxiliaryModuleRelationOverRing.of_submodule N hU) hV)
      have hExtS₀ : Subsingleton (Abelian.Ext S₀ Y 1) :=
        extOneSubsingleton_of_simpleModule_of_finiteLength_of_exclusion hS₀ hY
          (fun V hcfV => h S₀ V hcfS₀ hcfV)
      have hSE := submoduleSES_shortExact N
      haveI : Subsingleton (Abelian.Ext (submoduleSES N).X₁ Y 1) := hExtN
      haveI : Subsingleton (Abelian.Ext (submoduleSES N).X₃ Y 1) := hExtS₀
      have hX₂ : Subsingleton (Abelian.Ext (submoduleSES N).X₂ Y 1) := by
        refine ⟨fun a b => ?_⟩
        suffices key : ∀ x : Abelian.Ext (submoduleSES N).X₂ Y 1, x = 0 by rw [key a, key b]
        intro x
        obtain ⟨x₁, hx₁⟩ :=
          Abelian.Ext.contravariant_sequence_exact₂ hSE Y x (Subsingleton.elim _ _)
        rw [← hx₁, Subsingleton.elim x₁ 0, Abelian.Ext.comp_zero]
      exact hX₂

/-- The degree-one extension space between two finite-length module objects is a subsingleton when the stated exclusion hypothesis holds. -/
theorem extOneSubsingleton_of_finiteLengthModules_of_exclusion
    {X Y : ModuleCat.{v} R} (hX : IsFiniteLength R X) (hY : IsFiniteLength R Y)
    (h : ∀ U V : ModuleCat.{v} R,
      auxiliaryModuleRelationOverRing R X U → auxiliaryModuleRelationOverRing R Y V →
        ¬ auxiliaryModuleRelation R U V) :
    Subsingleton (Abelian.Ext X Y 1) :=
  extOneSubsingleton_of_finiteLengthCarrier_of_exclusion hY hX h

end RepresentationTheory.CategoryTheory.Abelian.ModuleCat.ExtProperties

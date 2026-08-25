/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Homology.TensorProductConstruction
import RepresentationTheory.Algebra.Module.BalancedTensorProduct.Adjunction
import RepresentationTheory.Algebra.Category.ModuleCat.TensorHom
import RepresentationTheory.Algebra.ModuleCategory.Auxiliary
import RepresentationTheory.ModulePairing.Projective
import RepresentationTheory.ModuleCategoryTensorFinsupp
import RepresentationTheory.CategoryTheory.LeftDerivedFunctor.ConnectingMorphisms
import RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses
import RepresentationTheory.Algebra.Module.ExtensionCocycles
import RepresentationTheory.Algebra.Homology.TensorBarResolution
import RepresentationTheory.HomologicalAlgebra.CochainComplexComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import RepresentationTheory.Alignment.Attribute


/-!
# Derived Functor Exactness
-/

namespace RepresentationTheory.DerivedFunctorExactness

open _root_.CategoryTheory TensorProduct CochainComplex.HomComplex

universe u


/-- Relates the displayed degree-zero object to an additive commutative group object. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
theorem AuxiliaryDegreeZeroIso
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A N M 0 ≅ AddCommGrpCat.of (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N M)) :=
  ⟨((RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf).app M⟩


/-- Provides an additive equivalence from the displayed degree-zero construction to module morphisms. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
theorem AuxiliaryDegreeZeroAddEquiv
    (A : Type u) [Ring A] (M N : ModuleCat.{u} A) :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses M N 0 ≃+ (M ⟶ N)) :=
  ⟨CategoryTheory.Abelian.Ext.addEquiv₀⟩


/-- Defines the displayed additive equivalence between the degree-one constructions. -/
@[source_ref "Chapter8/Problem8.2.6" (role := primary)]
noncomputable def AuxiliaryDegreeOneExtAddEquiv
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] :
    RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of A W) (ModuleCat.of A V) 1
      ≃+ RepresentationTheory.Algebra.Module.ExtensionCocycles.AuxiliaryData k A V W :=
  ((RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).extAddEquivCohomologyClass
      (Y := ModuleCat.of A V) (n := 1)).trans
    (RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.firstCohomologyEquivAuxiliaryQuotient k A W V)


/-- Describes the value of the displayed degree-one additive equivalence on an element. -/
@[simp]
theorem AuxiliaryDegreeOneExtAddEquiv_apply
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (x : RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of A W) (ModuleCat.of A V) 1) :
    AuxiliaryDegreeOneExtAddEquiv k A V W x =
      RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.firstCohomologyEquivAuxiliaryQuotient k A W V
        ((RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).extAddEquivCohomologyClass x) :=
  rfl


/-- Builds a degree-one cocycle from a morphism whose displayed composite vanishes. -/
noncomputable def AuxiliaryCocycleOfComposedZero
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (f : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.X 1 ⟶ ModuleCat.of A V)
    (hf : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.d 2 1 ≫ f = 0) :
    Cocycle (RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.auxiliaryCochainComplex k A W) (RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.auxiliaryTargetCochainComplex A V) 1 :=
  Cocycle.toSingleMk
    (((RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).cochainComplexXIso (-(1 : ℕ)) 1 rfl).hom ≫ f) (by simp)
    (-(2 : ℕ)) (by lia)
    (by
      rw [ProjectiveResolution.cochainComplex_d (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W)
        (-(2 : ℕ)) (-(1 : ℕ)) 2 1 (by norm_num) (by norm_num)]
      simp [Category.assoc, hf])


/-- Computes the displayed degree-one equivalence on an extension built from a cocycle. -/
@[simp]
theorem AuxiliaryDegreeOneExtAddEquiv_extMk
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (f : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.X 1 ⟶ ModuleCat.of A V)
    (hf : (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).complex.d 2 1 ≫ f = 0) :
    AuxiliaryDegreeOneExtAddEquiv k A V W
        ((RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A W).extMk f 2 rfl hf) =
      RepresentationTheory.HomologicalAlgebra.CochainComplexComparison.firstCohomologyEquivAuxiliaryQuotient k A W V
        (CohomologyClass.mk (AuxiliaryCocycleOfComposedZero k A V W f hf)) := by
  unfold AuxiliaryDegreeOneExtAddEquiv
  rw [AddEquiv.trans_apply,
    ProjectiveResolution.extAddEquivCohomologyClass_apply,
    ProjectiveResolution.extEquivCohomologyClass_extMk]
  rfl


/-- Provides the stated additive equivalence at degree one for the module data. -/
@[source_ref "Chapter8/Problem8.2.6" (role := primary)]
theorem AuxiliaryDegreeOneAddEquiv
    (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]
    (V W : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] :
    Nonempty (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of A W) (ModuleCat.of A V) 1
      ≃+ RepresentationTheory.Algebra.Module.ExtensionCocycles.AuxiliaryData k A V W) :=
  ⟨AuxiliaryDegreeOneExtAddEquiv k A V W⟩


/-- Shows that the covariant sequence associated to a short exact complex is exact at adjacent indices. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
theorem covariantSequence_exact
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (Abelian.Ext.covariantSequence (X := M) hS n₀ n₁ h).Exact :=
  Abelian.Ext.covariantSequence_exact M hS n₀ n₁ h

set_option backward.isDefEq.respectTransparency false in


/-- Shows that the displayed morphisms associated to a short complex have zero composite. -/
lemma AuxiliaryShortComplexHom_comp
    (A : Type u) [Ring A] {S : ShortComplex (ModuleCat.{u} A)} :
    RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.f.hom ≫ RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom = 0 := by
  have hcomp : ∀ (n : S.X₁), S.g.hom (S.f.hom n) = 0 := by
    intro n
    have h0 : (S.f ≫ S.g).hom n = 0 := by rw [S.zero]; rfl
    rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at h0
  ext Y x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  induction y with
  | zero => simp
  | tmul m n =>
    change RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryAddMonoidHom A S.g.hom Y (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryAddMonoidHom A S.f.hom Y
      (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n))) = 0
    rw [RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryAddMonoidHom_tmul, RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryAddMonoidHom_tmul, hcomp n, tmul_zero]
    rfl
  | add a b ha hb =>
    rw [show ((a + b : TensorProduct ℤ Y ↑S.X₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A ↑S.X₁ Y)
          = (a : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A ↑S.X₁ Y) + b from
        map_add (QuotientAddGroup.mk' (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A ↑S.X₁ Y)) a b,
      map_add, map_add, ha, hb]


/-- Obtains an exact five-arrow sequence from a short exact complex and the displayed module data. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
theorem AuxiliaryCovariantExactSequence
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₃ M n₁ ⟶ RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₁ M n₀,
      (ComposableArrows.mk₅
        (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.f.hom n₁ M) (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom n₁ M)
        δ
        (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.f.hom n₀ M) (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom n₀ M)).Exact := by


  exact RepresentationTheory.FunctorPairConstructions.associatedType.exists_derivedConnectingMorphism_exact
    (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.f.hom) (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom)
    (AuxiliaryShortComplexHom_comp A)
    (fun Y _ => RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_map_shortExact A Y hS) M n₀ n₁ h


/-- Defines the comparison isomorphism from degree zero to the left-derived functor value. -/
noncomputable def leftDerivedZeroIso
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A N M 0 ≅
      (Functor.leftDerived (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M) 0).obj (ModuleCat.of A N) :=
  ((RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf.app M) ≪≫
    ((RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M).leftDerivedZeroIsoSelf.app (ModuleCat.of A N)).symm

set_option backward.isDefEq.respectTransparency false in


/-- Obtains an exact five-arrow sequence by applying the displayed left-derived maps to a short exact complex. -/
theorem AuxiliaryLeftDerivedExactSequence
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (Functor.leftDerived (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A S.X₃) n₁).obj (ModuleCat.of A N) ⟶
          (Functor.leftDerived (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A S.X₁) n₀).obj (ModuleCat.of A N),
      (ComposableArrows.mk₅
        ((NatTrans.leftDerived (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.f) n₁).app (ModuleCat.of A N))
        ((NatTrans.leftDerived (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.g) n₁).app (ModuleCat.of A N))
        δ
        ((NatTrans.leftDerived (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.f) n₀).app (ModuleCat.of A N))
        ((NatTrans.leftDerived (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.g) n₀).app (ModuleCat.of A N))).Exact := by

  have hcomp : ∀ (m : S.X₁), S.g.hom (S.f.hom m) = 0 := by
    intro m
    have h0 : (S.f ≫ S.g).hom m = 0 := by rw [S.zero]; rfl
    rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at h0


  have w : RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.f ≫ RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.g = 0 := by
    ext N' x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n =>
      change (QuotientAddGroup.mk (S.g.hom (S.f.hom m) ⊗ₜ[ℤ] n)
          : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N' S.X₃) = 0
      rw [hcomp m, zero_tmul]
      rfl
    | add a b ha hb =>
      rw [show ((a + b : TensorProduct ℤ S.X₁ N') : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N' S.X₁)
            = (a : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A N' S.X₁) + b from
          map_add (QuotientAddGroup.mk' (RepresentationTheory.Algebra.Homology.TensorProductConstruction.integerTensorSubgroup A N' S.X₁)) a b,
        map_add, map_add, ha, hb]


  exact RepresentationTheory.FunctorPairConstructions.associatedType.exists_derivedConnectingMorphism_exact
    (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.f) (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A S.g) w
    (fun Y _ => RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryShortExact_map_of_projective A Y hS) (ModuleCat.of A N) n₀ n₁ h


section BalancingIV

open CategoryTheory.Limits

universe v₁ u₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in


/-- States commutativity of the natural comparison square at degree zero. -/
lemma leftDerivedZero_naturality
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
    {D : Type*} [Category D] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (X : C) :
    (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X
      = F.fromLeftDerivedZero.app X ≫ α.app X := by
  let P : ProjectiveResolution X := projectiveResolution X
  rw [ProjectiveResolution.leftDerived_app_eq α P 0,
    ProjectiveResolution.fromLeftDerivedZero_eq P G,
    ProjectiveResolution.fromLeftDerivedZero_eq P F]
  simp only [HomologicalComplex.homologyFunctor_map, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.cancel_iso_hom_left, ← Iso.inv_comp_eq,
    ChainComplex.isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id_assoc]
  refine (cancel_epi (HomologicalComplex.pOpcycles
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) 0)).1 ?_
  rw [← Category.assoc, HomologicalComplex.p_opcyclesMap, Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero', ← Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  simp only [NatTrans.mapHomologicalComplex_app_f]
  exact (α.naturality (P.π.f 0)).symm

set_option backward.isDefEq.respectTransparency false in


/-- Constructs an isomorphism between the middle objects of an exact five-arrow diagram with zero outer objects. -/
noncomputable def exactFiveIso
    {D : Type*} [Category D] [Abelian D] {W : ComposableArrows D 5}
    (hW : W.Exact) (h1 : IsZero (W.obj 1)) (h4 : IsZero (W.obj 4)) :
    W.obj 2 ≅ W.obj 3 := by
  let g : W.obj 2 ⟶ W.obj 3 := W.map' 2 3
  haveI : Mono g := (hW.exact' 1 2 3).mono_g (h1.eq_of_src _ _)
  haveI : Epi g := (hW.exact' 2 3 4).epi_f (h4.eq_of_tgt _ _)
  haveI : IsIso g := isIso_of_mono_of_epi _
  exact asIso g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in


/-- States naturality of the degree-zero comparison isomorphism with respect to a morphism. -/
lemma leftDerivedZeroIso_naturality
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N 0).map f ≫ (leftDerivedZeroIso A N M').hom
      = (leftDerivedZeroIso A N M).hom
        ≫ (NatTrans.leftDerived (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A f) 0).app (ModuleCat.of A N) := by
  have hmap : (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A f).app (ModuleCat.of A N)
      = (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).map f := rfl
  have hnat := leftDerivedZero_naturality (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A f) (ModuleCat.of A N)
  rw [hmap] at hnat
  have hα : (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N 0).map f
        ≫ ((RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf.app M').hom
      = ((RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf.app M).hom
        ≫ (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).map f :=
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf.hom.naturality f
  have hβ : (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).map f
        ≫ ((RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M').leftDerivedZeroIsoSelf.app (ModuleCat.of A N)).inv
      = ((RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M).leftDerivedZeroIsoSelf.app (ModuleCat.of A N)).inv
        ≫ (NatTrans.leftDerived (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A f) 0).app (ModuleCat.of A N) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hnat.symm
  simp only [leftDerivedZeroIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hα, Category.assoc, hβ]

end BalancingIV


/-- Exhibits an isomorphism between the displayed object and a left-derived functor value. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
theorem AuxiliaryLeftDerivedIso
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) :
    Nonempty (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A N M n ≅
      (Functor.leftDerived (RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M) n).obj (ModuleCat.of A N)) := by
  induction n generalizing M with
  | zero => exact ⟨leftDerivedZeroIso A N M⟩
  | succ k IH =>
    obtain ⟨pp⟩ := CategoryTheory.EnoughProjectives.presentation M
    set SC : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) :=
      ShortComplex.mk (Limits.kernel.ι pp.f) pp.f (by simp) with hSC
    have hSE : SC.ShortExact := { exact := ShortComplex.exact_kernel pp.f }
    haveI : CategoryTheory.Projective SC.X₂ := pp.projective
    obtain ⟨δT, hT⟩ :=
      RepresentationTheory.CategoryPair.AssociatedType.exists_connectingMorphism_exact (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) hSE k (k + 1) rfl
    obtain ⟨δB, hB⟩ := AuxiliaryLeftDerivedExactSequence A N hSE k (k + 1) rfl
    obtain _ | j := k
    ·
      set a := (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N 0).map SC.f with ha
      set b := (NatTrans.leftDerived (RepresentationTheory.ModulePairing.Projective.ModulePairing.Auxiliary.moduleFunctorMap A SC.f) 0).app (ModuleCat.of A N) with hb
      have hcompT : δT ≫ a = 0 := hT.toIsComplex.zero' 2 3 4
      have hcompB : δB ≫ b = 0 := hB.toIsComplex.zero' 2 3 4
      haveI hmonoT : Mono δT := (hT.exact' 1 2 3).mono_g
        ((Functor.isZero_leftDerived_obj_projective_succ
          (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) 0 SC.X₂).eq_of_src _ _)
      haveI hmonoB : Mono δB := (hB.exact' 1 2 3).mono_g
        ((RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_leftDerived_succ_isZero A SC.X₂ N 0).eq_of_src _ _)
      let ST : ShortComplex AddCommGrpCat.{u} := ShortComplex.mk δT a hcompT
      let SB : ShortComplex AddCommGrpCat.{u} := ShortComplex.mk δB b hcompB
      have hExT : ST.Exact := hT.exact' 2 3 4
      have hExB : SB.Exact := hB.exact' 2 3 4
      haveI : Mono ST.f := hmonoT
      haveI : Mono SB.f := hmonoB
      have isoTor := Limits.IsLimit.conePointUniqueUpToIso hExT.fIsKernel (Limits.kernelIsKernel a)
      have isoB := Limits.IsLimit.conePointUniqueUpToIso hExB.fIsKernel (Limits.kernelIsKernel b)
      have hsq : a ≫ (leftDerivedZeroIso A N SC.X₂).hom
          = (leftDerivedZeroIso A N SC.X₁).hom ≫ b := leftDerivedZeroIso_naturality A N SC.f
      exact ⟨isoTor.trans ((Limits.kernel.mapIso a b (leftDerivedZeroIso A N SC.X₁)
        (leftDerivedZeroIso A N SC.X₂) hsq).trans isoB.symm)⟩
    ·
      exact ⟨(exactFiveIso hT
          (Functor.isZero_leftDerived_obj_projective_succ (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) (j + 1) SC.X₂)
          (Functor.isZero_leftDerived_obj_projective_succ (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) j SC.X₂)).trans
        (((IH SC.X₁).some).trans
          (exactFiveIso hB
            (RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_leftDerived_succ_isZero A SC.X₂ N (j + 1))
            (RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_leftDerived_succ_isZero A SC.X₂ N j)).symm)⟩


/-- Shows that the contravariant sequence associated to a short exact complex is exact at adjacent indices. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
theorem contravariantSequence_exact
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Abelian.Ext.contravariantSequence hS N n₀ n₁ h).Exact :=
  Abelian.Ext.contravariantSequence_exact hS N n₀ n₁ h


/-- Obtains an exact five-arrow sequence from a short exact complex using the displayed functors. -/
@[source_ref "Chapter8/Problem8.2.6" (role := supporting)]
theorem AuxiliaryContravariantExactSequence
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n₁).obj S.X₃ ⟶ (RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n₀).obj S.X₁,
      (ComposableArrows.mk₅
        ((RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n₁).map S.f) ((RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n₁).map S.g)
        δ
        ((RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n₀).map S.f) ((RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n₀).map S.g)).Exact := by
  exact RepresentationTheory.CategoryPair.AssociatedType.exists_connectingMorphism_exact (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) hS n₀ n₁ h

end RepresentationTheory.DerivedFunctorExactness

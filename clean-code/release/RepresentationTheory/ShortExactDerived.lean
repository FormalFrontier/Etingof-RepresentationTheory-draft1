/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.DerivedFunctorExactness
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-! # Short Exact Derived -/

namespace RepresentationTheory.ShortExactDerived

open _root_.CategoryTheory

universe u

/-- An auxiliary inductive object parameterized by three indexed additive families. -/
structure Auxiliary
    (T1 T2 T3 : ℕ → AddCommGrpCat.{u}) where
  /-- Returns the degreewise map from the first family to the second family. -/
  firstToSecond : ∀ n, T1 n ⟶ T2 n
  /-- Returns the degreewise map from the second family to the third family. -/
  secondToThird : ∀ n, T2 n ⟶ T3 n
  /-- Returns the map from the third family at degree n to the first family at the succeeding degree. -/
  toFirstSucc : ∀ n, T3 n ⟶ T1 (n + 1)
  /-- The five displayed consecutive maps satisfy the given exactness condition. -/
  fiveTermExact : ∀ n,
    (ComposableArrows.mk₅ (firstToSecond n) (secondToThird n) (toFirstSucc n)
      (firstToSecond (n + 1)) (secondToThird (n + 1))).Exact

/-- An auxiliary inductive object parameterized by three indexed additive families. -/
structure Auxiliary2
    (T1 T2 T3 : ℕ → AddCommGrpCat.{u}) where
  /-- Returns the degreewise map from the first family to the second family. -/
  firstToSecond : ∀ n, T1 n ⟶ T2 n
  /-- Returns the degreewise map from the second family to the third family. -/
  secondToThird : ∀ n, T2 n ⟶ T3 n
  /-- Returns the map from the next third-family term to the current first-family term. -/
  succToFirst : ∀ n, T3 (n + 1) ⟶ T1 n
  /-- The five displayed consecutive maps satisfy the given exactness condition. -/
  fiveTermExact : ∀ n,
    (ComposableArrows.mk₅ (firstToSecond (n + 1)) (secondToThird (n + 1)) (succToFirst n)
      (firstToSecond n) (secondToThird n)).Exact

/-! ## Ext in the second argument -/

/-- Constructs the connecting morphism between the displayed indexed additive objects. -/
noncomputable def connectingMap
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses M S.X₃ n) ⟶
      AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses M S.X₁ (n + 1)) :=
  AddCommGrpCat.ofHom (hS.extClass.postcomp M rfl)

/-- Packages the three displayed indexed constructions into an auxiliary exactness object. -/
noncomputable def exactData
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Auxiliary
      (fun n => AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses M S.X₁ n))
      (fun n => AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses M S.X₂ n))
      (fun n => AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses M S.X₃ n)) where
  firstToSecond n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.f).postcomp M (add_zero n))
  secondToThird n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.g).postcomp M (add_zero n))
  toFirstSucc := connectingMap A M hS
  fiveTermExact n := by
    simpa [Abelian.Ext.covariantSequence, connectingMap] using
      Abelian.Ext.covariantSequence_exact M hS n (n + 1) rfl

/-- The displayed postcomposition morphism is monic for a short exact complex. -/
theorem postcompMono
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Mono (AddCommGrpCat.ofHom
      ((Abelian.Ext.mk₀ S.f).postcomp M (add_zero 0))) := by
  letI : Mono S.f := hS.mono_f
  exact Abelian.Ext.mono_postcomp_mk₀_of_mono M S.f

/-- Evaluation of the postcomposition additive equivalence agrees with composition by the first map. -/
theorem postcompAsCompose
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (φ : M ⟶ S.X₁) :
    Abelian.Ext.addEquiv₀
      (((Abelian.Ext.mk₀ S.f).postcomp M (add_zero 0))
        (Abelian.Ext.addEquiv₀.symm φ)) = φ ≫ S.f := by
  simp only [Abelian.Ext.addEquiv₀_symm_apply, AddMonoidHom.flip_apply,
    Abelian.Ext.bilinearComp_apply_apply, Abelian.Ext.mk₀_comp_mk₀]
  change Abelian.Ext.addEquiv₀ (Abelian.Ext.addEquiv₀.symm (φ ≫ S.f)) = _
  exact Abelian.Ext.addEquiv₀.apply_symm_apply _

/-- A short exact complex yields exactness for the displayed postcomposition construction. -/
theorem postcompExact
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (ShortComplex.mk
      (0 : AddCommGrpCat.of PUnit ⟶ AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses M S.X₁ 0))
      (AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.f).postcomp M (add_zero 0)))
      (by simp)).Exact := by
  letI := postcompMono A M hS
  apply (ShortComplex.exact_iff_mono _ rfl).2
  infer_instance

/-! ## Ext in the first argument -/

/-- Constructs the connecting morphism for the displayed module-valued indexed objects. -/
noncomputable def moduleConnectingMap
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses S.X₁ N n) ⟶
      AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses S.X₃ N (n + 1)) :=
  AddCommGrpCat.ofHom (hS.extClass.precomp N (Nat.one_add n))

/-- Packages the displayed reversed module-valued constructions into an auxiliary exactness object. -/
noncomputable def moduleExactData
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Auxiliary
      (fun n => AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses S.X₃ N n))
      (fun n => AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses S.X₂ N n))
      (fun n => AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses S.X₁ N n)) where
  firstToSecond n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.g).precomp N (zero_add n))
  secondToThird n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.f).precomp N (zero_add n))
  toFirstSucc := moduleConnectingMap A N hS
  fiveTermExact n := by
    simpa [Abelian.Ext.contravariantSequence, moduleConnectingMap] using
      Abelian.Ext.contravariantSequence_exact hS N n (n + 1) (Nat.one_add n)

/-- The displayed precomposition morphism is monic for a short exact complex. -/
theorem precompMono
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Mono (AddCommGrpCat.ofHom
      ((Abelian.Ext.mk₀ S.g).precomp N (zero_add 0))) := by
  letI : Epi S.g := hS.epi_g
  exact Abelian.Ext.mono_precomp_mk₀_of_epi N S.g

/-- Evaluation of the precomposition additive equivalence agrees with composition by the second map. -/
theorem precompAsCompose
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (φ : S.X₃ ⟶ N) :
    Abelian.Ext.addEquiv₀
      (((Abelian.Ext.mk₀ S.g).precomp N (zero_add 0))
        (Abelian.Ext.addEquiv₀.symm φ)) = S.g ≫ φ := by
  simp only [Abelian.Ext.addEquiv₀_symm_apply, Abelian.Ext.bilinearComp_apply_apply,
    Abelian.Ext.mk₀_comp_mk₀]
  change Abelian.Ext.addEquiv₀ (Abelian.Ext.addEquiv₀.symm (S.g ≫ φ)) = _
  exact Abelian.Ext.addEquiv₀.apply_symm_apply _

/-- A short exact complex gives exactness for the displayed precomposition construction. -/
theorem precompExact
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (ShortComplex.mk
      (0 : AddCommGrpCat.of PUnit ⟶ AddCommGrpCat.of (_root_.RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses S.X₃ N 0))
      (AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.g).precomp N (zero_add 0)))
      (by simp)).Exact := by
  letI := precompMono A N hS
  apply (ShortComplex.exact_iff_mono _ rfl).2
  infer_instance

/-! ## Tor in the second argument -/

/-- An auxiliary copy of the oppositely directed connecting morphism. -/
noncomputable def auxiliaryOppositeConnectingMap
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₃ M (n + 1) ⟶ _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₁ M n :=
  _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism
    (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.f.hom) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom)
    (_root_.RepresentationTheory.DerivedFunctorExactness.AuxiliaryShortComplexHom_comp A)
    (fun Y _ => _root_.RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_map_shortExact A Y hS) M n (n + 1) rfl

/-- The opposite auxiliary connecting morphism is natural in a module morphism. -/
theorem auxiliaryOppositeNaturality
    (A : Type u) [Ring A] {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    auxiliaryOppositeConnectingMap A M hS n ≫ (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A S.X₁ n).map f =
      (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A S.X₃ (n + 1)).map f ≫ auxiliaryOppositeConnectingMap A M' hS n := by
  simpa [auxiliaryOppositeConnectingMap, _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor] using
    _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism_naturality_object
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.f.hom) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom)
      (_root_.RepresentationTheory.DerivedFunctorExactness.AuxiliaryShortComplexHom_comp A)
      (fun Y _ => _root_.RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_map_shortExact A Y hS) f n (n + 1) rfl

/-- The opposite auxiliary connecting morphism is natural in a morphism of short complexes. -/
theorem auxiliaryOppositeNaturalityInComplex
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S T : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A φ.τ₃.hom (n + 1) M ≫ auxiliaryOppositeConnectingMap A M hT n =
      auxiliaryOppositeConnectingMap A M hS n ≫ _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A φ.τ₁.hom n M := by
  have comm₁₂ :
      _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A φ.τ₁.hom ≫ _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A T.f.hom =
        _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.f.hom ≫ _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A φ.τ₂.hom := by
    change (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map φ.τ₁ ≫
        (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map T.f =
      (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map S.f ≫ (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map φ.τ₂
    rw [← Functor.map_comp, φ.comm₁₂, Functor.map_comp]
  have comm₂₃ :
      _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A φ.τ₂.hom ≫ _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A T.g.hom =
        _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom ≫ _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A φ.τ₃.hom := by
    change (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map φ.τ₂ ≫
        (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map T.g =
      (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map S.g ≫ (_root_.RepresentationTheory.ModuleCategoryTensorFinsupp.auxiliaryModuleToAddCommGrpFunctor A).map φ.τ₃
    rw [← Functor.map_comp, φ.comm₂₃, Functor.map_comp]
  simpa [auxiliaryOppositeConnectingMap, _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom] using
    _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism_naturality_functorComplex
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.f.hom) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom)
      (_root_.RepresentationTheory.DerivedFunctorExactness.AuxiliaryShortComplexHom_comp A)
      (fun Y _ => _root_.RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_map_shortExact A Y hS)
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A T.f.hom) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A T.g.hom)
      (_root_.RepresentationTheory.DerivedFunctorExactness.AuxiliaryShortComplexHom_comp A)
      (fun Y _ => _root_.RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_map_shortExact A Y hT)
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A φ.τ₁.hom) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A φ.τ₂.hom)
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A φ.τ₃.hom) comm₁₂ comm₂₃ M n (n + 1) rfl

/-- Constructs the oppositely directed connecting morphism from the displayed module data. -/
noncomputable def oppositeConnectingMap
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₃ M (n + 1) ⟶ _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₁ M n :=
  auxiliaryOppositeConnectingMap A M hS n

/-- The five displayed maps associated to the opposite construction are exact. -/
theorem oppositeFiveMapExact
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.f.hom (n + 1) M) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom (n + 1) M)
      (oppositeConnectingMap A M hS n)
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.f.hom n M) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom n M)).Exact := by
  simpa [oppositeConnectingMap, auxiliaryOppositeConnectingMap, _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom] using
    _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism_exact
      (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.f.hom) (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom)
      (_root_.RepresentationTheory.DerivedFunctorExactness.AuxiliaryShortComplexHom_comp A)
      (fun Y _ => _root_.RepresentationTheory.ModulePairing.Projective.ModulePairing.projectiveModuleFunctor_map_shortExact A Y hS) M n (n + 1) rfl

/-- Packages the opposite indexed constructions into the reverse auxiliary exactness object. -/
noncomputable def oppositeExactData
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Auxiliary2
      (fun n => _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₁ M n)
      (fun n => _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₂ M n)
      (fun n => _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₃ M n) where
  firstToSecond n := _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.f.hom n M
  secondToThird n := _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom n M
  succToFirst := oppositeConnectingMap A M hS
  fiveTermExact := oppositeFiveMapExact A M hS

/-- The degree-zero comparison is compatible with the second morphism of the short complex. -/
theorem oppositeZeroNaturality
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} :
    _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom 0 M ≫
        ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A S.X₃).leftDerivedZeroIsoSelf.app M).hom =
      ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A S.X₂).leftDerivedZeroIsoSelf.app M).hom ≫
        (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M).map S.g := by
  let F1 := _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A S.X₂
  let F2 := _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A S.X₃
  let α := _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom
  have hα : α.app M = (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M).map S.g := rfl
  simpa [F1, F2, α, hα, _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom] using
    _root_.RepresentationTheory.DerivedFunctorExactness.leftDerivedZero_naturality (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A S.g.hom) M

/-- The indicated degree-zero morphism is epic for a short exact complex. -/
theorem oppositeEpi
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Epi (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom 0 M) := by
  let F1 := _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A S.X₂
  let F2 := _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A S.X₃
  haveI : Epi S.g := hS.epi_g
  haveI : Epi ((_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M).map S.g) :=
    Functor.map_epi (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.rightModuleToAddCommGrpFunctor A M) S.g
  have hnat := oppositeZeroNaturality A M (S := S)
  apply (epi_comp_iff_of_isIso (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom 0 M)
    (F2.leftDerivedZeroIsoSelf.app M).hom).mp
  rw [hnat]
  infer_instance

/-- A short exact complex induces exactness for the displayed opposite construction. -/
theorem oppositeExact
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (ShortComplex.mk (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A S.g.hom 0 M)
      (0 : _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup A S.X₃ M 0 ⟶ AddCommGrpCat.of PUnit) (by simp)).Exact := by
  letI := oppositeEpi A M hS
  apply (ShortComplex.exact_iff_epi _ rfl).2
  infer_instance

/-! ## Tor in the first argument -/

/-- An auxiliary copy of the functor-applied connecting morphism. -/
noncomputable def auxiliaryFunctorConnectingMap
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (n : ℕ) :
    (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N (n + 1)).obj S.X₃ ⟶
      (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).obj S.X₁ :=
  _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) hS n (n + 1) rfl

/-- The auxiliary connecting morphism is natural in a linear map of coefficient objects. -/
theorem auxiliaryConnectingNaturality
    (A : Type u) [Ring A]
    {N N' : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (f : N →ₗ[A] N') {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)}
    (hS : S.ShortExact) (n : ℕ) :
    _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A f (n + 1) S.X₃ ≫ auxiliaryFunctorConnectingMap A N' hS n =
      auxiliaryFunctorConnectingMap A N hS n ≫ _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom A f n S.X₁ := by
  simpa [auxiliaryFunctorConnectingMap, _root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryIndexedHom] using
    _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism_naturality_functor (_root_.RepresentationTheory.Algebra.ModuleCategory.Auxiliary.ModuleCategoryAuxiliary.linearMapToAuxiliaryHom A f) hS n (n + 1) rfl

/-- The auxiliary connecting morphism is natural in a morphism of short complexes. -/
theorem auxiliaryConnectingNaturalityInComplex
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S T : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N (n + 1)).map φ.τ₃ ≫ auxiliaryFunctorConnectingMap A N hT n =
      auxiliaryFunctorConnectingMap A N hS n ≫ (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).map φ.τ₁ := by
  simpa [auxiliaryFunctorConnectingMap, _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor] using
    _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism_naturality_shortComplex
      (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) hS hT φ n (n + 1) rfl

/-- Constructs a connecting morphism after applying the indexed functors to a short exact complex. -/
noncomputable def functorConnectingMap
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (n : ℕ) :
    (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N (n + 1)).obj S.X₃ ⟶
      (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).obj S.X₁ :=
  auxiliaryFunctorConnectingMap A N hS n

/-- The five functor-applied morphisms surrounding the connecting map are exact. -/
theorem functorFiveMapExact
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N (n + 1)).map S.f) ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N (n + 1)).map S.g)
      (functorConnectingMap A N hS n)
      ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).map S.f) ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).map S.g)).Exact := by
  simpa [functorConnectingMap, auxiliaryFunctorConnectingMap, _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor] using
    _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism_exact (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N) hS n (n + 1) rfl

/-- Packages the functor-applied indexed objects into the reverse auxiliary exactness object. -/
noncomputable def functorExactData
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    Auxiliary2
      (fun n => (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).obj S.X₁)
      (fun n => (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).obj S.X₂)
      (fun n => (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).obj S.X₃) where
  firstToSecond n := (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).map S.f
  secondToThird n := (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N n).map S.g
  succToFirst := functorConnectingMap A N hS
  fiveTermExact := functorFiveMapExact A N hS

/-- The degree-zero comparison commutes with the functor image of the second map. -/
theorem functorZeroNaturality
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} :
    (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N 0).map S.g ≫
        ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf.app S.X₃).hom =
      ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf.app S.X₂).hom ≫
        (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).map S.g :=
  (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerivedZeroIsoSelf.hom.naturality S.g

/-- The degree-zero image of the second map is epic under the short exactness assumption. -/
theorem functorEpi
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    Epi ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N 0).map S.g) := by
  change Epi (((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N).leftDerived 0).map S.g)
  let F := _root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor A N
  haveI : Epi S.g := hS.epi_g
  haveI : Epi (F.map S.g) := Functor.map_epi F S.g
  change Epi ((F.leftDerived 0).map S.g)
  apply (epi_comp_iff_of_isIso ((F.leftDerived 0).map S.g)
    (F.leftDerivedZeroIsoSelf.app S.X₃).hom).mp
  change Epi ((F.leftDerived 0).map S.g ≫ F.leftDerivedZeroIsoSelf.hom.app S.X₃)
  rw [F.leftDerivedZeroIsoSelf.hom.naturality S.g]
  infer_instance

/-- The functor-applied degree-zero construction is exact for a short exact complex. -/
theorem functorExact
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    (ShortComplex.mk ((_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N 0).map S.g)
      (0 : (_root_.RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor A N 0).obj S.X₃ ⟶ AddCommGrpCat.of PUnit) (by simp)).Exact := by
  letI := functorEpi A N hS
  apply (ShortComplex.exact_iff_epi _ rfl).2
  infer_instance

end RepresentationTheory.ShortExactDerived

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Homology.ExactSequence

/-! # Connecting morphisms for left-derived functors -/

set_option backward.isDefEq.respectTransparency false


universe v u v' u'

open CategoryTheory Category Limits ComposableArrows

namespace RepresentationTheory.CategoryTheory.LeftDerivedFunctor.ConnectingMorphisms

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]

omit [EnoughProjectives C] in


/-- An additive functor maps a short exact complex of homological complexes to a short exact complex when every component of its third object is projective. -/
lemma CategoryTheory.ShortComplex.ShortExact.mapHomologicalComplex_of_projective_X3 {ι : Type*} {c : ComplexShape ι}
    {SC : ShortComplex (HomologicalComplex C c)} (hSC : SC.ShortExact)
    (hproj : ∀ i, Projective (SC.X₃.X i)) :
    (SC.map (F.mapHomologicalComplex c)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hi : (SC.map (HomologicalComplex.eval C c i)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact SC).mp hSC i
  haveI : Projective ((SC.map (HomologicalComplex.eval C c i)).X₃) := hproj i
  have split : (SC.map (HomologicalComplex.eval C c i)).Splitting :=
    hi.splittingOfProjective
  exact (split.map F).shortExact


/-- The connecting morphism from the left-derived image of the third object in one degree to that of the first object in the adjacent lower degree. -/
noncomputable def _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism
    {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (F.leftDerived n₁).obj S.X₃ ⟶ (F.leftDerived n₀).obj S.X₁ := by
  let P₁ : ProjectiveResolution S.X₁ := projectiveResolution S.X₁
  let P₃ : ProjectiveResolution S.X₃ := projectiveResolution S.X₃
  let SC := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃
  let T := SC.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  have hT : T.ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mapHomologicalComplex_of_projective_X3 F
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hS P₁ P₃) (fun i => P₃.projective i)
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]
    omega
  exact (P₃.isoLeftDerivedObj F n₁).hom ≫ hT.δ n₁ n₀ hij ≫
    (P₁.isoLeftDerivedObj F n₀).inv


/-- Connecting morphisms commute with the maps on left-derived functors induced by a natural transformation of additive functors. -/
theorem _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism_naturality_functor
    {F G : CategoryTheory.Functor C D} [F.Additive] [G.Additive] (η : F ⟶ G)
    {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (NatTrans.leftDerived η n₁).app S.X₃ ≫
        RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism G hS n₀ n₁ h =
      RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism F hS n₀ n₁ h ≫
        (NatTrans.leftDerived η n₀).app S.X₁ := by
  let P₁ : ProjectiveResolution S.X₁ := projectiveResolution S.X₁
  let P₃ : ProjectiveResolution S.X₃ := projectiveResolution S.X₃
  let SC : ShortComplex (ChainComplex C ℕ) := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃
  let TF := SC.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  let TG := SC.map (G.mapHomologicalComplex (ComplexShape.down ℕ))
  have hTF : TF.ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mapHomologicalComplex_of_projective_X3 F
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hS P₁ P₃) (fun i => P₃.projective i)
  have hTG : TG.ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mapHomologicalComplex_of_projective_X3 G
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hS P₁ P₃) (fun i => P₃.projective i)
  let Φ : TF ⟶ TG := ShortComplex.homMk
    ((NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app SC.X₁)
    ((NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app SC.X₂)
    ((NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app SC.X₃)
    (NatTrans.naturality _ SC.f).symm (NatTrans.naturality _ SC.g).symm
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]
    omega
  have hδ := HomologicalComplex.HomologySequence.δ_naturality Φ hTF hTG n₁ n₀ hij
  have hδ' : hTF.δ n₁ n₀ hij ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app P₁.complex) =
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app P₃.complex) ≫
        hTG.δ n₁ n₀ hij := by
    simpa [Φ, TF, TG, SC, RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex] using hδ
  rw [ProjectiveResolution.leftDerived_app_eq η P₃ n₁,
    ProjectiveResolution.leftDerived_app_eq η P₁ n₀]
  dsimp only [RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism]
  simp only [P₁, P₃, Category.assoc, Iso.inv_hom_id_assoc]
  change (P₃.isoLeftDerivedObj F n₁).hom ≫
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map
        ((NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app P₃.complex) ≫
      hTG.δ n₁ n₀ hij ≫ (P₁.isoLeftDerivedObj G n₀).inv =
    (P₃.isoLeftDerivedObj F n₁).hom ≫ hTF.δ n₁ n₀ hij ≫
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map
        ((NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app P₁.complex) ≫
      (P₁.isoLeftDerivedObj G n₀).inv
  simpa only [Category.assoc] using congrArg
    (fun k => (P₃.isoLeftDerivedObj F n₁).hom ≫ k ≫
      (P₁.isoLeftDerivedObj G n₀).inv) hδ'.symm


/-- Connecting morphisms commute with the maps induced by a morphism between short exact complexes. -/
theorem _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism_naturality_shortComplex
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (F.leftDerived n₁).map φ.τ₃ ≫ RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism F hT n₀ n₁ h =
      RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism F hS n₀ n₁ h ≫ (F.leftDerived n₀).map φ.τ₁ := by
  let P₁ : ProjectiveResolution S.X₁ := projectiveResolution S.X₁
  let P₃ : ProjectiveResolution S.X₃ := projectiveResolution S.X₃
  let Q₁ : ProjectiveResolution T.X₁ := projectiveResolution T.X₁
  let Q₃ : ProjectiveResolution T.X₃ := projectiveResolution T.X₃
  let SC : ShortComplex (ChainComplex C ℕ) := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃
  let TC : ShortComplex (ChainComplex C ℕ) := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hT Q₁ Q₃
  let SF := SC.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  let TF := TC.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  have hSF : SF.ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mapHomologicalComplex_of_projective_X3 F
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hS P₁ P₃) (fun i => P₃.projective i)
  have hTF : TF.ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mapHomologicalComplex_of_projective_X3 F
      (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hT Q₁ Q₃) (fun i => Q₃.projective i)
  let ψ : SC ⟶ TC := RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.middleResolutionMap hS hT φ P₁ P₃ Q₁ Q₃
  let Ψ : SF ⟶ TF :=
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).mapShortComplex.map ψ
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]
    omega
  have hδ := HomologicalComplex.HomologySequence.δ_naturality Ψ hSF hTF n₁ n₀ hij
  have hδ' : hSF.δ n₁ n₀ hij ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map
            (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.leftResolutionMap φ P₁ Q₁) =
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map
            (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.rightResolutionMap φ P₃ Q₃) ≫ hTF.δ n₁ n₀ hij := by
    simpa [Ψ, ψ, SF, TF, SC, TC, RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.middleResolutionMap] using hδ
  have comm₁ : (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.leftResolutionMap φ P₁ Q₁).f 0 ≫ Q₁.π.f 0 =
      P₁.π.f 0 ≫ φ.τ₁ := ProjectiveResolution.lift_commutes_zero φ.τ₁ P₁ Q₁
  have comm₃ : (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.rightResolutionMap φ P₃ Q₃).f 0 ≫ Q₃.π.f 0 =
      P₃.π.f 0 ≫ φ.τ₃ := ProjectiveResolution.lift_commutes_zero φ.τ₃ P₃ Q₃
  dsimp only [RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism]
  simp only [Category.assoc]
  rw [ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    φ.τ₁ P₁ Q₁ (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.leftResolutionMap φ P₁ Q₁) comm₁ F n₀]
  rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality_assoc
    φ.τ₃ P₃ Q₃ (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.rightResolutionMap φ P₃ Q₃) comm₃ F n₁]
  change (P₃.isoLeftDerivedObj F n₁).hom ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map
          (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.rightResolutionMap φ P₃ Q₃) ≫ hTF.δ n₁ n₀ hij ≫
      (Q₁.isoLeftDerivedObj F n₀).inv =
    (P₃.isoLeftDerivedObj F n₁).hom ≫ hSF.δ n₁ n₀ hij ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map
          (RepresentationTheory.HomologicalAlgebra.ShortExactProjectiveResolutionComparison.ShortExactProjectiveResolutionComparison.leftResolutionMap φ P₁ Q₁) ≫ (Q₁.isoLeftDerivedObj F n₀).inv
  simpa only [Category.assoc] using congrArg
    (fun k => (P₃.isoLeftDerivedObj F n₁).hom ≫ k ≫
      (Q₁.isoLeftDerivedObj F n₀).inv) hδ'.symm


/-- The five composable arrows formed from the left-derived maps of a short exact complex and its connecting morphism are exact. -/
theorem _root_.RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism_exact
    {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (ComposableArrows.mk₅
      ((F.leftDerived n₁).map S.f) ((F.leftDerived n₁).map S.g)
      (RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism F hS n₀ n₁ h)
      ((F.leftDerived n₀).map S.f) ((F.leftDerived n₀).map S.g)).Exact := by

  let P₁ : ProjectiveResolution S.X₁ := projectiveResolution S.X₁
  let P₃ : ProjectiveResolution S.X₃ := projectiveResolution S.X₃
  let P₂ : ProjectiveResolution S.X₂ := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.middleProjectiveResolution hS P₁ P₃

  let SC : ShortComplex (ChainComplex C ℕ) := RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex hS P₁ P₃
  have hSE : SC.ShortExact := by
    exact RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex_shortExact hS P₁ P₃
  have aug₁ : SC.f.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f := by
    dsimp [SC, P₂, RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex, RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.middleProjectiveResolution]
    simpa only [RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.middleAugmentation_f_zero] using RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.inl_comp_middleAugmentationZero hS P₁ P₃
  have aug₂ : SC.g.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g := by
    dsimp [SC, P₂, RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.resolutionShortComplex, RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.middleProjectiveResolution]
    simpa only [RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.middleAugmentation_f_zero] using (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.ShortExact.CategoryTheory.ShortComplex.ShortExact.middleAugmentationZero_comp_g hS P₁ P₃).symm
  have hT : (SC.map (F.mapHomologicalComplex (ComplexShape.down ℕ))).ShortExact :=
    CategoryTheory.ShortComplex.ShortExact.mapHomologicalComplex_of_projective_X3 F hSE (fun i => P₃.projective i)
  set T := SC.map (F.mapHomologicalComplex (ComplexShape.down ℕ)) with hTdef

  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]; omega
  set δ' := hT.δ n₁ n₀ hij with hδ'

  have hδ : RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism F hS n₀ n₁ h =
      (P₃.isoLeftDerivedObj F n₁).hom ≫ δ' ≫
        (P₁.isoLeftDerivedObj F n₀).inv := by
    simp only [RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism]
    rfl

  set Hrow : ComposableArrows D 5 := ComposableArrows.mk₅
    (HomologicalComplex.homologyMap T.f n₁) (HomologicalComplex.homologyMap T.g n₁)
    δ'
    (HomologicalComplex.homologyMap T.f n₀) (HomologicalComplex.homologyMap T.g n₀) with hHrow

  have hHrowExact : Hrow.Exact := by
    rw [hHrow]
    refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ (exact_of_δ₀ ?_ ?_))
    · exact (hT.homology_exact₂ n₁).exact_toComposableArrows
    · exact (hT.homology_exact₃ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₁ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₂ n₀).exact_toComposableArrows

  have e : ComposableArrows.mk₅
      ((F.leftDerived n₁).map S.f) ((F.leftDerived n₁).map S.g)
      (RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism F hS n₀ n₁ h)
      ((F.leftDerived n₀).map S.f) ((F.leftDerived n₀).map S.g) ≅ Hrow := by
    refine ComposableArrows.isoMk₅
      (P₁.isoLeftDerivedObj F n₁) (P₂.isoLeftDerivedObj F n₁) (P₃.isoLeftDerivedObj F n₁)
      (P₁.isoLeftDerivedObj F n₀) (P₂.isoLeftDerivedObj F n₀) (P₃.isoLeftDerivedObj F n₀)
      ?_ ?_ ?_ ?_ ?_
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.f P₁ P₂ SC.f aug₁ F n₁
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.g P₂ P₃ SC.g aug₂ F n₁
    · rw [hδ]
      change ((P₃.isoLeftDerivedObj F n₁).hom ≫ δ' ≫ (P₁.isoLeftDerivedObj F n₀).inv) ≫
          (P₁.isoLeftDerivedObj F n₀).hom = (P₃.isoLeftDerivedObj F n₁).hom ≫ δ'
      simp
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.f P₁ P₂ SC.f aug₁ F n₀
    · exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.g P₂ P₃ SC.g aug₂ F n₀
  exact (ComposableArrows.exact_iff_of_iso e).mpr hHrowExact


/-- The left-derived images of a short exact complex in adjacent degrees admit a connecting morphism for which the resulting five composable arrows are exact. -/
theorem _root_.RepresentationTheory.CategoryPair.AssociatedType.exists_connectingMorphism_exact
    {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (F.leftDerived n₁).obj S.X₃ ⟶ (F.leftDerived n₀).obj S.X₁,
      (ComposableArrows.mk₅
        ((F.leftDerived n₁).map S.f) ((F.leftDerived n₁).map S.g)
        δ
        ((F.leftDerived n₀).map S.f) ((F.leftDerived n₀).map S.g)).Exact :=
  ⟨RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism F hS n₀ n₁ h,
    RepresentationTheory.CategoryPair.AssociatedType.connectingMorphism_exact F hS n₀ n₁ h⟩


/-- The connecting morphism between adjacent left-derived degrees associated to a composable pair of additive natural transformations that is short exact on projective objects. -/
noncomputable def _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism
    {F₁ F₂ F₃ : CategoryTheory.Functor C D} [F₁.Additive] [F₂.Additive] [F₃.Additive]
    (τ₁ : F₁ ⟶ F₂) (τ₂ : F₂ ⟶ F₃) (w : τ₁ ≫ τ₂ = 0)
    (hSE : ∀ (Y : C) [Projective Y],
      (ShortComplex.mk (τ₁.app Y) (τ₂.app Y)
        (by rw [← NatTrans.comp_app, w]; rfl)).ShortExact)
    (X : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (F₃.leftDerived n₁).obj X ⟶ (F₁.leftDerived n₀).obj X := by
  let P : ProjectiveResolution X := projectiveResolution X
  have w' : (NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, w]
    ext i
    simp [NatTrans.mapHomologicalComplex_app_f]
  let SC : ShortComplex (ChainComplex D ℕ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) w'
  have hT : SC.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact hSE (P.complex.X i)
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]
    omega
  exact (P.isoLeftDerivedObj F₃ n₁).hom ≫ hT.δ n₁ n₀ hij ≫
    (P.isoLeftDerivedObj F₁ n₀).inv


/-- The connecting morphism associated to a projectivewise short exact pair of additive natural transformations is natural in the source object. -/
theorem _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism_naturality_object
    {F₁ F₂ F₃ : CategoryTheory.Functor C D} [F₁.Additive] [F₂.Additive] [F₃.Additive]
    (τ₁ : F₁ ⟶ F₂) (τ₂ : F₂ ⟶ F₃) (w : τ₁ ≫ τ₂ = 0)
    (hSE : ∀ (Z : C) [Projective Z],
      (ShortComplex.mk (τ₁.app Z) (τ₂.app Z)
        (by rw [← NatTrans.comp_app, w]; rfl)).ShortExact)
    {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism τ₁ τ₂ w hSE X n₀ n₁ h ≫
        (F₁.leftDerived n₀).map f =
      (F₃.leftDerived n₁).map f ≫
        RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism τ₁ τ₂ w hSE Y n₀ n₁ h := by
  let P : ProjectiveResolution X := projectiveResolution X
  let Q : ProjectiveResolution Y := projectiveResolution Y
  let φ : P.complex ⟶ Q.complex := ProjectiveResolution.lift f P Q
  have comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
    ProjectiveResolution.lift_commutes_zero f P Q
  have wP : (NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, w]
    ext i
    simp [NatTrans.mapHomologicalComplex_app_f]
  have wQ : (NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app Q.complex ≫
      (NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app Q.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, w]
    ext i
    simp [NatTrans.mapHomologicalComplex_app_f]
  let SP : ShortComplex (ChainComplex D ℕ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) wP
  let SQ : ShortComplex (ChainComplex D ℕ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app Q.complex)
    ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app Q.complex) wQ
  have hSP : SP.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact hSE (P.complex.X i)
  have hSQ : SQ.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact hSE (Q.complex.X i)
  let Φ : SP ⟶ SQ := ShortComplex.homMk
    ((F₁.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)
    ((F₂.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)
    ((F₃.mapHomologicalComplex (ComplexShape.down ℕ)).map φ)
    (NatTrans.mapHomologicalComplex_naturality τ₁ φ)
    (NatTrans.mapHomologicalComplex_naturality τ₂ φ)
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]
    omega
  have hδ := HomologicalComplex.HomologySequence.δ_naturality Φ hSP hSQ n₁ n₀ hij
  have hδ' : hSP.δ n₁ n₀ hij ≫
        (F₁.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map φ =
      (F₃.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map φ ≫
        hSQ.δ n₁ n₀ hij := by
    simpa [Φ] using hδ
  dsimp only [RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism]
  simp only [Category.assoc]
  rw [ProjectiveResolution.isoLeftDerivedObj_inv_naturality f P Q φ comm F₁ n₀]
  rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality_assoc f P Q φ comm F₃ n₁]
  change (P.isoLeftDerivedObj F₃ n₁).hom ≫ hSP.δ n₁ n₀ hij ≫
      (F₁.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map φ ≫
        (Q.isoLeftDerivedObj F₁ n₀).inv =
    (P.isoLeftDerivedObj F₃ n₁).hom ≫
      (F₃.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map φ ≫
      hSQ.δ n₁ n₀ hij ≫ (Q.isoLeftDerivedObj F₁ n₀).inv
  simpa only [Category.assoc] using congrArg
    (fun k => (P.isoLeftDerivedObj F₃ n₁).hom ≫ k ≫
      (Q.isoLeftDerivedObj F₁ n₀).inv) hδ'


/-- Compatible morphisms between two projectivewise short exact pairs of additive natural transformations commute with their connecting morphisms on left-derived functors. -/
theorem _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism_naturality_functorComplex
    {F₁ F₂ F₃ G₁ G₂ G₃ : CategoryTheory.Functor C D}
    [F₁.Additive] [F₂.Additive] [F₃.Additive]
    [G₁.Additive] [G₂.Additive] [G₃.Additive]
    (τ₁ : F₁ ⟶ F₂) (τ₂ : F₂ ⟶ F₃) (wF : τ₁ ≫ τ₂ = 0)
    (hF : ∀ (Z : C) [Projective Z],
      (ShortComplex.mk (τ₁.app Z) (τ₂.app Z)
        (by rw [← NatTrans.comp_app, wF]; rfl)).ShortExact)
    (σ₁ : G₁ ⟶ G₂) (σ₂ : G₂ ⟶ G₃) (wG : σ₁ ≫ σ₂ = 0)
    (hG : ∀ (Z : C) [Projective Z],
      (ShortComplex.mk (σ₁.app Z) (σ₂.app Z)
        (by rw [← NatTrans.comp_app, wG]; rfl)).ShortExact)
    (η₁ : F₁ ⟶ G₁) (η₂ : F₂ ⟶ G₂) (η₃ : F₃ ⟶ G₃)
    (comm₁₂ : η₁ ≫ σ₁ = τ₁ ≫ η₂) (comm₂₃ : η₂ ≫ σ₂ = τ₂ ≫ η₃)
    (X : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (NatTrans.leftDerived η₃ n₁).app X ≫
        RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism σ₁ σ₂ wG hG X n₀ n₁ h =
      RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism τ₁ τ₂ wF hF X n₀ n₁ h ≫
        (NatTrans.leftDerived η₁ n₀).app X := by
  let P : ProjectiveResolution X := projectiveResolution X
  have wFP : (NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, wF]
    ext i
    simp [NatTrans.mapHomologicalComplex_app_f]
  have wGP : (NatTrans.mapHomologicalComplex σ₁ (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex σ₂ (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, wG]
    ext i
    simp [NatTrans.mapHomologicalComplex_app_f]
  let SF : ShortComplex (ChainComplex D ℕ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) wFP
  let SG : ShortComplex (ChainComplex D ℕ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex σ₁ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex σ₂ (ComplexShape.down ℕ)).app P.complex) wGP
  have hSF : SF.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact hF (P.complex.X i)
  have hSG : SG.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact hG (P.complex.X i)
  have comm₁₂P :
      (NatTrans.mapHomologicalComplex η₁ (ComplexShape.down ℕ)).app P.complex ≫ SG.f =
        SF.f ≫ (NatTrans.mapHomologicalComplex η₂
          (ComplexShape.down ℕ)).app P.complex := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, comm₁₂,
      NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]
  have comm₂₃P :
      (NatTrans.mapHomologicalComplex η₂ (ComplexShape.down ℕ)).app P.complex ≫ SG.g =
        SF.g ≫ (NatTrans.mapHomologicalComplex η₃
          (ComplexShape.down ℕ)).app P.complex := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, comm₂₃,
      NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]
  let Φ : SF ⟶ SG := ShortComplex.homMk
    ((NatTrans.mapHomologicalComplex η₁ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex η₂ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex η₃ (ComplexShape.down ℕ)).app P.complex)
    comm₁₂P comm₂₃P
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by
    simp only [ComplexShape.down_Rel]
    omega
  have hδ := HomologicalComplex.HomologySequence.δ_naturality Φ hSF hSG n₁ n₀ hij
  have hδ' : hSF.δ n₁ n₀ hij ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map
          ((NatTrans.mapHomologicalComplex η₁ (ComplexShape.down ℕ)).app P.complex) =
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map
          ((NatTrans.mapHomologicalComplex η₃ (ComplexShape.down ℕ)).app P.complex) ≫
        hSG.δ n₁ n₀ hij := by
    simpa [Φ] using hδ
  rw [ProjectiveResolution.leftDerived_app_eq η₃ P n₁,
    ProjectiveResolution.leftDerived_app_eq η₁ P n₀]
  dsimp only [RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism]
  simp only [P, Category.assoc, Iso.inv_hom_id_assoc]
  change (P.isoLeftDerivedObj F₃ n₁).hom ≫
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₁).map
        ((NatTrans.mapHomologicalComplex η₃ (ComplexShape.down ℕ)).app P.complex) ≫
      hSG.δ n₁ n₀ hij ≫ (P.isoLeftDerivedObj G₁ n₀).inv =
    (P.isoLeftDerivedObj F₃ n₁).hom ≫ hSF.δ n₁ n₀ hij ≫
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n₀).map
        ((NatTrans.mapHomologicalComplex η₁ (ComplexShape.down ℕ)).app P.complex) ≫
      (P.isoLeftDerivedObj G₁ n₀).inv
  simpa only [Category.assoc] using congrArg
    (fun k => (P.isoLeftDerivedObj F₃ n₁).hom ≫ k ≫
      (P.isoLeftDerivedObj G₁ n₀).inv) hδ'.symm


/-- The left-derived maps of a projectivewise short exact pair of additive natural transformations, together with its connecting morphism, form an exact sequence in adjacent degrees. -/
theorem _root_.RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism_exact
    {F₁ F₂ F₃ : C ⥤ D} [F₁.Additive] [F₂.Additive] [F₃.Additive]
    (τ₁ : F₁ ⟶ F₂) (τ₂ : F₂ ⟶ F₃) (w : τ₁ ≫ τ₂ = 0)
    (hSE : ∀ (Y : C) [Projective Y],
      (ShortComplex.mk (τ₁.app Y) (τ₂.app Y)
        (by rw [← NatTrans.comp_app, w]; rfl)).ShortExact)
    (X : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (ComposableArrows.mk₅
      ((NatTrans.leftDerived τ₁ n₁).app X) ((NatTrans.leftDerived τ₂ n₁).app X)
      (RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism τ₁ τ₂ w hSE X n₀ n₁ h)
      ((NatTrans.leftDerived τ₁ n₀).app X) ((NatTrans.leftDerived τ₂ n₀).app X)).Exact := by

  set P : ProjectiveResolution X := projectiveResolution X with hP

  have w' : (NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, w]
    ext i
    simp [NatTrans.mapHomologicalComplex_app_f]
  set SC : ShortComplex (ChainComplex D ℕ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) w' with hSCdef
  have hij : (ComplexShape.down ℕ).Rel n₁ n₀ := by simp only [ComplexShape.down_Rel]; omega

  have hT : SC.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact hSE (P.complex.X i)
  set δ' := hT.δ n₁ n₀ hij with hδ'
  have hδ : RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism τ₁ τ₂ w hSE X n₀ n₁ h =
      (P.isoLeftDerivedObj F₃ n₁).hom ≫ δ' ≫
        (P.isoLeftDerivedObj F₁ n₀).inv := by
    simp only [RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism]
    rfl

  set Hrow : ComposableArrows D 5 := ComposableArrows.mk₅
    (HomologicalComplex.homologyMap SC.f n₁) (HomologicalComplex.homologyMap SC.g n₁)
    δ'
    (HomologicalComplex.homologyMap SC.f n₀) (HomologicalComplex.homologyMap SC.g n₀) with hHrow
  have hHrowExact : Hrow.Exact := by
    rw [hHrow]
    refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ (exact_of_δ₀ ?_ ?_))
    · exact (hT.homology_exact₂ n₁).exact_toComposableArrows
    · exact (hT.homology_exact₃ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₁ n₁ n₀ hij).exact_toComposableArrows
    · exact (hT.homology_exact₂ n₀).exact_toComposableArrows

  have e : ComposableArrows.mk₅
      ((NatTrans.leftDerived τ₁ n₁).app X) ((NatTrans.leftDerived τ₂ n₁).app X)
      (RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism τ₁ τ₂ w hSE X n₀ n₁ h)
      ((NatTrans.leftDerived τ₁ n₀).app X) ((NatTrans.leftDerived τ₂ n₀).app X) ≅ Hrow := by
    refine ComposableArrows.isoMk₅
      (P.isoLeftDerivedObj F₁ n₁) (P.isoLeftDerivedObj F₂ n₁) (P.isoLeftDerivedObj F₃ n₁)
      (P.isoLeftDerivedObj F₁ n₀) (P.isoLeftDerivedObj F₂ n₀) (P.isoLeftDerivedObj F₃ n₀)
      ?_ ?_ ?_ ?_ ?_
    · change (NatTrans.leftDerived τ₁ n₁).app X ≫ (P.isoLeftDerivedObj F₂ n₁).hom =
        (P.isoLeftDerivedObj F₁ n₁).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex) n₁
      rw [ProjectiveResolution.leftDerived_app_eq τ₁ P n₁]; simp
    · change (NatTrans.leftDerived τ₂ n₁).app X ≫ (P.isoLeftDerivedObj F₃ n₁).hom =
        (P.isoLeftDerivedObj F₂ n₁).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) n₁
      rw [ProjectiveResolution.leftDerived_app_eq τ₂ P n₁]; simp
    · rw [hδ]
      change ((P.isoLeftDerivedObj F₃ n₁).hom ≫ δ' ≫ (P.isoLeftDerivedObj F₁ n₀).inv) ≫
          (P.isoLeftDerivedObj F₁ n₀).hom = (P.isoLeftDerivedObj F₃ n₁).hom ≫ δ'
      simp
    · change (NatTrans.leftDerived τ₁ n₀).app X ≫ (P.isoLeftDerivedObj F₂ n₀).hom =
        (P.isoLeftDerivedObj F₁ n₀).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₁ (ComplexShape.down ℕ)).app P.complex) n₀
      rw [ProjectiveResolution.leftDerived_app_eq τ₁ P n₀]; simp
    · change (NatTrans.leftDerived τ₂ n₀).app X ≫ (P.isoLeftDerivedObj F₃ n₀).hom =
        (P.isoLeftDerivedObj F₂ n₀).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ₂ (ComplexShape.down ℕ)).app P.complex) n₀
      rw [ProjectiveResolution.leftDerived_app_eq τ₂ P n₀]; simp
  exact (ComposableArrows.exact_iff_of_iso e).mpr hHrowExact


/-- A composable pair of additive natural transformations that is short exact on projective objects induces, in adjacent degrees, a connecting morphism completing an exact sequence of left-derived maps. -/
theorem _root_.RepresentationTheory.FunctorPairConstructions.associatedType.exists_derivedConnectingMorphism_exact
    {F₁ F₂ F₃ : CategoryTheory.Functor C D} [F₁.Additive] [F₂.Additive] [F₃.Additive]
    (τ₁ : F₁ ⟶ F₂) (τ₂ : F₂ ⟶ F₃) (w : τ₁ ≫ τ₂ = 0)
    (hSE : ∀ (Y : C) [Projective Y],
      (ShortComplex.mk (τ₁.app Y) (τ₂.app Y)
        (by rw [← NatTrans.comp_app, w]; rfl)).ShortExact)
    (X : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ δ : (F₃.leftDerived n₁).obj X ⟶ (F₁.leftDerived n₀).obj X,
      (ComposableArrows.mk₅
        ((NatTrans.leftDerived τ₁ n₁).app X) ((NatTrans.leftDerived τ₂ n₁).app X)
        δ
        ((NatTrans.leftDerived τ₁ n₀).app X) ((NatTrans.leftDerived τ₂ n₀).app X)).Exact :=
  ⟨RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism τ₁ τ₂ w hSE X n₀ n₁ h,
    RepresentationTheory.FunctorPairConstructions.associatedType.derivedConnectingMorphism_exact τ₁ τ₂ w hSE X n₀ n₁ h⟩

end RepresentationTheory.CategoryTheory.LeftDerivedFunctor.ConnectingMorphisms


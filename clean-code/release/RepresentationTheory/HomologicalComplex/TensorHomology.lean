/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.HomologicalAlgebra.TensorProductHomology
import RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex
import RepresentationTheory.Alignment.Attribute

/-!
# Tensor-product homology

This module proves that the natural map from the graded sum of tensor products of homology
objects to the homology of the tensor-product complex is an isomorphism over a field.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open RepresentationTheory.HomologicalAlgebra.TensorProductHomology
open RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex
open RepresentationTheory.Mathlib.Algebra.Homology.CochainComplex.Monoidal.CochainComplex

set_option backward.isDefEq.respectTransparency false

namespace RepresentationTheory.HomologicalComplex.TensorHomology

universe u

variable {k : Type u} [Field k]

section ZeroDifferential

variable (C D : CochainComplex (ModuleCat.{u} k) ℤ)

/-- Provides the homology isomorphism from the displayed transformed complex to the original complex. -/
noncomputable def transformedHomologyIso (j : ℤ) :
    (homologyComplex C).homology j ≅ C.homology j :=
  ((homologyComplex C).isoHomologyπ (j - 1) j (by simp) rfl).symm ≪≫
    (homologyComplex C).iCyclesIso j (j + 1) (by simp) rfl

/-- Computes the homology projection after the transformed-homology isomorphism. -/
@[reassoc (attr := simp)]
lemma homologyPi_comp_transformedHomologyIso_hom (j : ℤ) :
    (homologyComplex C).homologyπ j ≫ (transformedHomologyIso C j).hom
      = (homologyComplex C).iCycles j := by
  simp [transformedHomologyIso]

/-- Reassociates the projection formula for the transformed-homology isomorphism with a following morphism. -/
add_decl_doc homologyPi_comp_transformedHomologyIso_hom_assoc

/-- At each integer degree, the tensor product component of the transformed complexes is isomorphic to its homology in that degree. -/
noncomputable def tensorTransformedXHomologyIso (i : ℤ) :
    (HomologicalComplex.tensorObj (homologyComplex C) (homologyComplex D)).X i ≅
      (HomologicalComplex.tensorObj (homologyComplex C) (homologyComplex D)).homology i :=
  ((HomologicalComplex.tensorObj (homologyComplex C) (homologyComplex D)).iCyclesIso i
      (i + 1) (by simp) (tensorObj_homologyComplex_d C D i (i + 1))).symm ≪≫
    (HomologicalComplex.tensorObj (homologyComplex C) (homologyComplex D)).isoHomologyπ
      (i - 1) i (by simp) (tensorObj_homologyComplex_d C D (i - 1) i)

/-- Relates the displayed homology comparison isomorphism to the comparison obtained after transforming both complexes. -/
lemma homologyComparison_eq (i : ℤ) :
    homologyTensorProductHomologyIso C D i =
      (tensorTransformedXHomologyIso C D i).symm ≪≫
        tensorObjXIsoSigma (homologyComplex C) (homologyComplex D) i :=
  rfl

/-- Computes the indicated tensor map on transformed complexes using the homology isomorphisms. -/
lemma transformedTensorMap_eq (j m : ℤ) :
    homologyTensorHomologyToTensorHomology (homologyComplex C) (homologyComplex D) j m
      = ((transformedHomologyIso C j).hom ⊗ₘ
            (transformedHomologyIso D m).hom) ≫
        HomologicalComplex.ιTensorObj (homologyComplex C) (homologyComplex D) j m
          (j + m) rfl ≫
        (tensorTransformedXHomologyIso C D (j + m)).hom := by
  have key : ((homologyComplex C).iCycles j ⊗ₘ (homologyComplex D).iCycles m) ≫
      HomologicalComplex.ιTensorObj (homologyComplex C) (homologyComplex D) j m
        (j + m) rfl ≫
      (tensorTransformedXHomologyIso C D (j + m)).hom
      = cyclesTensorCyclesToTensorHomology (homologyComplex C) (homologyComplex D) j m := by
    rw [← Category.assoc, ← cyclesTensorCyclesToTensorComponent,
      ← cyclesTensorCyclesToTensorCycles_comp_iCycles, cyclesTensorCyclesToTensorHomology,
      Category.assoc]
    congr 1
    rw [tensorTransformedXHomologyIso]
    simp
  rw [← cancel_epi ((homologyComplex C).homologyπ j ⊗ₘ (homologyComplex D).homologyπ m),
    tensorHomologyProjections_comp_homologyTensorHomologyToTensorHomology]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    homologyPi_comp_transformedHomologyIso_hom]
  simp only [Category.assoc]
  exact key.symm

/-- Expresses the tensor-homology map on transformed complexes through the displayed componentwise comparison. -/
lemma transformedHomologyTensorMap_eq (i : ℤ) :
    totalHomologyTensorToTensorHomology (homologyComplex C) (homologyComplex D) i
      = (Sigma.mapIso (fun p : TotalDegreeIndex i =>
            tensorIso (transformedHomologyIso C p.1.1)
              (transformedHomologyIso D p.1.2))).hom ≫
        (homologyTensorProductHomologyIso C D i).inv := by
  refine Sigma.hom_ext _ _ ?_
  rintro ⟨⟨j, m⟩, rfl⟩
  have hι : ∀ {W : ModuleCat.{u} k}
      (f : (HomologicalComplex.tensorObj (homologyComplex C)
        (homologyComplex D)).X (j + m) ⟶ W),
      Sigma.ι (fun p : TotalDegreeIndex (j + m) => C.homology p.1.1 ⊗ D.homology p.1.2)
          ⟨(j, m), rfl⟩ ≫
        (tensorObjXIsoSigma (homologyComplex C) (homologyComplex D) (j + m)).inv ≫ f
      = HomologicalComplex.ιTensorObj (homologyComplex C) (homologyComplex D) j m
          (j + m) rfl ≫ f := by
    intro W f
    rw [← Category.assoc]
    congr 1
    exact Sigma.ι_desc _ _
  rw [sigmaInclusion_pair_comp_totalHomologyTensorToTensorHomology, transformedTensorMap_eq,
    homologyComparison_eq]
  simp only [Iso.trans_inv, Iso.symm_inv, Sigma.ι_mapIso_hom_assoc, tensorIso_hom, hι]

/-- Shows that the tensor-product homology map is invertible after transforming both input complexes. -/
instance isIso_transformedHomologyTensorMap (i : ℤ) :
    IsIso (totalHomologyTensorToTensorHomology (homologyComplex C) (homologyComplex D) i) := by
  rw [transformedHomologyTensorMap_eq]
  infer_instance

end ZeroDifferential

section HomotopyEquivalence

/-- Identifies the tensor product of two complex morphisms with the associated bifunctorial map. -/
lemma tensorHom_eq_mapBifunctorMap {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    (f : C ⟶ C') (g : D ⟶ D') :
    f ⊗ₘ g = HomologicalComplex.mapBifunctorMap f g (curriedTensor (ModuleCat.{u} k))
      (ComplexShape.up ℤ) :=
  rfl

/-- Tensors homotopies between two pairs of complex morphisms. -/
noncomputable def homotopy_tensorHom {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    {f f' : C ⟶ C'} {g g' : D ⟶ D'} (hf : Homotopy f f') (hg : Homotopy g g') :
    Homotopy (f ⊗ₘ g) (f' ⊗ₘ g') :=
  (Homotopy.ofEq (tensorHom_eq_mapBifunctorMap f g)).trans
    (((HomologicalComplex.mapBifunctorMapHomotopy₁ hf g
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ f' hg
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (tensorHom_eq_mapBifunctorMap f' g').symm))

/-- Provides existence of a homotopy equivalence from the displayed transformed complex to the original complex. -/
lemma nonempty_homotopyEquiv_transformed (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    Nonempty (HomotopyEquiv (homologyComplex C) C) := by
  obtain ⟨E, hE, iso, -⟩ := exists_biprod_inr_comp_iso_inv_homologyMap_isIso C
  obtain ⟨hEH⟩ :=
    RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition.acyclic_homotopy_id_zero E hE
  -- `biprod.fst ≫ biprod.inl` is null-homotopic because `𝟙 E` is.
  have H₁ : Homotopy ((biprod.fst : E ⊞ homologyComplex C ⟶ E) ≫ biprod.inl)
      (0 : E ⊞ homologyComplex C ⟶ E ⊞ homologyComplex C) :=
    (Homotopy.ofEq (by simp)).trans
      (((hEH.compLeft (biprod.fst : E ⊞ homologyComplex C ⟶ E)).compRight
        (biprod.inl : E ⟶ E ⊞ homologyComplex C)).trans (Homotopy.ofEq (by simp)))
  -- hence `𝟙 = biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr` is homotopic to the second
  -- term alone.
  have H₂ : Homotopy (𝟙 (E ⊞ homologyComplex C))
      ((biprod.snd : E ⊞ homologyComplex C ⟶ homologyComplex C) ≫ biprod.inr) :=
    (Homotopy.ofEq biprod.total.symm).trans
      ((H₁.add (Homotopy.refl _)).trans (Homotopy.ofEq (zero_add _)))
  refine ⟨{ hom := biprod.inr ≫ iso.inv
            inv := iso.hom ≫ biprod.snd
            homotopyHomInvId := Homotopy.ofEq ?_
            homotopyInvHomId := ?_ }⟩
  · rw [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd]
  · exact (Homotopy.ofEq (by simp)).trans
      (((H₂.compLeft iso.hom).compRight iso.inv).symm.trans (Homotopy.ofEq (by simp)))

end HomotopyEquivalence

section Reduction

/-- Maps a pair of endomorphisms homotopic to identities to the identity under the sigma homology-tensor functor. -/
lemma sigmaHomologyTensorFunctor_map_eq_id_of_homotopy (i : ℤ)
    {C D : CochainComplex (ModuleCat.{u} k) ℤ}
    {f : C ⟶ C} {g : D ⟶ D} (hf : Homotopy f (𝟙 C)) (hg : Homotopy g (𝟙 D)) :
    (totalHomologyTensorFunctor i).map ((f, g) :
      ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) = 𝟙 _ := by
  have key : (totalHomologyTensorFunctor i).map ((f, g) :
        ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))
      = (totalHomologyTensorFunctor i).map (𝟙 ((C, D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ))) := by
    refine Sigma.hom_ext _ _ fun p => ?_
    rw [sigmaInclusion_naturality, sigmaInclusion_naturality]
    congr 1
    change HomologicalComplex.homologyMap f p.1.1 ⊗ₘ HomologicalComplex.homologyMap g p.1.2
      = HomologicalComplex.homologyMap (𝟙 C) p.1.1 ⊗ₘ
        HomologicalComplex.homologyMap (𝟙 D) p.1.2
    rw [hf.homologyMap_eq, hg.homologyMap_eq]
  rw [key, CategoryTheory.Functor.map_id]

/-- Maps a pair of endomorphisms homotopic to identities to the identity under the homology-tensor functor. -/
lemma homologyTensorFunctor_map_eq_id_of_homotopy (i : ℤ)
    {C D : CochainComplex (ModuleCat.{u} k) ℤ}
    {f : C ⟶ C} {g : D ⟶ D} (hf : Homotopy f (𝟙 C)) (hg : Homotopy g (𝟙 D)) :
    (tensorHomologyFunctor i).map ((f, g) : ((C, D) :
      (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) = 𝟙 _ := by
  have key : (tensorHomologyFunctor i).map ((f, g) : ((C, D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))
      = (tensorHomologyFunctor i).map (𝟙 ((C, D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ))) := by
    change HomologicalComplex.homologyMap (f ⊗ₘ g) i
      = HomologicalComplex.homologyMap (𝟙 C ⊗ₘ 𝟙 D) i
    exact (homotopy_tensorHom hf hg).homologyMap_eq i
  rw [key, CategoryTheory.Functor.map_id]

/-- A functor that maps homotopy-trivial endomorphisms to identities maps pairs of homotopy equivalences to isomorphisms. -/
lemma isIso_map_of_homotopyEquiv
    (F : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ) ⥤
      ModuleCat.{u} k)
    (hF : ∀ {C D : CochainComplex (ModuleCat.{u} k) ℤ} {f : C ⟶ C} {g : D ⟶ D},
      Homotopy f (𝟙 C) → Homotopy g (𝟙 D) →
        F.map ((f, g) : ((C, D) : (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) = 𝟙 _)
    {C C' D D' : CochainComplex (ModuleCat.{u} k) ℤ}
    (eC : HomotopyEquiv C C') (eD : HomotopyEquiv D D') :
    IsIso (F.map ((eC.hom, eD.hom) : ((C, D) :
      (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C', D'))) := by
  refine ⟨F.map ((eC.inv, eD.inv) : ((C', D') :
    (CochainComplex (ModuleCat.{u} k) ℤ) ×
      (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)), ?_, ?_⟩
  · rw [← F.map_comp]
    exact hF eC.homotopyHomInvId eD.homotopyHomInvId
  · rw [← F.map_comp]
    exact hF eC.homotopyInvHomId eD.homotopyInvHomId

/-- Establishes invertibility at every pair of complexes for the tensor-homology comparison. -/
instance isIso_tensorHomologyComparison_app (i : ℤ)
    (X : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) :
    IsIso ((totalHomologyTensorNatTrans (k := k) i).app X) := by
  obtain ⟨C, D⟩ := X
  obtain ⟨eC⟩ := nonempty_homotopyEquiv_transformed C
  obtain ⟨eD⟩ := nonempty_homotopyEquiv_transformed D
  haveI : IsIso ((totalHomologyTensorFunctor i).map ((eC.hom, eD.hom) :
      ((homologyComplex C, homologyComplex D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))) :=
    isIso_map_of_homotopyEquiv _
      (fun hf hg => sigmaHomologyTensorFunctor_map_eq_id_of_homotopy i hf hg) eC eD
  haveI : IsIso ((tensorHomologyFunctor i).map ((eC.hom, eD.hom) :
      ((homologyComplex C, homologyComplex D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D))) :=
    isIso_map_of_homotopyEquiv _
      (fun hf hg => homologyTensorFunctor_map_eq_id_of_homotopy i hf hg) eC eD
  haveI : IsIso ((totalHomologyTensorNatTrans (k := k) i).app
      (homologyComplex C, homologyComplex D)) :=
    isIso_transformedHomologyTensorMap C D i
  haveI : IsIso ((totalHomologyTensorFunctor i).map ((eC.hom, eD.hom) :
      ((homologyComplex C, homologyComplex D) :
        (CochainComplex (ModuleCat.{u} k) ℤ) ×
          (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)) ≫
      (totalHomologyTensorNatTrans i).app (C, D)) := by
    rw [(totalHomologyTensorNatTrans i).naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left ((totalHomologyTensorFunctor i).map ((eC.hom, eD.hom) :
    ((homologyComplex C, homologyComplex D) :
      (CochainComplex (ModuleCat.{u} k) ℤ) ×
        (CochainComplex (ModuleCat.{u} k) ℤ)) ⟶ (C, D)))
    ((totalHomologyTensorNatTrans (k := k) i).app (C, D))

/-- Shows that the displayed map relating tensor-product homology is an isomorphism. -/
instance isIso_homologyTensorMap (C D : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    IsIso (totalHomologyTensorToTensorHomology C D i) :=
  isIso_tensorHomologyComparison_app i (C, D)

end Reduction

section API

variable (C D : CochainComplex (ModuleCat.{u} k) ℤ)

/-- Identifies the graded sigma object of tensor products of homology with the homology of the tensor complex. -/
noncomputable def sigmaHomologyTensorIso (i : ℤ) :
    (∐ fun p : TotalDegreeIndex i => C.homology p.1.1 ⊗ D.homology p.1.2) ≅
      (binaryOperation C D).homology i :=
  asIso (totalHomologyTensorToTensorHomology C D i)

/-- Describes the forward morphism of the sigma-to-tensor-homology isomorphism. -/
@[simp]
lemma sigmaHomologyTensorIso_hom (i : ℤ) :
    (sigmaHomologyTensorIso C D i).hom = totalHomologyTensorToTensorHomology C D i := rfl

/-- Establishes invertibility of the natural comparison between the two tensor-homology functors. -/
instance isIso_tensorHomologyComparison (i : ℤ) :
    IsIso (totalHomologyTensorNatTrans (k := k) i) :=
  NatIso.isIso_of_isIso_app _

/-- Gives an isomorphism between the two displayed functors of pairs of cochain complexes. -/
@[source_ref "Chapter7/Introduction_7.8" (role := supporting),
  source_ref "Chapter7/Problem7.8.7" (role := supporting)]
noncomputable def tensorHomologyFunctorIso (i : ℤ) :
    totalHomologyTensorFunctor (k := k) i ≅ tensorHomologyFunctor (k := k) i :=
  asIso (totalHomologyTensorNatTrans i)

/-- Identifies the forward natural transformation of the tensor-homology functor isomorphism. -/
@[simp]
lemma tensorHomologyFunctorIso_hom (i : ℤ) :
    (tensorHomologyFunctorIso (k := k) i).hom = totalHomologyTensorNatTrans i := rfl

/-- Computes a component of the forward tensor-homology functor isomorphism. -/
@[simp]
lemma tensorHomologyFunctorIso_hom_app (i : ℤ)
    (X : (CochainComplex (ModuleCat.{u} k) ℤ) × (CochainComplex (ModuleCat.{u} k) ℤ)) :
    (tensorHomologyFunctorIso (k := k) i).hom.app X =
      totalHomologyTensorToTensorHomology X.1 X.2 i := rfl

/-- Identifies the homology of the displayed tensor complex with the corresponding graded sigma object. -/
@[source_ref "Chapter7/Problem7.8.7" (role := supporting)]
noncomputable def homologyTensorToSigmaIso (i : ℤ) :
    (binaryOperation C D).homology i ≅
      ∐ fun p : TotalDegreeIndex i => C.homology p.1.1 ⊗ D.homology p.1.2 :=
  (sigmaHomologyTensorIso C D i).symm

/-! ### The acyclic case -/

/-- The sigma homology-tensor value is zero when its left complex is acyclic. -/
lemma isZero_sigmaHomologyTensorFunctor_of_left_acyclic (i : ℤ) (hC : C.Acyclic) :
    IsZero ((totalHomologyTensorFunctor i).obj (C, D)) := by
  rw [IsZero.iff_id_eq_zero]
  refine Sigma.hom_ext _ _ fun p => ?_
  have hz : IsZero (C.homology p.1.1 ⊗ D.homology p.1.2) := by
    rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id,
      (IsZero.iff_id_eq_zero _).mp
        ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hC p.1.1)),
      MonoidalPreadditive.zero_tensor]
  rw [comp_zero]
  exact hz.eq_zero_of_src _

/-- The sigma homology-tensor value is zero when its right complex is acyclic. -/
lemma isZero_sigmaHomologyTensorFunctor_of_right_acyclic (i : ℤ) (hD : D.Acyclic) :
    IsZero ((totalHomologyTensorFunctor i).obj (C, D)) := by
  rw [IsZero.iff_id_eq_zero]
  refine Sigma.hom_ext _ _ fun p => ?_
  have hz : IsZero (C.homology p.1.1 ⊗ D.homology p.1.2) := by
    rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id,
      (IsZero.iff_id_eq_zero _).mp
        ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hD p.1.2)),
      MonoidalPreadditive.tensor_zero]
  rw [comp_zero]
  exact hz.eq_zero_of_src _

/-- The tensor-homology value is zero if either input complex is acyclic. -/
lemma isZero_homologyTensorFunctor_of_acyclic (i : ℤ) (h : C.Acyclic ∨ D.Acyclic) :
    IsZero ((tensorHomologyFunctor i).obj (C, D)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (tensorProduct_acyclic_of_acyclic C D h i)

end API

end RepresentationTheory.HomologicalComplex.TensorHomology

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.HomologicalComplex.TensorHomology.Auxiliary.statement021417 := _root_.RepresentationTheory.HomologicalComplex.TensorHomology.transformedTensorMap_eq

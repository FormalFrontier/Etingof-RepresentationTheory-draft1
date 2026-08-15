/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorProduct.RightModuleBifunctor
import RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose
import RepresentationTheory.CategoryTheory.Abelian.ObjectData
import Mathlib.Algebra.Homology.Monoidal

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits MonoidalCategory TensorProduct HomologicalComplex

namespace RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolutionComplexComparison

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))
variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}
variable
  (P₁ : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M₁)
  (P₂ : RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData M₂)

/-- Identifies the bifunctor image of the two projective-resolution complexes with the tensor
product of their separately mapped complexes. -/
noncomputable def mappedBifunctorComplexIsoTensorMappedProjectiveResolutionComplexes :
    (((RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose.CategoryTheory.Functor.bifunctorPostcompose
          (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
          (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
            k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj P₂.complex ≅
      (((curriedTensor (ModuleCat.{u} k)).mapBifunctorHomologicalComplex
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
          (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₁ N₁).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P₁.complex)).obj
        (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₂ N₂).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P₂.complex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents
      (fun i₂ =>
        RepresentationTheory.TensorProduct.RightModuleBifunctor.TensorProduct.RightModuleBifunctor.comparisonObjIso
          k A₁ A₂ N₁ N₂ hN (P₁.complex.X i₁) (P₂.complex.X i₂))
      (fun i₂ i₂' _ =>
        ((RepresentationTheory.TensorProduct.RightModuleBifunctor.TensorProduct.RightModuleBifunctor.comparisonIsoApp
          k A₁ A₂ N₁ N₂ hN (P₁.complex.X i₁)).hom.naturality
          (P₂.complex.d i₂ i₂')).symm))
    (fun i₁ i₁' _ => by
      apply HomologicalComplex.hom_ext
      intro i₂
      exact NatTrans.congr_app
        ((RepresentationTheory.TensorProduct.RightModuleBifunctor.TensorProduct.RightModuleBifunctor.comparisonIso
          k A₁ A₂ N₁ N₂ hN).hom.naturality (P₁.complex.d i₁ i₁')).symm
        (P₂.complex.X i₂))

/-- Constructs an isomorphism from a mapped complex associated with the two projective resolutions
to the tensor product of their separately mapped complexes. -/
noncomputable def mappedComplexIsoTensorMappedProjectiveResolutionComplexes :
    ((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
        k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
        (RepresentationTheory.Algebra.Homology.TensorProduct.tensorProductComplex P₁ P₂) ≅
      HomologicalComplex.tensorObj
        (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₁ N₁).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P₁.complex)
        (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₂ N₂).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P₂.complex) :=
  RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose.HomologicalComplex.mapBifunctorPostcomposeIso
      P₁.complex P₂.complex
      (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
      (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
        k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) ≪≫
    HomologicalComplex₂.total.mapIso
      (mappedBifunctorComplexIsoTensorMappedProjectiveResolutionComplexes
        k A₁ A₂ N₁ N₂ hN P₁ P₂)
      (ComplexShape.down ℕ)

/-- The hom of the mapped-complex comparison intertwines the bifunctor inclusion at a pair of
degrees with the pointwise comparison followed by the tensor-complex inclusion. -/
@[reassoc]
theorem mappedComplexIsoTensorMappedProjectiveResolutionComplexes_hom_comp_iota (i₁ i₂ j : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = j) :
    (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
          k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).map
          (HomologicalComplex.ιMapBifunctor P₁.complex P₂.complex
            (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
            (ComplexShape.down ℕ) i₁ i₂ j h) ≫
        (mappedComplexIsoTensorMappedProjectiveResolutionComplexes
          k A₁ A₂ N₁ N₂ hN P₁ P₂).hom.f j =
      (RepresentationTheory.TensorProduct.RightModuleBifunctor.TensorProduct.RightModuleBifunctor.comparisonObjIso
            k A₁ A₂ N₁ N₂ hN (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₁ N₁).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P₁.complex)
          (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₂ N₂).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P₂.complex)
          (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ j h := by
  rw [mappedComplexIsoTensorMappedProjectiveResolutionComplexes, Iso.trans_hom,
    HomologicalComplex.comp_f, ← Category.assoc]
  rw [show
    (RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose.HomologicalComplex.mapBifunctorPostcomposeIso
        P₁.complex P₂.complex
        (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
          k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).hom.f j =
      (RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose.HomologicalComplex.mapBifunctorPostcomposeXIso
        P₁.complex P₂.complex
        (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
          k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) j).hom from rfl,
    RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose.HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor,
    HomologicalComplex₂.total.mapIso_hom, HomologicalComplex₂.ιTotal_map]
  rfl

/-- The compatibility of the mapped-complex comparison with a bifunctor inclusion remains valid
after postcomposition by an arbitrary morphism. -/
add_decl_doc mappedComplexIsoTensorMappedProjectiveResolutionComplexes_hom_comp_iota_assoc

end RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolutionComplexComparison

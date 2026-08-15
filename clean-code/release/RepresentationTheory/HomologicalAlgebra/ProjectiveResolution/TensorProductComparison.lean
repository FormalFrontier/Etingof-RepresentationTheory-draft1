/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct
import RepresentationTheory.Algebra.TensorProduct.Free
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Monoidal

set_option backward.isDefEq.respectTransparency false

/-!
# Restriction of scalars and tensor products of projective resolutions

This module identifies the scalar restriction of the tensor-product complex of two projective
resolutions with the tensor product of their scalar-restricted complexes.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct

namespace RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison

set_option linter.dupNamespace false

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance]
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule

/-- A functor from modules over a tensor product algebra to modules over its commutative base
ring. -/
noncomputable abbrev ModuleCat.restrictScalarsFromTensorProduct
    (k A₁ A₂ : Type u) [CommRing k] [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂] :
    _root_.ModuleCat.{u} (A₁ ⊗[k] A₂) ⥤ _root_.ModuleCat.{u} k :=
  _root_.ModuleCat.restrictScalars (algebraMap k (A₁ ⊗[k] A₂))

/-- The functor from modules over the first algebra to modules over the common base ring. -/
noncomputable abbrev ModuleCat.restrictScalarsLeft
    (k A₁ : Type u) [CommRing k] [Ring A₁] [Algebra k A₁] :
    _root_.ModuleCat.{u} A₁ ⥤ _root_.ModuleCat.{u} k :=
  _root_.ModuleCat.restrictScalars (algebraMap k A₁)

/-- The functor from modules over the second algebra to modules over the common base ring. -/
noncomputable abbrev ModuleCat.restrictScalarsRight
    (k A₂ : Type u) [CommRing k] [Ring A₂] [Algebra k A₂] :
    _root_.ModuleCat.{u} A₂ ⥤ _root_.ModuleCat.{u} k :=
  _root_.ModuleCat.restrictScalars (algebraMap k A₂)

/-- Scalar multiplication through the base algebra map on a tensor product module agrees with the
original base-ring scalar action. -/
theorem ModuleCat.tensorProduct_algebraMap_smul
    (X : _root_.ModuleCat.{u} A₁) (Y : _root_.ModuleCat.{u} A₂) (c : k) (z : X ⊗[k] Y) :
    (algebraMap k (A₁ ⊗[k] A₂) c) • z = c • z := by
  change
    RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom
      k A₁ A₂ X Y (algebraMap k (A₁ ⊗[k] A₂) c) z = c • z
  rw [AlgHom.commutes]
  simp [Module.algebraMap_end_apply]

/-- The carrier of a tensor-product module after passage to the base ring is linearly equivalent to
the tensor product of the two base-ring carriers. -/
noncomputable def ModuleCat.restrictScalarsTensorProductLinearEquiv
    (X : _root_.ModuleCat.{u} A₁) (Y : _root_.ModuleCat.{u} A₂) :
    (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).obj
        (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ X Y) ≃ₗ[k]
      ((ModuleCat.restrictScalarsLeft k A₁).obj X) ⊗[k]
        ((ModuleCat.restrictScalarsRight k A₂).obj Y) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' c z := ModuleCat.tensorProduct_algebraMap_smul X Y c z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl

/-- The base-ring module underlying a tensor-product module is isomorphic to the monoidal tensor
product of the underlying base-ring modules. -/
noncomputable def ModuleCat.restrictScalarsTensorProductIso
    (X : _root_.ModuleCat.{u} A₁) (Y : _root_.ModuleCat.{u} A₂) :
    (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).obj
        (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ X Y) ≅
      ((ModuleCat.restrictScalarsLeft k A₁).obj X) ⊗
        ((ModuleCat.restrictScalarsRight k A₂).obj Y) :=
  (ModuleCat.restrictScalarsTensorProductLinearEquiv X Y).toModuleIso

/-- The forward morphism of the scalar-restriction tensor-product isomorphism sends each pure
tensor to the same pure tensor. -/
@[simp]
theorem ModuleCat.restrictScalarsTensorProductIso_hom_tmul
    (X : _root_.ModuleCat.{u} A₁) (Y : _root_.ModuleCat.{u} A₂) (x : X) (y : Y) :
    (ModuleCat.restrictScalarsTensorProductIso X Y).hom (x ⊗ₜ[k] y) = x ⊗ₜ[k] y := rfl

/-- The scalar-restriction tensor-product isomorphism commutes with a pair of module morphisms and
their tensor product. -/
theorem ModuleCat.restrictScalarsTensorProductIso_naturality
    {X X' : _root_.ModuleCat.{u} A₁} {Y Y' : _root_.ModuleCat.{u} A₂}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k f g) ≫
        (ModuleCat.restrictScalarsTensorProductIso X' Y').hom =
      (ModuleCat.restrictScalarsTensorProductIso X Y).hom ≫
        MonoidalCategory.tensorHom
          ((ModuleCat.restrictScalarsLeft k A₁).map f)
          ((ModuleCat.restrictScalarsRight k A₂).map g) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]

variable {M₁ : _root_.ModuleCat.{u} A₁} {M₂ : _root_.ModuleCat.{u} A₂}

/-- A projective resolution over the first algebra determines a chain complex of modules over the
common base ring. -/
noncomputable abbrev ProjectiveResolution.restrictScalarsComplexLeft
    (P₁ : CategoryTheory.ProjectiveResolution M₁) : ChainComplex (_root_.ModuleCat.{u} k) ℕ :=
  ((ModuleCat.restrictScalarsLeft k A₁).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj P₁.complex

/-- A projective resolution over the second algebra determines a chain complex of modules over the
common base ring. -/
noncomputable abbrev ProjectiveResolution.restrictScalarsComplexRight
    (P₂ : CategoryTheory.ProjectiveResolution M₂) : ChainComplex (_root_.ModuleCat.{u} k) ℕ :=
  ((ModuleCat.restrictScalarsRight k A₂).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj P₂.complex

/-- The double complex over a tensor product algebra associated to a pair of projective
resolutions. -/
noncomputable abbrev ProjectiveResolution.tensorProductBicomplex
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂) :
    HomologicalComplex₂ (_root_.ModuleCat.{u} (A₁ ⊗[k] A₂))
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
      k A₁ A₂).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      P₁.complex).obj P₂.complex

/-- In every degree, the scalar-restricted tensor-product construction is isomorphic to the
corresponding object of the tensor product of the scalar-restricted resolution complexes. -/
noncomputable def ProjectiveResolution.restrictScalarsTensorProductXIso
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂) (n : ℕ) :
    (((ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct
          P₁ P₂)).X n ≅
      (HomologicalComplex.tensorObj
        (ProjectiveResolution.restrictScalarsComplexLeft P₁)
        (ProjectiveResolution.restrictScalarsComplexRight P₂)).X n :=
  (PreservesCoproduct.iso (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂)
    ((ProjectiveResolution.tensorProductBicomplex P₁ P₂).toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)) ≪≫
  Limits.Sigma.mapIso (fun i => ModuleCat.restrictScalarsTensorProductIso
    (P₁.complex.X i.1.1) (P₂.complex.X i.1.2))

/-- The inverse degreewise comparison carries the canonical base-ring inclusion to the image of the
corresponding inclusion before scalar restriction. -/
theorem ProjectiveResolution.restrictScalarsTensorProductXIso_inv_iota
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂)
    (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    ιMapBifunctor (ProjectiveResolution.restrictScalarsComplexLeft P₁)
        (ProjectiveResolution.restrictScalarsComplexRight P₂)
        (curriedTensor (_root_.ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ n h ≫
        (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ n).inv =
      (ModuleCat.restrictScalarsTensorProductIso
          (P₁.complex.X i₁) (P₂.complex.X i₂)).inv ≫
        (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map
          (ιMapBifunctor P₁.complex P₂.complex
            (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
            (ComplexShape.down ℕ) i₁ i₂ n h) := by
  simp only [ProjectiveResolution.restrictScalarsTensorProductXIso, Iso.trans_inv,
    PreservesCoproduct.inv_hom, HomologicalComplex.ιMapBifunctor, HomologicalComplex₂.ιTotal,
    CategoryTheory.GradedObject.ιMapObj, Limits.Sigma.ι_mapIso_inv_assoc,
    Limits.ι_comp_sigmaComparison]

/-- The degreewise scalar-restriction comparison commutes with the canonical inclusion from a
bidegree into its total degree. -/
theorem ProjectiveResolution.restrictScalarsTensorProductXIso_iota
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂)
    (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map
          (ιMapBifunctor P₁.complex P₂.complex
            (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
            (ComplexShape.down ℕ) i₁ i₂ n h) ≫
        (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ n).hom =
      (ModuleCat.restrictScalarsTensorProductIso
          (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        ιMapBifunctor (ProjectiveResolution.restrictScalarsComplexLeft P₁)
          (ProjectiveResolution.restrictScalarsComplexRight P₂)
          (curriedTensor (_root_.ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ n h := by
  rw [← cancel_mono (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ n).inv,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ProjectiveResolution.restrictScalarsTensorProductXIso_inv_iota, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- The degreewise scalar-restriction comparison intertwines the first bifunctor differential with
the first differential on the tensor product of the base-ring complexes. -/
theorem ProjectiveResolution.restrictScalarsTensorProductXIso_d1
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map
          (HomologicalComplex.mapBifunctor.d₁ P₁.complex P₂.complex
            (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
            (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ m).hom =
      (ModuleCat.restrictScalarsTensorProductIso
          (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₁
          (ProjectiveResolution.restrictScalarsComplexLeft P₁)
          (ProjectiveResolution.restrictScalarsComplexRight P₂)
          (curriedTensor (_root_.ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ m := by
  rcases i₁ with _ | i₁'
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel])]
    simp
  · by_cases h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i₁', i₂) = m
    · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
          (by simp [ComplexShape.down_Rel]) _ _ h',
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
          (by simp [ComplexShape.down_Rel]) _ _ h',
        Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
      congr 1
      rw [Functor.map_comp, Category.assoc,
        ProjectiveResolution.restrictScalarsTensorProductXIso_iota,
        show ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
            k A₁ A₂).map (P₁.complex.d (i₁' + 1) i₁')).app (P₂.complex.X i₂) =
          RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap
            k (P₁.complex.d (i₁' + 1) i₁') (𝟙 (P₂.complex.X i₂)) from rfl,
        ← Category.assoc, ModuleCat.restrictScalarsTensorProductIso_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
          (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h',
        HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
          (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h']
      simp

/-- The degreewise scalar-restriction comparison intertwines the second bifunctor differential with
the second differential on the tensor product of the base-ring complexes. -/
theorem ProjectiveResolution.restrictScalarsTensorProductXIso_d2
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map
          (HomologicalComplex.mapBifunctor.d₂ P₁.complex P₂.complex
            (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
            (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ m).hom =
      (ModuleCat.restrictScalarsTensorProductIso
          (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₂
          (ProjectiveResolution.restrictScalarsComplexLeft P₁)
          (ProjectiveResolution.restrictScalarsComplexRight P₂)
          (curriedTensor (_root_.ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ m := by
  rcases i₂ with _ | i₂'
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel])]
    simp
  · by_cases h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i₁, i₂') = m
    · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
          (by simp [ComplexShape.down_Rel]) _ h',
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
          (by simp [ComplexShape.down_Rel]) _ h',
        Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
      congr 1
      rw [Functor.map_comp, Category.assoc,
        ProjectiveResolution.restrictScalarsTensorProductXIso_iota,
        show ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
            k A₁ A₂).obj (P₁.complex.X i₁)).map (P₂.complex.d (i₂' + 1) i₂') =
          RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap
            k (𝟙 (P₁.complex.X i₁)) (P₂.complex.d (i₂' + 1) i₂') from rfl,
        ← Category.assoc, ModuleCat.restrictScalarsTensorProductIso_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
          (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h',
        HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
          (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h']
      simp

/-- Restricting the tensor-product resolution construction to the base ring gives a complex
isomorphic to the tensor product of the two scalar-restricted resolution complexes. -/
noncomputable def ProjectiveResolution.restrictScalarsTensorProductComplexIso
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂) :
    ((ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.tensorProduct
          P₁ P₂) ≅
      HomologicalComplex.tensorObj
        (ProjectiveResolution.restrictScalarsComplexLeft P₁)
        (ProjectiveResolution.restrictScalarsComplexRight P₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂) <| by
    intro n m hnm
    rw [← cancel_epi (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ n).inv,
      Iso.inv_hom_id_assoc]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [← Category.assoc _
        (ProjectiveResolution.restrictScalarsTensorProductXIso P₁ P₂ n).inv,
      ProjectiveResolution.restrictScalarsTensorProductXIso_inv_iota, Category.assoc,
      Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      ProjectiveResolution.restrictScalarsTensorProductXIso_d1,
      ProjectiveResolution.restrictScalarsTensorProductXIso_d2,
      ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.id_comp]

/-- At bidegree zero, the scalar-restriction comparison identifies the induced resolution map with
the tensor product of the two resolution maps. -/
theorem ProjectiveResolution.restrictScalarsTensorProductIso_augmentation
    (P₁ : CategoryTheory.ProjectiveResolution M₁)
    (P₂ : CategoryTheory.ProjectiveResolution M₂)
    (h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (0, 0) = 0) :
    (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map
          (ιMapBifunctor P₁.complex P₂.complex
            (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
            (ComplexShape.down ℕ) 0 0 0 h₀) ≫
        (ModuleCat.restrictScalarsFromTensorProduct k A₁ A₂).map
          (RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct.auxiliaryMap
            P₁ P₂) ≫
        (ModuleCat.restrictScalarsTensorProductIso M₁ M₂).hom =
      (ModuleCat.restrictScalarsTensorProductIso
          (P₁.complex.X 0) (P₂.complex.X 0)).hom ≫
        MonoidalCategory.tensorHom
          ((ModuleCat.restrictScalarsLeft k A₁).map
            ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1)
          ((ModuleCat.restrictScalarsRight k A₂).map
            ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1) := by
  rw [← Functor.map_comp_assoc, HomologicalComplex.ι_mapBifunctorDesc,
    show ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map
          ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app (P₂.complex.X 0) ≫
        ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj
          M₁).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 =
      RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k
        ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
        ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 from by
      rw [show ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
              k A₁ A₂).map
            ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app (P₂.complex.X 0) =
          RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k
            ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
            (𝟙 (P₂.complex.X 0)) from rfl,
        show ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
              k A₁ A₂).obj M₁).map
            ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 =
          RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k (𝟙 M₁)
            ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 from rfl,
        ← RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap_comp,
        Category.comp_id, Category.id_comp],
    ModuleCat.restrictScalarsTensorProductIso_naturality]

end RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProductComparison

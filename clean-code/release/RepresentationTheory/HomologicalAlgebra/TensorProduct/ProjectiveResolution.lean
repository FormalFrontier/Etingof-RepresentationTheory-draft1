/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Homology.TensorProduct
import RepresentationTheory.Algebra.CategoryTheory.FreeModuleTensorProduct
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Monoidal

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance] RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.leftRestrictionModule RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.rightRestrictionModule RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.leftRestrictionModule_isScalarTower RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.rightRestrictionModule_isScalarTower RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductModule

/-- The scalar-restriction functor from modules over an opposite tensor product algebra to modules over the base ring. -/
noncomputable abbrev restrictScalarsFromTensorProductAlgebra (k A₁ A₂ : Type u) [CommRing k] [Ring A₁] [Ring A₂]
    [Algebra k A₁] [Algebra k A₂] :
    ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)

/-- The scalar-restriction functor from right modules over the first algebra to modules over the base ring. -/
noncomputable abbrev restrictScalarsFromFirstAlgebra (k A₁ : Type u) [CommRing k] [Ring A₁] [Algebra k A₁] :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A₁ᵐᵒᵖ)

/-- The scalar-restriction functor from right modules over the second algebra to modules over the base ring. -/
noncomputable abbrev restrictScalarsFromSecondAlgebra (k A₂ : Type u) [CommRing k] [Ring A₂] [Algebra k A₂] :
    ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A₂ᵐᵒᵖ)

/-- Scalar multiplication through the algebra map to the opposite tensor product algebra agrees with the given scalar action on a tensor product of modules. -/
theorem tensorProduct_algebraMap_smul (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (c : k)
    (z : X ⊗[k] Y) :
    (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) • z = c • z := by
  change RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.opTensorProductAction k A₁ A₂ X Y (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) z = c • z
  rw [AlgHom.commutes]
  simp [Module.algebraMap_end_apply]

/-- The underlying linear equivalence between the restricted external tensor product and the tensor product of the two restricted modules. -/
noncomputable def restrictScalarsExternalTensorProductLinearEquiv (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (restrictScalarsFromTensorProductAlgebra k A₁ A₂).obj (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ X Y) ≃ₗ[k]
      ((restrictScalarsFromFirstAlgebra k A₁).obj X) ⊗[k] ((restrictScalarsFromSecondAlgebra k A₂).obj Y) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' c z := tensorProduct_algebraMap_smul X Y c z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting an external tensor product module to the base ring is isomorphic to the tensor product of the individually restricted modules. -/
noncomputable def restrictScalarsExternalTensorProductIso (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (restrictScalarsFromTensorProductAlgebra k A₁ A₂).obj (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ X Y) ≅
      ((restrictScalarsFromFirstAlgebra k A₁).obj X) ⊗ ((restrictScalarsFromSecondAlgebra k A₂).obj Y) :=
  (restrictScalarsExternalTensorProductLinearEquiv X Y).toModuleIso

/-- The forward map of the scalar-restriction comparison isomorphism fixes pure tensors. -/
@[simp] theorem restrictScalarsExternalTensorProductIso_hom_tmul (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ)
    (x : X) (y : Y) :
    (restrictScalarsExternalTensorProductIso X Y).hom (x ⊗ₜ[k] y) = x ⊗ₜ[k] y := rfl

/-- The scalar-restriction comparison isomorphism intertwines the external tensor product of two morphisms with the tensor product of their restricted maps. -/
theorem restrictScalarsExternalTensorProductIso_naturality {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (restrictScalarsFromTensorProductAlgebra k A₁ A₂).map (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k f g) ≫ (restrictScalarsExternalTensorProductIso X' Y').hom =
      (restrictScalarsExternalTensorProductIso X Y).hom ≫
        MonoidalCategory.tensorHom ((restrictScalarsFromFirstAlgebra k A₁).map f) ((restrictScalarsFromSecondAlgebra k A₂).map g) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]

variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}

/-- The chain complex obtained by applying scalar restriction to a projective resolution over the first algebra. -/
noncomputable abbrev restrictScalarsFirstProjectiveResolution (P₁ : ProjectiveResolution M₁) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((restrictScalarsFromFirstAlgebra k A₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₁.complex

/-- The chain complex obtained by applying scalar restriction to a projective resolution over the second algebra. -/
noncomputable abbrev restrictScalarsSecondProjectiveResolution (P₂ : ProjectiveResolution M₂) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((restrictScalarsFromSecondAlgebra k A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₂.complex

/-- The double complex of modules over a tensor product algebra associated to a pair of projective resolutions. -/
noncomputable abbrev projectiveResolutionTensorDoubleComplex (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    HomologicalComplex₂ (ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj P₂.complex

/-- In each degree, restricting the complex formed from two projective resolutions is isomorphic to the corresponding term of the tensor product of the restricted complexes. -/
noncomputable def restrictScalarsTensorResolutionXIso (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    (((restrictScalarsFromTensorProductAlgebra k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (RepresentationTheory.Algebra.Homology.TensorProduct.tensorProductComplex P₁ P₂)).X n ≅
      (HomologicalComplex.tensorObj (restrictScalarsFirstProjectiveResolution P₁) (restrictScalarsSecondProjectiveResolution P₂)).X n :=
  (PreservesCoproduct.iso (restrictScalarsFromTensorProductAlgebra k A₁ A₂)
    ((projectiveResolutionTensorDoubleComplex P₁ P₂).toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)) ≪≫
  Limits.Sigma.mapIso (fun i => restrictScalarsExternalTensorProductIso (P₁.complex.X i.1.1) (P₂.complex.X i.1.2))

/-- The inverse degreewise scalar-restriction comparison intertwines the canonical map from a bidegree into the associated complex. -/
theorem restrictScalarsTensorResolutionXIso_inv_iota (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    ιMapBifunctor (restrictScalarsFirstProjectiveResolution P₁) (restrictScalarsSecondProjectiveResolution P₂) (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.down ℕ) i₁ i₂ n h ≫ (restrictScalarsTensorResolutionXIso P₁ P₂ n).inv =
      (restrictScalarsExternalTensorProductIso (P₁.complex.X i₁) (P₂.complex.X i₂)).inv ≫ (restrictScalarsFromTensorProductAlgebra k A₁ A₂).map
        (ιMapBifunctor P₁.complex P₂.complex (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (ComplexShape.down ℕ)
          i₁ i₂ n h) := by
  simp only [restrictScalarsTensorResolutionXIso, Iso.trans_inv, PreservesCoproduct.inv_hom,
    HomologicalComplex.ιMapBifunctor, HomologicalComplex₂.ιTotal,
    CategoryTheory.GradedObject.ιMapObj, Limits.Sigma.ι_mapIso_inv_assoc,
    Limits.ι_comp_sigmaComparison]

/-- The degreewise scalar-restriction comparison intertwines the canonical map from a bidegree into the associated complex. -/
theorem restrictScalarsTensorResolutionXIso_iota (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    (restrictScalarsFromTensorProductAlgebra k A₁ A₂).map (ιMapBifunctor P₁.complex P₂.complex (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (ComplexShape.down ℕ) i₁ i₂ n h) ≫ (restrictScalarsTensorResolutionXIso P₁ P₂ n).hom =
      (restrictScalarsExternalTensorProductIso (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        ιMapBifunctor (restrictScalarsFirstProjectiveResolution P₁) (restrictScalarsSecondProjectiveResolution P₂) (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.down ℕ) i₁ i₂ n h := by
  rw [← cancel_mono (restrictScalarsTensorResolutionXIso P₁ P₂ n).inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, restrictScalarsTensorResolutionXIso_inv_iota, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- The degreewise scalar-restriction comparison commutes with the differential in the first complex. -/
theorem restrictScalarsTensorResolutionXIso_d1 (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (restrictScalarsFromTensorProductAlgebra k A₁ A₂).map (HomologicalComplex.mapBifunctor.d₁ P₁.complex P₂.complex
        (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (restrictScalarsTensorResolutionXIso P₁ P₂ m).hom =
      (restrictScalarsExternalTensorProductIso (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₁ (restrictScalarsFirstProjectiveResolution P₁) (restrictScalarsSecondProjectiveResolution P₂)
          (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ m := by
  rcases i₁ with _ | i₁'
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel])]
    simp
  · by_cases h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i₁', i₂) = m
    · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by simp [ComplexShape.down_Rel]) _ _ h',
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by simp [ComplexShape.down_Rel]) _ _ h',
        Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
      congr 1
      rw [Functor.map_comp, Category.assoc, restrictScalarsTensorResolutionXIso_iota,
        show ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map (P₁.complex.d (i₁' + 1) i₁')).app
          (P₂.complex.X i₂) = RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k (P₁.complex.d (i₁' + 1) i₁')
            (𝟙 (P₂.complex.X i₂)) from rfl, ← Category.assoc,
        restrictScalarsExternalTensorProductIso_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h',
        HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h']
      simp

/-- The degreewise scalar-restriction comparison commutes with the differential in the second complex. -/
theorem restrictScalarsTensorResolutionXIso_d2 (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (restrictScalarsFromTensorProductAlgebra k A₁ A₂).map (HomologicalComplex.mapBifunctor.d₂ P₁.complex P₂.complex
        (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂) (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (restrictScalarsTensorResolutionXIso P₁ P₂ m).hom =
      (restrictScalarsExternalTensorProductIso (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₂ (restrictScalarsFirstProjectiveResolution P₁) (restrictScalarsSecondProjectiveResolution P₂)
          (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ m := by
  rcases i₂ with _ | i₂'
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel])]
    simp
  · by_cases h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i₁, i₂') = m
    · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (by simp [ComplexShape.down_Rel]) _ h',
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (by simp [ComplexShape.down_Rel]) _ h',
        Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
      congr 1
      rw [Functor.map_comp, Category.assoc, restrictScalarsTensorResolutionXIso_iota,
        show ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj (P₁.complex.X i₁)).map (P₂.complex.d (i₂' + 1) i₂') =
          RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k (𝟙 (P₁.complex.X i₁)) (P₂.complex.d (i₂' + 1) i₂') from rfl,
        ← Category.assoc, restrictScalarsExternalTensorProductIso_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h',
        HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h']
      simp

/-- Restricting the complex formed from two projective resolutions is isomorphic to the tensor product of their restricted complexes. -/
noncomputable def restrictScalarsTensorResolutionIso (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) :
    ((restrictScalarsFromTensorProductAlgebra k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj (RepresentationTheory.Algebra.Homology.TensorProduct.tensorProductComplex P₁ P₂) ≅
      HomologicalComplex.tensorObj (restrictScalarsFirstProjectiveResolution P₁) (restrictScalarsSecondProjectiveResolution P₂) :=
  HomologicalComplex.Hom.isoOfComponents (restrictScalarsTensorResolutionXIso P₁ P₂) <| by
    intro n m hnm
    rw [← cancel_epi (restrictScalarsTensorResolutionXIso P₁ P₂ n).inv, Iso.inv_hom_id_assoc]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h

    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]

    rw [← Category.assoc _ (restrictScalarsTensorResolutionXIso P₁ P₂ n).inv, restrictScalarsTensorResolutionXIso_inv_iota,
      Category.assoc, Functor.mapHomologicalComplex_obj_d,
      ← Functor.map_comp_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      restrictScalarsTensorResolutionXIso_d1, restrictScalarsTensorResolutionXIso_d2, ← Category.assoc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Category.id_comp]

/-- In degree zero, the scalar-restriction comparison identifies the mapped augmentation with the tensor product of the two restricted augmentations. -/
theorem restrictScalarsTensorResolutionIso_zero_augmentation (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂)
    (h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (0, 0) = 0) :
    (restrictScalarsFromTensorProductAlgebra k A₁ A₂).map (ιMapBifunctor P₁.complex P₂.complex (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (ComplexShape.down ℕ) 0 0 0 h₀) ≫
        (restrictScalarsFromTensorProductAlgebra k A₁ A₂).map (RepresentationTheory.Algebra.Homology.TensorProduct.zeroComponentToTarget P₁ P₂) ≫ (restrictScalarsExternalTensorProductIso M₁ M₂).hom =
      (restrictScalarsExternalTensorProductIso (P₁.complex.X 0) (P₂.complex.X 0)).hom ≫ MonoidalCategory.tensorHom
        ((restrictScalarsFromFirstAlgebra k A₁).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1)
        ((restrictScalarsFromSecondAlgebra k A₂).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1) := by
  rw [← Functor.map_comp_assoc, HomologicalComplex.ι_mapBifunctorDesc,
    show ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app
          (P₂.complex.X 0) ≫
        ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj M₁).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
      = RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
          ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 from by
        rw [show ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map
              ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app (P₂.complex.X 0)
            = RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
                (𝟙 (P₂.complex.X 0)) from rfl,
          show ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj M₁).map
              ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
            = RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k (𝟙 M₁) ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
                from rfl,
          ← RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom_comp, Category.comp_id, Category.id_comp],
    restrictScalarsExternalTensorProductIso_naturality]

end RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolution

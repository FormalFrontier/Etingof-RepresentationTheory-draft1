/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.TensorProduct.Module
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products in module categories

This module packages tensor products of modules and module morphisms as a bifunctor between
module categories.
-/

open TensorProduct CategoryTheory

namespace RepresentationTheory.Algebra.TensorProduct.ModuleCat

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

/-- Supplies the base-ring module structure carried by a module-category object. -/
noncomputable local instance moduleCarrier (X : ModuleCat.{u} A₁) : Module k X :=
  Module.compHom X (algebraMap k A₁)

/-- Auxiliary base-ring module structure for a module-category carrier. -/
noncomputable local instance moduleCarrierAux (Y : ModuleCat.{u} A₂) : Module k Y :=
  Module.compHom Y (algebraMap k A₂)

/-- The carrier action of an algebra object satisfies the scalar-tower law. -/
local instance isScalarTower (X : ModuleCat.{u} A₁) : IsScalarTower k A₁ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- Auxiliary scalar-tower instance for the carrier of a module-category object. -/
local instance isScalarTowerAux (Y : ModuleCat.{u} A₂) : IsScalarTower k A₂ Y :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- Provides the module structure on a tensor product of module carriers. -/
noncomputable local instance tensorProductModule (X : ModuleCat.{u} A₁)
    (Y : ModuleCat.{u} A₂) : Module (A₁ ⊗[k] A₂) (X ⊗[k] Y) :=
  RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k A₁ A₂ X Y

/-- Scalar multiplication by a pure tensor acts componentwise on pure module tensors. -/
@[simp] theorem smul_tmul (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂)
    (a₁ : A₁) (a₂ : A₂) (m₁ : X) (m₂ : Y) :
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (m₁ ⊗ₜ[k] m₂ : X ⊗[k] Y)
      = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂) :=
  RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.smul_tmul
    k A₁ A₂ X Y a₁ a₂ m₁ m₂

/-- Forms the module-category object obtained from two modules by tensor product. -/
noncomputable def tensorProduct (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    ModuleCat.{u} (A₁ ⊗[k] A₂) :=
  ModuleCat.of (A₁ ⊗[k] A₂) (X ⊗[k] Y)

variable {A₁ A₂}

/-- The linear map induced on tensor products by two module morphisms. -/
noncomputable def tensorProductLinearMap {X X' : ModuleCat.{u} A₁}
    {Y Y' : ModuleCat.{u} A₂} (f : X ⟶ X') (g : Y ⟶ Y') :
    (X ⊗[k] Y) →ₗ[(A₁ ⊗[k] A₂)] (X' ⊗[k] Y') where
  toFun := TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)
  map_add' := map_add _
  map_smul' r z := by
    change TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) (r • z)
      = r • TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) z
    induction r using TensorProduct.induction_on generalizing z with
    | zero => simp only [zero_smul, map_zero]
    | tmul a₁ a₂ =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | tmul m₁ m₂ =>
        simp only [smul_tmul, TensorProduct.map_tmul,
          LinearMap.restrictScalars_apply, map_smul]
      | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
    | add s1 s2 ih1 ih2 => simp only [add_smul, map_add, ih1, ih2]

/-- Describes the value of the induced linear map on a pure tensor. -/
@[simp] theorem tensorProductLinearMap_tmul {X X' : ModuleCat.{u} A₁}
    {Y Y' : ModuleCat.{u} A₂} (f : X ⟶ X') (g : Y ⟶ Y') (m₁ : X) (m₂ : Y) :
    tensorProductLinearMap k f g (m₁ ⊗ₜ[k] m₂) = f.hom m₁ ⊗ₜ[k] g.hom m₂ := rfl

/-- Tensor-product linear maps send identity morphisms to the identity map. -/
theorem tensorProductLinearMap_id (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    tensorProductLinearMap k (𝟙 X) (𝟙 Y) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add, LinearMap.id_coe, id_eq]

/-- Tensor-product linear maps respect composition in both arguments. -/
theorem tensorProductLinearMap_comp {X X' X'' : ModuleCat.{u} A₁}
    {Y Y' Y'' : ModuleCat.{u} A₂} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'')
    (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    tensorProductLinearMap k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = (tensorProductLinearMap k f₂ g₂) ∘ₗ (tensorProductLinearMap k f₁ g₁) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- Maps a pair of module morphisms to the induced tensor-product morphism. -/
noncomputable def tensorProductMap {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorProduct k A₁ A₂ X Y ⟶ tensorProduct k A₁ A₂ X' Y' :=
  ModuleCat.ofHom (tensorProductLinearMap k f g)

/-- The underlying linear map of a tensor-product morphism is the induced linear map. -/
@[simp] theorem tensorProductMap_hom {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorProductMap k f g).hom = tensorProductLinearMap k f g := rfl

/-- The tensor-product morphism construction preserves identity morphisms. -/
theorem tensorProductMap_id (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    tensorProductMap k (𝟙 X) (𝟙 Y) = 𝟙 (tensorProduct k A₁ A₂ X Y) := by
  apply ModuleCat.hom_ext
  rw [tensorProductMap_hom, tensorProductLinearMap_id, ModuleCat.hom_id]

/-- The tensor-product morphism construction preserves composition. -/
theorem tensorProductMap_comp {X X' X'' : ModuleCat.{u} A₁}
    {Y Y' Y'' : ModuleCat.{u} A₂} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'')
    (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    tensorProductMap k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = tensorProductMap k f₁ g₁ ≫ tensorProductMap k f₂ g₂ := by
  apply ModuleCat.hom_ext
  rw [tensorProductMap_hom, tensorProductLinearMap_comp, ModuleCat.hom_comp,
    tensorProductMap_hom, tensorProductMap_hom]

variable (A₁ A₂)

/-- Constructs the bifunctor taking two module-category objects to their tensor product. -/
noncomputable def tensorProductFunctor :
    ModuleCat.{u} A₁ ⥤ ModuleCat.{u} A₂ ⥤ ModuleCat.{u} (A₁ ⊗[k] A₂) where
  obj X :=
    { obj := fun Y => tensorProduct k A₁ A₂ X Y
      map := fun {_ _} g => tensorProductMap k (𝟙 X) g
      map_id := fun Y => tensorProductMap_id k X Y
      map_comp := fun {_ _ _} g₁ g₂ => by
        have h := tensorProductMap_comp k (𝟙 X) (𝟙 X) g₁ g₂
        rwa [Category.comp_id] at h }
  map := fun {X X'} f =>
    { app := fun Y => tensorProductMap k f (𝟙 Y)
      naturality := fun {Y Y'} g => by
        have h1 := tensorProductMap_comp k (𝟙 X) f g (𝟙 Y')
        have h2 := tensorProductMap_comp k f (𝟙 X') (𝟙 Y) g
        rw [Category.id_comp, Category.comp_id] at h1
        rw [Category.comp_id, Category.id_comp] at h2
        rw [← h1, ← h2] }
  map_id := fun X => by
    apply NatTrans.ext
    funext Y
    simpa using tensorProductMap_id k X Y
  map_comp := fun {X X' X''} f₁ f₂ => by
    apply NatTrans.ext
    funext Y
    have h := tensorProductMap_comp k f₁ f₂ (𝟙 Y) (𝟙 Y)
    rw [Category.comp_id] at h
    simpa using h

end RepresentationTheory.Algebra.TensorProduct.ModuleCat

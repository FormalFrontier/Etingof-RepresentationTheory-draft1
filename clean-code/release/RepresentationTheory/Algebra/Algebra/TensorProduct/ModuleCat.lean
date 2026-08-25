/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.TensorProduct.OppositeModule
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of module-category objects over opposite algebras

This module packages tensor products of right-module objects and their morphisms as a bifunctor
between module categories.
-/

open TensorProduct MulOpposite CategoryTheory

namespace RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

/-- Equips the first carrier with the scalar-module structure induced by its algebra action. -/
noncomputable local instance leftRestrictionModule (X : ModuleCat.{u} A₁ᵐᵒᵖ) : Module k X :=
  Module.compHom X (algebraMap k A₁ᵐᵒᵖ)

/-- Equips the second carrier with the scalar-module structure induced by its algebra action. -/
noncomputable local instance rightRestrictionModule (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : Module k Y :=
  Module.compHom Y (algebraMap k A₂ᵐᵒᵖ)

/-- The scalar actions on the first carrier form a compatible tower. -/
local instance leftRestrictionModule_isScalarTower
    (X : ModuleCat.{u} A₁ᵐᵒᵖ) : IsScalarTower k A₁ᵐᵒᵖ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- The scalar actions on the second carrier form a compatible tower. -/
local instance rightRestrictionModule_isScalarTower
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : IsScalarTower k A₂ᵐᵒᵖ Y :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- Provides the module structure on the tensor product of two carriers over the opposite
tensor-product algebra. -/
noncomputable local instance tensorProductModule (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) :=
  RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.moduleOppositeTensorProduct
    k A₁ A₂ X Y

/-- A pure algebra tensor acts on a pure module tensor componentwise. -/
@[simp] theorem tensorProduct_tmul_smul (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (a₁ : A₁) (a₂ : A₂) (m₁ : X) (m₂ : Y) :
    (op (a₁ ⊗ₜ[k] a₂) : (A₁ ⊗[k] A₂)ᵐᵒᵖ) • (m₁ ⊗ₜ[k] m₂ : X ⊗[k] Y)
      = (op a₁ • m₁) ⊗ₜ[k] (op a₂ • m₂) :=
  RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.op_tmul_smul_tmul
    k A₁ A₂ X Y a₁ a₂ m₁ m₂

/-- Constructs the module-category object from a pair of module-category objects by tensor product. -/
noncomputable def tensorProductObject (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ :=
  ModuleCat.of (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y)

variable {A₁ A₂}

/-- Constructs the linear map induced by a pair of module morphisms on a tensor product. -/
noncomputable def tensorProductLinearMap {X X' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y') :
    (X ⊗[k] Y) →ₗ[(A₁ ⊗[k] A₂)ᵐᵒᵖ] (X' ⊗[k] Y') where
  toFun := TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)
  map_add' := map_add _
  map_smul' r z := by
    change TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) (r • z)
      = r • TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) z
    induction r using MulOpposite.rec' with
    | _ s =>
      induction s using TensorProduct.induction_on generalizing z with
      | zero => simp only [MulOpposite.op_zero, zero_smul, map_zero]
      | tmul a₁ a₂ =>
        induction z using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul m₁ m₂ =>
          simp only [tensorProduct_tmul_smul, TensorProduct.map_tmul,
            LinearMap.restrictScalars_apply, map_smul]
        | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
      | add s1 s2 ih1 ih2 => simp only [MulOpposite.op_add, add_smul, map_add, ih1, ih2]

/-- The induced linear map carries a pure tensor to the tensor of the images. -/
@[simp] theorem tensorProductLinearMap_tmul {X X' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y') (m₁ : X) (m₂ : Y) :
    tensorProductLinearMap k f g (m₁ ⊗ₜ[k] m₂) = f.hom m₁ ⊗ₜ[k] g.hom m₂ := rfl

/-- The tensor-product linear map of identity morphisms is the identity. -/
theorem tensorProductLinearMap_id (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    tensorProductLinearMap k (𝟙 X) (𝟙 Y) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add, LinearMap.id_coe, id_eq]

/-- The induced tensor-product linear maps preserve composition. -/
theorem tensorProductLinearMap_comp {X X' X'' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' Y'' : ModuleCat.{u} A₂ᵐᵒᵖ} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'')
    (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    tensorProductLinearMap k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = (tensorProductLinearMap k f₂ g₂) ∘ₗ (tensorProductLinearMap k f₁ g₁) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- Sends a pair of morphisms to the associated morphism between tensor-product objects. -/
noncomputable def tensorProductHom {X X' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorProductObject k A₁ A₂ X Y ⟶ tensorProductObject k A₁ A₂ X' Y' :=
  ModuleCat.ofHom (tensorProductLinearMap k f g)

/-- The underlying linear map of a tensor-product morphism is the induced tensor-product linear
map. -/
@[simp] theorem tensorProductHom_hom {X X' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorProductHom k f g).hom = tensorProductLinearMap k f g := rfl

/-- The tensor-product morphism of identity maps is the identity. -/
theorem tensorProductHom_id (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    tensorProductHom k (𝟙 X) (𝟙 Y) = 𝟙 (tensorProductObject k A₁ A₂ X Y) := by
  apply ModuleCat.hom_ext
  rw [tensorProductHom_hom, tensorProductLinearMap_id, ModuleCat.hom_id]

/-- The tensor-product morphism construction respects composition. -/
theorem tensorProductHom_comp {X X' X'' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' Y'' : ModuleCat.{u} A₂ᵐᵒᵖ} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'')
    (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    tensorProductHom k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = tensorProductHom k f₁ g₁ ≫ tensorProductHom k f₂ g₂ := by
  apply ModuleCat.hom_ext
  rw [tensorProductHom_hom, tensorProductLinearMap_comp, ModuleCat.hom_comp,
    tensorProductHom_hom, tensorProductHom_hom]

variable (A₁ A₂)

/-- Maps a pair of module-category objects to their tensor-product object. -/
noncomputable def tensorProductFunctor :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ where
  obj X :=
    { obj := fun Y => tensorProductObject k A₁ A₂ X Y
      map := fun {_ _} g => tensorProductHom k (𝟙 X) g
      map_id := fun Y => tensorProductHom_id k X Y
      map_comp := fun {_ _ _} g₁ g₂ => by
        have h := tensorProductHom_comp k (𝟙 X) (𝟙 X) g₁ g₂
        rwa [Category.comp_id] at h }
  map := fun {X X'} f =>
    { app := fun Y => tensorProductHom k f (𝟙 Y)
      naturality := fun {Y Y'} g => by
        have h1 := tensorProductHom_comp k (𝟙 X) f g (𝟙 Y')
        have h2 := tensorProductHom_comp k f (𝟙 X') (𝟙 Y) g
        rw [Category.id_comp, Category.comp_id] at h1
        rw [Category.comp_id, Category.id_comp] at h2
        rw [← h1, ← h2] }
  map_id := fun X => by
    apply NatTrans.ext
    funext Y
    simpa using tensorProductHom_id k X Y
  map_comp := fun {X X' X''} f₁ f₂ => by
    apply NatTrans.ext
    funext Y
    have h := tensorProductHom_comp k f₁ f₂ (𝟙 Y) (𝟙 Y)
    rw [Category.comp_id] at h
    simpa using h

end RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat

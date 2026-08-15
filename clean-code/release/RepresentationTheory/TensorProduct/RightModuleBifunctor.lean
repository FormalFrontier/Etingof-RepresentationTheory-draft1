/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.TensorProduct.RightLinearMap
import RepresentationTheory.ModuleCat.RightTensor
import RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Right-module tensor-product bifunctor comparison

This module constructs and compares two bifunctors obtained from tensor products of right modules.
-/

open CategoryTheory MonoidalCategory TensorProduct MulOpposite

namespace RepresentationTheory.TensorProduct.RightModuleBifunctor.TensorProduct.RightModuleBifunctor

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

/-- The carrier of a right module over an algebra is naturally a module over the base field. -/
noncomputable local instance baseFieldModule {B : Type u} [Ring B] [Algebra k B]
    (X : ModuleCat.{u} Bᵐᵒᵖ) : Module k X :=
  Module.compHom X (algebraMap k Bᵐᵒᵖ)

/-- The base field, opposite algebra, and carrier of a right module form a scalar tower. -/
local instance baseField_isScalarTower {B : Type u} [Ring B] [Algebra k B] (X : ModuleCat.{u} Bᵐᵒᵖ) :
    IsScalarTower k Bᵐᵒᵖ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- Base-field scalar multiplication commutes with the action of the opposite algebra on a right module. -/
local instance baseField_smulCommClass {B : Type u} [Ring B] [Algebra k B] (X : ModuleCat.{u} Bᵐᵒᵖ) :
    SMulCommClass k Bᵐᵒᵖ X where
  smul_comm c a m := by
    change (algebraMap k Bᵐᵒᵖ c) • (a • m) = a • ((algebraMap k Bᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The tensor product of two right modules carries a module structure over the opposite of the tensor product algebra. -/
noncomputable local instance tensorProductRightModule (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) :=
  inferInstanceAs (Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ X Y))

/-- Base-field scalars commute with the opposite tensor-product algebra on the tensor product of two right modules. -/
local instance tensorProduct_smulCommClass (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) where
  smul_comm c r m := by
    change c • (RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.opTensorProductAction k A₁ A₂ X Y r m) = RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.opTensorProductAction k A₁ A₂ X Y r (c • m)
    rw [map_smul]

/-- An auxiliary equality between the two displayed maps associated with a morphism of right modules. -/
theorem Auxiliary.moduleMorphismMap_eq {B : Type u} [Ring B] [Algebra k B]
    (N : Type u) [AddCommGroup N] [Module B N] {M M' : ModuleCat.{u} Bᵐᵒᵖ} (f : M ⟶ M') :
    RepresentationTheory.ModuleCat.RightTensor.rightTensorMapLinear k B N f
      = RepresentationTheory.TensorProduct.RightLinearMap.auxiliaryTensorProductMapInduced k B M M' N (RepresentationTheory.TensorProduct.RightLinearMap.rightLinearMapToLinearMap k B M M' f.hom)
          (RepresentationTheory.TensorProduct.RightLinearMap.rightLinearMapToLinearMap_smul k B M M' f.hom) := by
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => simp
  | tmul m n => rw [RepresentationTheory.ModuleCat.RightTensor.rightTensorMapLinear_apply_tmul, RepresentationTheory.TensorProduct.RightLinearMap.auxiliaryTensorProductMapInduced_mk_tmul, RepresentationTheory.TensorProduct.RightLinearMap.rightLinearMapToLinearMap_apply]
  | add a b ha hb => rw [QuotientAddGroup.mk_add, map_add, map_add, ha, hb]

/-- A bifunctor from two categories of right modules to vector spaces, parameterized by a module structure on the tensor product of two vector spaces. -/
noncomputable def moduleBifunctorOfTensorProductModule :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂ ⋙
    (Functor.whiskeringRight (ModuleCat.{u} A₂ᵐᵒᵖ) (ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ)
      (ModuleCat.{u} k)).obj (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))

/-- A bifunctor from two categories of right modules to vector spaces, parameterized by a module over each algebra. -/
noncomputable def moduleBifunctorOfFactorModules :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₁ N₁ ⋙ curriedTensor (ModuleCat.{u} k)) ⋙
    (Functor.whiskeringLeft (ModuleCat.{u} A₂ᵐᵒᵖ) (ModuleCat.{u} k) (ModuleCat.{u} k)).obj
      (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₂ N₂)

include hN in

/-- The two explicitly displayed module objects built from the tensor-product data are isomorphic over the base field. -/
noncomputable def explicitComparisonObjIso (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ModuleCat.of k (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (X ⊗[k] Y))
      ≅ ModuleCat.of k (RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ X ⊗[k] RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ Y) :=
  (RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.combinedTensorComponentsEquiv k A₁ A₂ X Y N₁ N₂
    (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProduct_tmul_smul k A₁ A₂ X Y) hN).toModuleIso

/-- A scalar embedded into the opposite tensor-product algebra acts on the tensor product in the same way as the original scalar. -/
theorem algebraMap_smul_eq_smul (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (c : k)
    (z : X ⊗[k] Y) :
    (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) • z = c • z := by
  change RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.opTensorProductAction k A₁ A₂ X Y (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) z = c • z
  rw [AlgHom.commutes]
  simp [Module.algebraMap_end_apply]

/-- The carrier of the tensor-product-module bifunctor value is linearly equivalent to the displayed tensor-product module carrier. -/
noncomputable def moduleBifunctorCarrierLinearEquiv (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (((moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂).obj X).obj Y) ≃ₗ[k]
      RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (X ⊗[k] Y) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' c z := by
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
      simp only [RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul w n =>
          simp only [RepresentationTheory.TensorProduct.AuxiliaryScalarAction.TensorProduct.Auxiliary.smul_mk, TensorProduct.smul_tmul']
          exact congrArg (fun v => (QuotientAddGroup.mk (v ⊗ₜ[ℤ] n) :
            RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (X ⊗[k] Y)))
            (algebraMap_smul_eq_smul k A₁ A₂ X Y c w)
      | add a b ha hb =>
          simp only [QuotientAddGroup.mk_add, smul_add, ha, hb]
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl

omit [Module A₁ N₁] [IsScalarTower k A₁ N₁] [Module A₂ N₂] [IsScalarTower k A₂ N₂] in
/-- The carrier linear equivalence acts as the identity on every element of the bifunctor value. -/
@[simp] theorem moduleBifunctorCarrierLinearEquiv_apply (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ)
    (z : ((moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂).obj X).obj Y) :
    moduleBifunctorCarrierLinearEquiv k A₁ A₂ N₁ N₂ X Y z = z := rfl

include hN in

/-- The carriers of the values of the two module bifunctors are linearly equivalent over the base field. -/
noncomputable def comparisonLinearEquiv (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (((moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂).obj X).obj Y) ≃ₗ[k]
      (((moduleBifunctorOfFactorModules k A₁ A₂ N₁ N₂).obj X).obj Y) :=
  (moduleBifunctorCarrierLinearEquiv k A₁ A₂ N₁ N₂ X Y).trans
    (RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.combinedTensorComponentsEquiv k A₁ A₂ X Y N₁ N₂ (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProduct_tmul_smul k A₁ A₂ X Y) hN)

include hN in
/-- The comparison linear equivalence sends a tensor of pure-tensor classes to the tensor of the corresponding classes. -/
@[simp] theorem comparisonLinearEquiv_tmul (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (x : X) (y : Y) (n₁ : N₁) (n₂ : N₂) :
    comparisonLinearEquiv k A₁ A₂ N₁ N₂ hN X Y
        (QuotientAddGroup.mk ((x ⊗ₜ[k] y) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (x ⊗ₜ[ℤ] n₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ X)
          ⊗ₜ[k] (QuotientAddGroup.mk (y ⊗ₜ[ℤ] n₂) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ Y) := by
  rw [comparisonLinearEquiv, LinearEquiv.trans_apply]
  exact RepresentationTheory.Auxiliary.TensorProductPairingMaps.Auxiliary.combinedTensorComponentsEquiv_mk_tmul_tmul k A₁ A₂ X Y N₁ N₂
    (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProduct_tmul_smul k A₁ A₂ X Y) hN x y n₁ n₂

include hN in

/-- For fixed right modules, the two displayed module bifunctors have isomorphic values when the tensor-product action satisfies the pure-tensor formula. -/
noncomputable def comparisonObjIso (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ((moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂).obj X).obj Y ≅
      ((moduleBifunctorOfFactorModules k A₁ A₂ N₁ N₂).obj X).obj Y :=
  (comparisonLinearEquiv k A₁ A₂ N₁ N₂ hN X Y).toModuleIso

include hN in
/-- The forward map of the objectwise comparison sends a tensor of pure-tensor classes to the corresponding tensor of classes. -/
@[simp] theorem comparisonObjIso_hom_tmul (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (x : X) (y : Y) (n₁ : N₁) (n₂ : N₂) :
    (comparisonObjIso k A₁ A₂ N₁ N₂ hN X Y).hom
        (QuotientAddGroup.mk ((x ⊗ₜ[k] y) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (x ⊗ₜ[ℤ] n₁) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₁ N₁ X)
          ⊗ₜ[k] (QuotientAddGroup.mk (y ⊗ₜ[ℤ] n₂) : RepresentationTheory.Algebra.Homology.TensorProductConstruction.ModuleConstruction A₂ N₂ Y) :=
  comparisonLinearEquiv_tmul k A₁ A₂ N₁ N₂ hN X Y x y n₁ n₂

omit [Module A₁ N₁] [IsScalarTower k A₁ N₁] [Module A₂ N₂] [IsScalarTower k A₂ N₂] in
/-- Mapping in the second variable of the tensor-product-module bifunctor agrees with the displayed map obtained by fixing the first variable. -/
theorem moduleBifunctorOfTensorProductModule_map_second (X : ModuleCat.{u} A₁ᵐᵒᵖ) {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') :
    ((moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂).obj X).map g =
      (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).map (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k (𝟙 X) g) :=
  rfl

omit [Module k N₁] [IsScalarTower k A₁ N₁] [Module k N₂] [IsScalarTower k A₂ N₂] instN in
/-- Mapping in the second variable of the factor-module bifunctor is the left whiskering of the corresponding map. -/
theorem moduleBifunctorOfFactorModules_map_second (X : ModuleCat.{u} A₁ᵐᵒᵖ) {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') :
    ((moduleBifunctorOfFactorModules k A₁ A₂ N₁ N₂).obj X).map g =
      MonoidalCategory.whiskerLeft ((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₁ N₁).obj X)
        ((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₂ N₂).map g) :=
  rfl

/-- The map induced by a pair of module morphisms sends a pure tensor to the tensor of their values. -/
theorem map_tmul {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap k f g (x ⊗ₜ[k] y) = f.hom x ⊗ₜ[k] g.hom y :=
  rfl

omit [Module A₁ N₁] [IsScalarTower k A₁ N₁] [Module A₂ N₂] [IsScalarTower k A₂ N₂] in
/-- Mapping in the first variable of the tensor-product-module bifunctor agrees with the displayed map obtained by fixing the second variable. -/
theorem moduleBifunctorOfTensorProductModule_map_first {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} (f : X ⟶ X')
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ((moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂).map f).app Y =
      (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).map (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k f (𝟙 Y)) :=
  rfl

omit [Module k N₁] [IsScalarTower k A₁ N₁] [Module k N₂] [IsScalarTower k A₂ N₂] instN in
/-- Mapping in the first variable of the factor-module bifunctor is the right whiskering of the corresponding map. -/
theorem moduleBifunctorOfFactorModules_map_first {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} (f : X ⟶ X')
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ((moduleBifunctorOfFactorModules k A₁ A₂ N₁ N₂).map f).app Y =
      MonoidalCategory.whiskerRight ((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₁ N₁).map f)
        ((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₂ N₂).obj Y) :=
  rfl

include hN in

/-- Fixing the first right module in the two bifunctors yields isomorphic functors of the second module. -/
noncomputable def comparisonIsoApp (X : ModuleCat.{u} A₁ᵐᵒᵖ) :
    (moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂).obj X ≅ (moduleBifunctorOfFactorModules k A₁ A₂ N₁ N₂).obj X :=
  NatIso.ofComponents
    (fun Y => comparisonObjIso k A₁ A₂ N₁ N₂ hN X Y)
    (by
      intro Y Y' g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [QuotientAddGroup.mk_add, map_add, ha, hb]
      | tmul p q =>
          induction p using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb =>
              simp only [add_tmul, QuotientAddGroup.mk_add, map_add, ha, hb]
          | tmul x y =>
              induction q using TensorProduct.induction_on with
              | zero => simp
              | add a b ha hb =>
                  simp only [tmul_add, QuotientAddGroup.mk_add, map_add, ha, hb]
              | tmul n₁ n₂ =>
                  simp only [moduleBifunctorOfTensorProductModule_map_second, moduleBifunctorOfFactorModules_map_second,
                    ModuleCat.comp_apply]
                  erw [RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor_map_tmul]
                  erw [RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom_hom, map_tmul]
                  simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq]
                  rw [comparisonObjIso_hom_tmul,
                    comparisonObjIso_hom_tmul]
                  erw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
                  rw [RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor_map_tmul])

include hN in
/-- The component of the fixed-first-variable comparison map is the forward map of the objectwise comparison. -/
@[simp] theorem comparisonIsoApp_hom_app (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (comparisonIsoApp k A₁ A₂ N₁ N₂ hN X).hom.app Y =
      (comparisonObjIso k A₁ A₂ N₁ N₂ hN X Y).hom :=
  rfl

include hN in

/-- The tensor-product-module bifunctor is isomorphic to the factor-module bifunctor under the stated pure-tensor action rule. -/
noncomputable def comparisonIso :
    moduleBifunctorOfTensorProductModule k A₁ A₂ N₁ N₂ ≅ moduleBifunctorOfFactorModules k A₁ A₂ N₁ N₂ :=
  NatIso.ofComponents
    (fun X => comparisonIsoApp k A₁ A₂ N₁ N₂ hN X)
    (by
      intro X X' f
      apply NatTrans.ext
      apply funext
      intro Y
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [QuotientAddGroup.mk_add, map_add, ha, hb]
      | tmul p q =>
          induction p using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb =>
              simp only [add_tmul, QuotientAddGroup.mk_add, map_add, ha, hb]
          | tmul x y =>
              induction q using TensorProduct.induction_on with
              | zero => simp
              | add a b ha hb =>
                  simp only [tmul_add, QuotientAddGroup.mk_add, map_add, ha, hb]
              | tmul n₁ n₂ =>
                  simp only [NatTrans.comp_app, comparisonIsoApp_hom_app,
                    moduleBifunctorOfTensorProductModule_map_first, moduleBifunctorOfFactorModules_map_first,
                    ModuleCat.comp_apply]
                  erw [RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor_map_tmul]
                  erw [RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom_hom, map_tmul]
                  simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq]
                  rw [comparisonObjIso_hom_tmul,
                    comparisonObjIso_hom_tmul]
                  erw [ModuleCat.MonoidalCategory.whiskerRight_apply]
                  rw [RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor_map_tmul])

end RepresentationTheory.TensorProduct.RightModuleBifunctor.TensorProduct.RightModuleBifunctor

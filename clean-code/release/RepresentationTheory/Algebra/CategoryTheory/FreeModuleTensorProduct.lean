/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat
import RepresentationTheory.ModulePairing.Projective
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite

set_option backward.isDefEq.respectTransparency false

open TensorProduct MulOpposite CategoryTheory

namespace RepresentationTheory.Algebra.CategoryTheory.FreeModuleTensorProduct

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance]
  RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.leftRestrictionModule
  RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.rightRestrictionModule
  RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.leftRestrictionModule_isScalarTower
  RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.rightRestrictionModule_isScalarTower
  RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductModule

/-- The carrier of the indicated free right module is linearly equivalent to finitely supported functions into the opposite ring. -/
noncomputable def freeModuleLinearEquivFinsuppLeft (I₁ : Type u) :
    (↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) ≃ₗ[k] (I₁ →₀ A₁ᵐᵒᵖ) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₁ᵐᵒᵖ c (id x : I₁ →₀ A₁ᵐᵒᵖ)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- The carrier of the indicated free right module is linearly equivalent to finitely supported functions into the opposite ring. -/
noncomputable def freeModuleLinearEquivFinsuppRight (I₂ : Type u) :
    (↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) ≃ₗ[k] (I₂ →₀ A₂ᵐᵒᵖ) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₂ᵐᵒᵖ c (id x : I₂ →₀ A₂ᵐᵒᵖ)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- The displayed equivalence acts as the identity on each free-module element. -/
@[simp] lemma freeModuleLinearEquivFinsuppLeft_apply (I₁ : Type u)
    (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) :
    freeModuleLinearEquivFinsuppLeft k A₁ I₁ x = x := rfl

/-- The displayed equivalence acts as the identity on each free-module element. -/
@[simp] lemma freeModuleLinearEquivFinsuppRight_apply (I₂ : Type u)
    (x : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) :
    freeModuleLinearEquivFinsuppRight k A₂ I₂ x = x := rfl

/-- Evaluating the equivalence after an opposite-ring scalar action multiplies the corresponding coordinate. -/
lemma freeModuleLinearEquivFinsuppLeft_smul_apply (I₁ : Type u) (a₁ : A₁)
    (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) (i : I₁) :
    freeModuleLinearEquivFinsuppLeft k A₁ I₁ (op a₁ • x) i =
      op a₁ * freeModuleLinearEquivFinsuppLeft k A₁ I₁ x i := by
  change (op a₁ • freeModuleLinearEquivFinsuppLeft k A₁ I₁ x) i = _
  rw [Finsupp.smul_apply, smul_eq_mul]

/-- Evaluating the equivalence after an opposite-ring scalar action multiplies the corresponding coordinate. -/
lemma freeModuleLinearEquivFinsuppRight_smul_apply (I₂ : Type u) (a₂ : A₂)
    (y : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) (j : I₂) :
    freeModuleLinearEquivFinsuppRight k A₂ I₂ (op a₂ • y) j =
      op a₂ * freeModuleLinearEquivFinsuppRight k A₂ I₂ y j := by
  change (op a₂ • freeModuleLinearEquivFinsuppRight k A₂ I₂ y) j = _
  rw [Finsupp.smul_apply, smul_eq_mul]

/-- The displayed tensor product of free-module carriers is linearly equivalent over the base ring to finitely supported functions on pairs of indices. -/
noncomputable def freeModuleTensorLinearEquivFinsuppBase (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂))) ≃ₗ[k]
      (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)ᵐᵒᵖ) :=
  (TensorProduct.congr (freeModuleLinearEquivFinsuppLeft k A₁ I₁)
      (freeModuleLinearEquivFinsuppRight k A₂ I₂)) ≪≫ₗ
    (finsuppTensorFinsupp k k A₁ᵐᵒᵖ A₂ᵐᵒᵖ I₁ I₂) ≪≫ₗ
    (Finsupp.mapRange.linearEquiv
      (Algebra.TensorProduct.opAlgEquiv k k A₁ A₂).toLinearEquiv)

/-- At a pair of indices, the equivalence applied to a pure tensor is the image of the tensor of its two coordinates. -/
lemma freeModuleTensorLinearEquivFinsuppBase_tmul_apply (I₁ I₂ : Type u)
    (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) (y : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂))
    (i : I₁) (j : I₂) :
    freeModuleTensorLinearEquivFinsuppBase k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) (i, j)
      = Algebra.TensorProduct.opAlgEquiv k k A₁ A₂
          (freeModuleLinearEquivFinsuppLeft k A₁ I₁ x i ⊗ₜ[k]
            freeModuleLinearEquivFinsuppRight k A₂ I₂ y j) := by
  simp only [freeModuleTensorLinearEquivFinsuppBase, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply,
    finsuppTensorFinsupp_apply, AlgEquiv.toLinearEquiv_apply]

/-- The base-linear equivalence carries a tensor of scalar multiples to the corresponding opposite tensor-product scalar multiple. -/
lemma freeModuleTensorLinearEquivFinsuppBase_tmul_smul (I₁ I₂ : Type u)
    (a₁ : A₁) (a₂ : A₂) (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁))
    (y : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) :
    freeModuleTensorLinearEquivFinsuppBase k A₁ A₂ I₁ I₂
        ((op a₁ • x) ⊗ₜ[k] (op a₂ • y)) =
      (op (a₁ ⊗ₜ[k] a₂) : (A₁ ⊗[k] A₂)ᵐᵒᵖ) •
        freeModuleTensorLinearEquivFinsuppBase k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) := by
  refine Finsupp.ext fun p => ?_
  obtain ⟨i, j⟩ := p
  rw [freeModuleTensorLinearEquivFinsuppBase_tmul_apply, Finsupp.smul_apply,
    freeModuleTensorLinearEquivFinsuppBase_tmul_apply, smul_eq_mul,
    freeModuleLinearEquivFinsuppLeft_smul_apply,
    freeModuleLinearEquivFinsuppRight_smul_apply, ← Algebra.TensorProduct.tmul_mul_tmul,
    map_mul, Algebra.TensorProduct.opAlgEquiv_tmul]
  rfl

/-- The tensor product of the displayed free-module carriers is linearly equivalent to finitely supported functions on the product index type over the opposite tensor-product ring. -/
noncomputable def freeModuleTensorLinearEquivFinsupp (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)))
      ≃ₗ[(A₁ ⊗[k] A₂)ᵐᵒᵖ] (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)ᵐᵒᵖ) where
  toFun := freeModuleTensorLinearEquivFinsuppBase k A₁ A₂ I₁ I₂
  map_add' := map_add _
  map_smul' r z := by
    induction r using MulOpposite.rec' with
    | _ s =>
      induction s using TensorProduct.induction_on generalizing z with
      | zero => simp
      | tmul a₁ a₂ =>
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          rw [RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProduct_tmul_smul,
            RingHom.id_apply, freeModuleTensorLinearEquivFinsuppBase_tmul_smul]
        | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
      | add s1 s2 ih1 ih2 => simp only [MulOpposite.op_add, add_smul, map_add, ih1, ih2]
  invFun := (freeModuleTensorLinearEquivFinsuppBase k A₁ A₂ I₁ I₂).symm
  left_inv := (freeModuleTensorLinearEquivFinsuppBase k A₁ A₂ I₁ I₂).left_inv
  right_inv := (freeModuleTensorLinearEquivFinsuppBase k A₁ A₂ I₁ I₂).right_inv

/-- Applying the displayed binary construction to free modules on two index types yields a projective object. -/
theorem projective_binaryConstruction_freeModules (I₁ I₂ : Type u) :
    Projective
      (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂
        ((ModuleCat.free A₁ᵐᵒᵖ).obj I₁) ((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) :=
  ModuleCat.projective_of_free
    (Module.Basis.ofRepr (freeModuleTensorLinearEquivFinsupp k A₁ A₂ I₁ I₂))

variable {A₁ A₂}

/-- Combines two retracts into a retract between the corresponding values of the displayed binary construction. -/
noncomputable def binaryConstruction_retract
    {X F₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {Y F₂ : ModuleCat.{u} A₂ᵐᵒᵖ}
    (hX : Retract X F₁) (hY : Retract Y F₂) :
    Retract
      (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ X Y)
      (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ F₁ F₂) where
  i := RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k hX.i hY.i
  r := RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k hX.r hY.r
  retract := by
    rw [← RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom_comp,
      hX.retract, hY.retract,
      RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom_id]

variable (A₁ A₂)

/-- The value of the displayed two-variable functor at projective module objects is projective. -/
theorem projective_binaryFunctor_obj (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ)
    [Projective X] [Projective Y] :
    Projective
      ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj X |>.obj Y) := by
  -- `X` is a retract of the free module on its underlying set, split by projectivity.
  let εX : (ModuleCat.free A₁ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₁ᵐᵒᵖ)).obj X) ⟶ X :=
    (ModuleCat.adj A₁ᵐᵒᵖ).counit.app X
  let hX : Retract X ((ModuleCat.free A₁ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₁ᵐᵒᵖ)).obj X)) :=
    { i := Projective.factorThru (𝟙 X) εX
      r := εX
      retract := Projective.factorThru_comp (𝟙 X) εX }
  let εY : (ModuleCat.free A₂ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₂ᵐᵒᵖ)).obj Y) ⟶ Y :=
    (ModuleCat.adj A₂ᵐᵒᵖ).counit.app Y
  let hY : Retract Y ((ModuleCat.free A₂ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₂ᵐᵒᵖ)).obj Y)) :=
    { i := Projective.factorThru (𝟙 Y) εY
      r := εY
      retract := Projective.factorThru_comp (𝟙 Y) εY }
  haveI : Projective
      (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂
        ((ModuleCat.free A₁ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₁ᵐᵒᵖ)).obj X))
        ((ModuleCat.free A₂ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₂ᵐᵒᵖ)).obj Y))) :=
    projective_binaryConstruction_freeModules k A₁ A₂ _ _
  exact (binaryConstruction_retract k hX hY).projective

end RepresentationTheory.Algebra.CategoryTheory.FreeModuleTensorProduct

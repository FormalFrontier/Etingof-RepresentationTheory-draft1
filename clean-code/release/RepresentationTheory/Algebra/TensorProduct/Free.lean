/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.TensorProduct.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of free modules

This module identifies tensor products of free module-category objects with free modules and proves
that tensor products preserve projectivity.
-/

open TensorProduct CategoryTheory

namespace RepresentationTheory.Algebra.TensorProduct.Free

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance] ModuleCat.moduleCarrier ModuleCat.moduleCarrierAux
  ModuleCat.isScalarTower ModuleCat.isScalarTowerAux ModuleCat.tensorProductModule

/-! ### Free case -/

/-- Linear equivalence from a free module carrier to finitely supported coefficient functions. -/
noncomputable def TensorProduct.leftFreeToFinsupp (I₁ : Type u) :
    (↑((ModuleCat.free A₁).obj I₁)) ≃ₗ[k] (I₁ →₀ A₁) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₁ c (id x : I₁ →₀ A₁)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- Linear equivalence from the second free module carrier to finitely supported coefficient
functions. -/
noncomputable def TensorProduct.rightFreeToFinsupp (I₂ : Type u) :
    (↑((ModuleCat.free A₂).obj I₂)) ≃ₗ[k] (I₂ →₀ A₂) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₂ c (id x : I₂ →₀ A₂)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- The left free-module equivalence acts as the identity on carrier elements. -/
@[simp] lemma TensorProduct.leftFreeToFinsupp_apply (I₁ : Type u)
    (x : ↑((ModuleCat.free A₁).obj I₁)) :
    TensorProduct.leftFreeToFinsupp k A₁ I₁ x = x := rfl

/-- The right free-module equivalence acts as the identity on carrier elements. -/
@[simp] lemma TensorProduct.rightFreeToFinsupp_apply (I₂ : Type u)
    (x : ↑((ModuleCat.free A₂).obj I₂)) :
    TensorProduct.rightFreeToFinsupp k A₂ I₂ x = x := rfl

/-- Evaluation after the left free-module equivalence commutes with scalar multiplication. -/
lemma TensorProduct.leftFreeToFinsupp_smul_apply (I₁ : Type u) (a₁ : A₁)
    (x : ↑((ModuleCat.free A₁).obj I₁)) (i : I₁) :
    TensorProduct.leftFreeToFinsupp k A₁ I₁ (a₁ • x) i =
      a₁ * TensorProduct.leftFreeToFinsupp k A₁ I₁ x i := by
  change (a₁ • TensorProduct.leftFreeToFinsupp k A₁ I₁ x) i = _
  rw [Finsupp.smul_apply, smul_eq_mul]

/-- Evaluation after the right free-module equivalence commutes with scalar multiplication. -/
lemma TensorProduct.rightFreeToFinsupp_smul_apply (I₂ : Type u) (a₂ : A₂)
    (y : ↑((ModuleCat.free A₂).obj I₂)) (j : I₂) :
    TensorProduct.rightFreeToFinsupp k A₂ I₂ (a₂ • y) j =
      a₂ * TensorProduct.rightFreeToFinsupp k A₂ I₂ y j := by
  change (a₂ • TensorProduct.rightFreeToFinsupp k A₂ I₂ y) j = _
  rw [Finsupp.smul_apply, smul_eq_mul]

/-- Linear equivalence from a tensor product of free module carriers to functions on pairs with
finite support. -/
noncomputable def TensorProduct.freeToFinsupp (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂).obj I₂))) ≃ₗ[k]
      (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)) :=
  (TensorProduct.congr (TensorProduct.leftFreeToFinsupp k A₁ I₁)
    (TensorProduct.rightFreeToFinsupp k A₂ I₂)) ≪≫ₗ
    (finsuppTensorFinsupp k k A₁ A₂ I₁ I₂)

/-- At a pair of indices, the free tensor equivalence of a pure tensor is the tensor of the
evaluated coefficients. -/
lemma TensorProduct.freeToFinsupp_tmul_apply (I₁ I₂ : Type u)
    (x : ↑((ModuleCat.free A₁).obj I₁)) (y : ↑((ModuleCat.free A₂).obj I₂))
    (i : I₁) (j : I₂) :
    TensorProduct.freeToFinsupp k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) (i, j) =
      TensorProduct.leftFreeToFinsupp k A₁ I₁ x i ⊗ₜ[k]
        TensorProduct.rightFreeToFinsupp k A₂ I₂ y j := by
  simp only [TensorProduct.freeToFinsupp, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    finsuppTensorFinsupp_apply]

/-- The free tensor equivalence carries scalar multiples of pure tensors to the corresponding
product scalar action. -/
lemma TensorProduct.freeToFinsupp_smul_tmul (I₁ I₂ : Type u) (a₁ : A₁) (a₂ : A₂)
    (x : ↑((ModuleCat.free A₁).obj I₁)) (y : ↑((ModuleCat.free A₂).obj I₂)) :
    TensorProduct.freeToFinsupp k A₁ A₂ I₁ I₂ ((a₁ • x) ⊗ₜ[k] (a₂ • y)) =
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) •
        TensorProduct.freeToFinsupp k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) := by
  refine Finsupp.ext fun p => ?_
  obtain ⟨i, j⟩ := p
  rw [TensorProduct.freeToFinsupp_tmul_apply, Finsupp.smul_apply,
    TensorProduct.freeToFinsupp_tmul_apply, TensorProduct.leftFreeToFinsupp_smul_apply,
    TensorProduct.rightFreeToFinsupp_smul_apply, smul_eq_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- A linear equivalence over the tensor product algebra from free module tensors to finitely
supported functions on pairs. -/
noncomputable def TensorProduct.freeToFinsuppOverTensorProduct (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂).obj I₂)))
      ≃ₗ[(A₁ ⊗[k] A₂)] (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)) where
  toFun := TensorProduct.freeToFinsupp k A₁ A₂ I₁ I₂
  map_add' := map_add _
  map_smul' r z := by
    induction r using TensorProduct.induction_on generalizing z with
    | zero => simp
    | tmul a₁ a₂ =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [RepresentationTheory.Algebra.TensorProduct.ModuleCat.smul_tmul, RingHom.id_apply,
          TensorProduct.freeToFinsupp_smul_tmul]
      | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
    | add s1 s2 ih1 ih2 => simp only [add_smul, map_add, ih1, ih2]
  invFun := (TensorProduct.freeToFinsupp k A₁ A₂ I₁ I₂).symm
  left_inv := (TensorProduct.freeToFinsupp k A₁ A₂ I₁ I₂).left_inv
  right_inv := (TensorProduct.freeToFinsupp k A₁ A₂ I₁ I₂).right_inv

/-- Free objects are projective after applying the displayed binary module construction. -/
theorem ModuleCat.projective_tensorProductFree (I₁ I₂ : Type u) :
    Projective (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂
      ((ModuleCat.free A₁).obj I₁)
      ((ModuleCat.free A₂).obj I₂)) :=
  ModuleCat.projective_of_free
    (Module.Basis.ofRepr (TensorProduct.freeToFinsuppOverTensorProduct k A₁ A₂ I₁ I₂))

/-! ### Retract case -/

variable {A₁ A₂}

/-- Constructs a retract between the results of the displayed binary module construction. -/
noncomputable def CategoryTheory.Retract.tensorProduct
    {X F₁ : ModuleCat.{u} A₁} {Y F₂ : ModuleCat.{u} A₂}
    (hX : Retract X F₁) (hY : Retract Y F₂) :
    Retract (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ X Y)
      (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ F₁ F₂) where
  i := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k hX.i hY.i
  r := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap k hX.r hY.r
  retract := by
    rw [← RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap_comp, hX.retract,
      hY.retract, RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap_id]

variable (A₁ A₂)

/-- The displayed iterated module construction preserves projective objects. -/
theorem ModuleCat.projective_tensorProduct (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂)
    [Projective X] [Projective Y] :
    Projective
      ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj X
        |>.obj Y) := by
  let εX : (ModuleCat.free A₁).obj ((forget (ModuleCat.{u} A₁)).obj X) ⟶ X :=
    (ModuleCat.adj A₁).counit.app X
  let hX : Retract X ((ModuleCat.free A₁).obj ((forget (ModuleCat.{u} A₁)).obj X)) :=
    { i := Projective.factorThru (𝟙 X) εX
      r := εX
      retract := Projective.factorThru_comp (𝟙 X) εX }
  let εY : (ModuleCat.free A₂).obj ((forget (ModuleCat.{u} A₂)).obj Y) ⟶ Y :=
    (ModuleCat.adj A₂).counit.app Y
  let hY : Retract Y ((ModuleCat.free A₂).obj ((forget (ModuleCat.{u} A₂)).obj Y)) :=
    { i := Projective.factorThru (𝟙 Y) εY
      r := εY
      retract := Projective.factorThru_comp (𝟙 Y) εY }
  haveI : Projective (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂
      ((ModuleCat.free A₁).obj ((forget (ModuleCat.{u} A₁)).obj X))
      ((ModuleCat.free A₂).obj ((forget (ModuleCat.{u} A₂)).obj Y))) :=
    ModuleCat.projective_tensorProductFree k A₁ A₂ _ _
  exact (CategoryTheory.Retract.tensorProduct k hX hY).projective

end RepresentationTheory.Algebra.TensorProduct.Free

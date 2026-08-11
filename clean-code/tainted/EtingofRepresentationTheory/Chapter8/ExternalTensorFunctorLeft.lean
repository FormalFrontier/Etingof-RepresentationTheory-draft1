import EtingofRepresentationTheory.Chapter8.ExternalTensorModuleLeft
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# The external tensor product bifunctor (left modules)

`Etingof.extTensorModuleLeft` (in `ExternalTensorModuleLeft.lean`) equips `M₁ ⊗[k] M₂` with a
**left** `A₁ ⊗[k] A₂`-module structure whenever `M₁` is a left `A₁`-module and `M₂` a left
`A₂`-module, both `k`-linearly. This file packages that pointwise construction as a **bifunctor**
between module categories:

* `Etingof.extTensorFunctorLeft :
    ModuleCat.{u} A₁ ⥤ ModuleCat.{u} A₂ ⥤ ModuleCat.{u} (A₁ ⊗[k] A₂)`

sending `(X, Y)` to `X ⊗[k] Y` with the external action, and a pair of module maps `(f, g)` to
`TensorProduct.map f g`.

This is the left-module twin of `Etingof.extTensorFunctor` (in `ExternalTensorFunctor.lean`), built
for the `Ext` half of Problem 8.2.8. It is simpler than the right-module version: no
`Algebra.TensorProduct.opAlgEquiv` transport is needed because the action lands directly in
`A₁ ⊗[k] A₂`.

## Restriction of scalars

An object `X : ModuleCat A₁` carries only a `Module A₁ X`. Since `A₁` is a `k`-algebra, we obtain
the `Module k X` and `IsScalarTower k A₁ X` needed by `extTensorModuleLeft` by restriction of
scalars along `algebraMap k A₁` (`Module.compHom`). These are provided as `local instance`s, keyed
on the `ModuleCat` carriers, so they do not leak diamonds onto the algebras themselves.
-/

open TensorProduct CategoryTheory

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

/-- Restriction of scalars along `k → A₁` gives every left `A₁`-module a `k`-module structure. -/
noncomputable local instance restrictModule₁L (X : ModuleCat.{u} A₁) : Module k X :=
  Module.compHom X (algebraMap k A₁)

/-- Restriction of scalars along `k → A₂` gives every left `A₂`-module a `k`-module structure. -/
noncomputable local instance restrictModule₂L (Y : ModuleCat.{u} A₂) : Module k Y :=
  Module.compHom Y (algebraMap k A₂)

local instance tower₁L (X : ModuleCat.{u} A₁) : IsScalarTower k A₁ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance tower₂L (Y : ModuleCat.{u} A₂) : IsScalarTower k A₂ Y :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- The external `A₁ ⊗[k] A₂`-action on `X ⊗[k] Y`, from `Etingof.extTensorModuleLeft`. -/
noncomputable local instance extModuleL (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    Module (A₁ ⊗[k] A₂) (X ⊗[k] Y) := extTensorModuleLeft k A₁ A₂ X Y

/-- The external action on a simple tensor, phrased with the ambient `•` of `extModuleL`. This
restates `Etingof.extTensorModuleLeft_smul_tmul` so that `simp`/`rw` fire against the instance used
throughout this file. -/
@[simp] theorem extTensorFunctorLeft_smul_tmul (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂)
    (a₁ : A₁) (a₂ : A₂) (m₁ : X) (m₂ : Y) :
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (m₁ ⊗ₜ[k] m₂ : X ⊗[k] Y)
      = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂) :=
  extTensorModuleLeft_smul_tmul k A₁ A₂ X Y a₁ a₂ m₁ m₂

/-- Object map of the external tensor bifunctor: `X ⊗[k] Y` with its external action. -/
noncomputable def extTensorFunctorLeftObj (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    ModuleCat.{u} (A₁ ⊗[k] A₂) :=
  ModuleCat.of (A₁ ⊗[k] A₂) (X ⊗[k] Y)

variable {A₁ A₂}

/-- The underlying `A₁ ⊗[k] A₂`-linear map of the bifunctor on a pair of morphisms: the tensor
product `TensorProduct.map f g`, which is `A₁ ⊗[k] A₂`-linear for the external action (checked on
simple tensors). -/
noncomputable def extTensorFunctorLeftMapHom {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') (g : Y ⟶ Y') :
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
        simp only [extTensorFunctorLeft_smul_tmul, TensorProduct.map_tmul,
          LinearMap.restrictScalars_apply, map_smul]
      | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
    | add s1 s2 ih1 ih2 => simp only [add_smul, map_add, ih1, ih2]

@[simp] theorem extTensorFunctorLeftMapHom_tmul {X X' : ModuleCat.{u} A₁}
    {Y Y' : ModuleCat.{u} A₂} (f : X ⟶ X') (g : Y ⟶ Y') (m₁ : X) (m₂ : Y) :
    extTensorFunctorLeftMapHom k f g (m₁ ⊗ₜ[k] m₂) = f.hom m₁ ⊗ₜ[k] g.hom m₂ := rfl

theorem extTensorFunctorLeftMapHom_id (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    extTensorFunctorLeftMapHom k (𝟙 X) (𝟙 Y) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add, LinearMap.id_coe, id_eq]

theorem extTensorFunctorLeftMapHom_comp {X X' X'' : ModuleCat.{u} A₁}
    {Y Y' Y'' : ModuleCat.{u} A₂} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'') (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    extTensorFunctorLeftMapHom k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = (extTensorFunctorLeftMapHom k f₂ g₂) ∘ₗ (extTensorFunctorLeftMapHom k f₁ g₁) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- The bifunctor on a pair of morphisms, as a morphism in `ModuleCat (A₁ ⊗[k] A₂)`. -/
noncomputable def extTensorFunctorLeftMap {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    extTensorFunctorLeftObj k A₁ A₂ X Y ⟶ extTensorFunctorLeftObj k A₁ A₂ X' Y' :=
  ModuleCat.ofHom (extTensorFunctorLeftMapHom k f g)

@[simp] theorem extTensorFunctorLeftMap_hom {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (extTensorFunctorLeftMap k f g).hom = extTensorFunctorLeftMapHom k f g := rfl

theorem extTensorFunctorLeftMap_id (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    extTensorFunctorLeftMap k (𝟙 X) (𝟙 Y) = 𝟙 (extTensorFunctorLeftObj k A₁ A₂ X Y) := by
  apply ModuleCat.hom_ext
  rw [extTensorFunctorLeftMap_hom, extTensorFunctorLeftMapHom_id, ModuleCat.hom_id]

theorem extTensorFunctorLeftMap_comp {X X' X'' : ModuleCat.{u} A₁}
    {Y Y' Y'' : ModuleCat.{u} A₂} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'') (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    extTensorFunctorLeftMap k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = extTensorFunctorLeftMap k f₁ g₁ ≫ extTensorFunctorLeftMap k f₂ g₂ := by
  apply ModuleCat.hom_ext
  rw [extTensorFunctorLeftMap_hom, extTensorFunctorLeftMapHom_comp, ModuleCat.hom_comp,
    extTensorFunctorLeftMap_hom, extTensorFunctorLeftMap_hom]

variable (A₁ A₂)

/-- The **external tensor product bifunctor**
`ModuleCat A₁ ⥤ ModuleCat A₂ ⥤ ModuleCat (A₁ ⊗[k] A₂)`, sending `(X, Y)` to `X ⊗[k] Y` with the
external action and `(f, g)` to `TensorProduct.map f g`. -/
noncomputable def extTensorFunctorLeft :
    ModuleCat.{u} A₁ ⥤ ModuleCat.{u} A₂ ⥤ ModuleCat.{u} (A₁ ⊗[k] A₂) where
  obj X :=
    { obj := fun Y => extTensorFunctorLeftObj k A₁ A₂ X Y
      map := fun {_ _} g => extTensorFunctorLeftMap k (𝟙 X) g
      map_id := fun Y => extTensorFunctorLeftMap_id k X Y
      map_comp := fun {_ _ _} g₁ g₂ => by
        have h := extTensorFunctorLeftMap_comp k (𝟙 X) (𝟙 X) g₁ g₂
        rwa [Category.comp_id] at h }
  map := fun {X X'} f =>
    { app := fun Y => extTensorFunctorLeftMap k f (𝟙 Y)
      naturality := fun {Y Y'} g => by
        have h1 := extTensorFunctorLeftMap_comp k (𝟙 X) f g (𝟙 Y')
        have h2 := extTensorFunctorLeftMap_comp k f (𝟙 X') (𝟙 Y) g
        rw [Category.id_comp, Category.comp_id] at h1
        rw [Category.comp_id, Category.id_comp] at h2
        rw [← h1, ← h2] }
  map_id := fun X => by
    apply NatTrans.ext
    funext Y
    simpa using extTensorFunctorLeftMap_id k X Y
  map_comp := fun {X X' X''} f₁ f₂ => by
    apply NatTrans.ext
    funext Y
    have h := extTensorFunctorLeftMap_comp k f₁ f₂ (𝟙 Y) (𝟙 Y)
    rw [Category.comp_id] at h
    simpa using h

end Etingof

import EtingofRepresentationTheory.Chapter8.ExternalTensorModule
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# The external tensor product bifunctor

`Etingof.extTensorModule` (in `ExternalTensorModule.lean`) equips `M₁ ⊗[k] M₂` with an
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`-module structure whenever `M₁` is a right `A₁`-module (a left `A₁ᵐᵒᵖ`-module)
and `M₂` a right `A₂`-module. This file packages that pointwise construction as a **bifunctor**
between module categories:

* `Etingof.extTensorFunctor :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ`

sending `(X, Y)` to `X ⊗[k] Y` with the external action, and a pair of module maps `(f, g)` to
`TensorProduct.map f g`.

## Restriction of scalars

An object `X : ModuleCat A₁ᵐᵒᵖ` carries only a `Module A₁ᵐᵒᵖ X`. Since `A₁ᵐᵒᵖ` is a `k`-algebra,
we obtain the `Module k X` and `IsScalarTower k A₁ᵐᵒᵖ X` needed by `extTensorModule` by restriction
of scalars along `algebraMap k A₁ᵐᵒᵖ` (`Module.compHom`). These are provided as `local instance`s,
keyed on the `ModuleCat` carriers, so they do not leak diamonds onto the algebras themselves.

This bifunctor is the second piece of the tensor-of-resolutions construction for the Künneth
formula for `Tor` over a tensor product of algebras (Problem 8.2.8): it is applied degreewise to
two projective resolutions.
-/

open TensorProduct MulOpposite CategoryTheory

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

/-- Restriction of scalars along `k → A₁ᵐᵒᵖ` gives every left `A₁ᵐᵒᵖ`-module a `k`-module
structure. -/
noncomputable local instance restrictModule₁ (X : ModuleCat.{u} A₁ᵐᵒᵖ) : Module k X :=
  Module.compHom X (algebraMap k A₁ᵐᵒᵖ)

/-- Restriction of scalars along `k → A₂ᵐᵒᵖ` gives every left `A₂ᵐᵒᵖ`-module a `k`-module
structure. -/
noncomputable local instance restrictModule₂ (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : Module k Y :=
  Module.compHom Y (algebraMap k A₂ᵐᵒᵖ)

local instance tower₁ (X : ModuleCat.{u} A₁ᵐᵒᵖ) : IsScalarTower k A₁ᵐᵒᵖ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance tower₂ (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : IsScalarTower k A₂ᵐᵒᵖ Y :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- The external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action on `X ⊗[k] Y`, from `Etingof.extTensorModule`. -/
noncomputable local instance extModule (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) := extTensorModule k A₁ A₂ X Y

/-- The external action on a simple tensor, phrased with the ambient `•` of `extModule`. This
restates `Etingof.extTensorModule_op_smul_tmul` so that `simp`/`rw` fire against the instance used
throughout this file. -/
@[simp] theorem extTensorFunctor_op_smul_tmul (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ)
    (a₁ : A₁) (a₂ : A₂) (m₁ : X) (m₂ : Y) :
    (op (a₁ ⊗ₜ[k] a₂) : (A₁ ⊗[k] A₂)ᵐᵒᵖ) • (m₁ ⊗ₜ[k] m₂ : X ⊗[k] Y)
      = (op a₁ • m₁) ⊗ₜ[k] (op a₂ • m₂) :=
  extTensorModule_op_smul_tmul k A₁ A₂ X Y a₁ a₂ m₁ m₂

/-- Object map of the external tensor bifunctor: `X ⊗[k] Y` with its external action. -/
noncomputable def extTensorFunctorObj (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ :=
  ModuleCat.of (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y)

variable {A₁ A₂}

/-- The underlying `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-linear map of the bifunctor on a pair of morphisms: the
tensor product `TensorProduct.map f g`, which is `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-linear for the external action
(checked on simple tensors). -/
noncomputable def extTensorFunctorMapHom {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
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
          simp only [extTensorFunctor_op_smul_tmul, TensorProduct.map_tmul,
            LinearMap.restrictScalars_apply, map_smul]
        | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
      | add s1 s2 ih1 ih2 => simp only [MulOpposite.op_add, add_smul, map_add, ih1, ih2]

@[simp] theorem extTensorFunctorMapHom_tmul {X X' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y') (m₁ : X) (m₂ : Y) :
    extTensorFunctorMapHom k f g (m₁ ⊗ₜ[k] m₂) = f.hom m₁ ⊗ₜ[k] g.hom m₂ := rfl

theorem extTensorFunctorMapHom_id (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    extTensorFunctorMapHom k (𝟙 X) (𝟙 Y) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add, LinearMap.id_coe, id_eq]

theorem extTensorFunctorMapHom_comp {X X' X'' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' Y'' : ModuleCat.{u} A₂ᵐᵒᵖ} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'') (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    extTensorFunctorMapHom k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = (extTensorFunctorMapHom k f₂ g₂) ∘ₗ (extTensorFunctorMapHom k f₁ g₁) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ => rfl
  | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- The bifunctor on a pair of morphisms, as a morphism in `ModuleCat (A₁ ⊗[k] A₂)ᵐᵒᵖ`. -/
noncomputable def extTensorFunctorMap {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    extTensorFunctorObj k A₁ A₂ X Y ⟶ extTensorFunctorObj k A₁ A₂ X' Y' :=
  ModuleCat.ofHom (extTensorFunctorMapHom k f g)

@[simp] theorem extTensorFunctorMap_hom {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (extTensorFunctorMap k f g).hom = extTensorFunctorMapHom k f g := rfl

theorem extTensorFunctorMap_id (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    extTensorFunctorMap k (𝟙 X) (𝟙 Y) = 𝟙 (extTensorFunctorObj k A₁ A₂ X Y) := by
  apply ModuleCat.hom_ext
  rw [extTensorFunctorMap_hom, extTensorFunctorMapHom_id, ModuleCat.hom_id]

theorem extTensorFunctorMap_comp {X X' X'' : ModuleCat.{u} A₁ᵐᵒᵖ}
    {Y Y' Y'' : ModuleCat.{u} A₂ᵐᵒᵖ} (f₁ : X ⟶ X') (f₂ : X' ⟶ X'') (g₁ : Y ⟶ Y') (g₂ : Y' ⟶ Y'') :
    extTensorFunctorMap k (f₁ ≫ f₂) (g₁ ≫ g₂)
      = extTensorFunctorMap k f₁ g₁ ≫ extTensorFunctorMap k f₂ g₂ := by
  apply ModuleCat.hom_ext
  rw [extTensorFunctorMap_hom, extTensorFunctorMapHom_comp, ModuleCat.hom_comp,
    extTensorFunctorMap_hom, extTensorFunctorMap_hom]

variable (A₁ A₂)

/-- The **external tensor product bifunctor**
`ModuleCat A₁ᵐᵒᵖ ⥤ ModuleCat A₂ᵐᵒᵖ ⥤ ModuleCat (A₁ ⊗[k] A₂)ᵐᵒᵖ`, sending `(X, Y)` to `X ⊗[k] Y`
with the external action and `(f, g)` to `TensorProduct.map f g`. -/
noncomputable def extTensorFunctor :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ where
  obj X :=
    { obj := fun Y => extTensorFunctorObj k A₁ A₂ X Y
      map := fun {_ _} g => extTensorFunctorMap k (𝟙 X) g
      map_id := fun Y => extTensorFunctorMap_id k X Y
      map_comp := fun {_ _ _} g₁ g₂ => by
        have h := extTensorFunctorMap_comp k (𝟙 X) (𝟙 X) g₁ g₂
        rwa [Category.comp_id] at h }
  map := fun {X X'} f =>
    { app := fun Y => extTensorFunctorMap k f (𝟙 Y)
      naturality := fun {Y Y'} g => by
        have h1 := extTensorFunctorMap_comp k (𝟙 X) f g (𝟙 Y')
        have h2 := extTensorFunctorMap_comp k f (𝟙 X') (𝟙 Y) g
        rw [Category.id_comp, Category.comp_id] at h1
        rw [Category.comp_id, Category.id_comp] at h2
        rw [← h1, ← h2] }
  map_id := fun X => by
    apply NatTrans.ext
    funext Y
    simpa using extTensorFunctorMap_id k X Y
  map_comp := fun {X X' X''} f₁ f₂ => by
    apply NatTrans.ext
    funext Y
    have h := extTensorFunctorMap_comp k f₁ f₂ (𝟙 Y) (𝟙 Y)
    rw [Category.comp_id] at h
    simpa using h

end Etingof

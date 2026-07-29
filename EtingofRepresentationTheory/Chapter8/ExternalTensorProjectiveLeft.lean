import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctorLeft
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Projectivity of the external tensor product of projectives (left modules)

Left-module twin of `ExternalTensorProjective.lean`. The external-tensor bifunctor
`Etingof.extTensorFunctorLeft` sends `(X, Y)` with `X` a left `A₁`-module and `Y` a left
`A₂`-module to `X ⊗[k] Y` with its `A₁ ⊗[k] A₂`-action. This file proves it **preserves
projectivity**:

* `Etingof.extTensor_projectiveLeft`: if `X` is projective over `A₁` and `Y` is projective over
    `A₂`, then `(extTensorFunctorLeft k A₁ A₂).obj X |>.obj Y` is projective over `A₁ ⊗[k] A₂`.

## Proof route

Identical to the right-module case, but simpler: since the action lands directly in `A₁ ⊗[k] A₂`,
the free case uses `finsuppTensorFinsupp k k A₁ A₂ I₁ I₂` with no `opAlgEquiv` relabeling.

1. **Free case** (`extTensorFunctorLeftObj_projective_of_free`). The external tensor of two *free*
   modules `(I₁ →₀ A₁) ⊗[k] (I₂ →₀ A₂)` is free over `A₁ ⊗[k] A₂`, basis indexed by `I₁ × I₂`.
2. **Retract case** (`extTensorRetractL`, `extTensor_projectiveLeft`). A projective `X` is a retract
   of the free module `↑X →₀ A₁`; the bifunctor sends this pair of retracts to a retract of
   `X ⊗[k] Y` inside the free external tensor, and a retract of a projective is projective.
-/

open TensorProduct CategoryTheory

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

/-! ### Free case -/

/-- The restricted free module `↑((free A₁).obj I₁)` and the standard free module `I₁ →₀ A₁` have
the same underlying `k`-module (their `k`-actions agree by `algebraMap_smul`), so the identity is a
`k`-linear equivalence between them. -/
noncomputable def freeCastEquiv₁L (I₁ : Type u) :
    (↑((ModuleCat.free A₁).obj I₁)) ≃ₗ[k] (I₁ →₀ A₁) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₁ c (id x : I₁ →₀ A₁)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- The second-factor analogue of `freeCastEquiv₁L`. -/
noncomputable def freeCastEquiv₂L (I₂ : Type u) :
    (↑((ModuleCat.free A₂).obj I₂)) ≃ₗ[k] (I₂ →₀ A₂) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₂ c (id x : I₂ →₀ A₂)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma freeCastEquiv₁L_apply (I₁ : Type u) (x : ↑((ModuleCat.free A₁).obj I₁)) :
    freeCastEquiv₁L k A₁ I₁ x = x := rfl

@[simp] lemma freeCastEquiv₂L_apply (I₂ : Type u) (x : ↑((ModuleCat.free A₂).obj I₂)) :
    freeCastEquiv₂L k A₂ I₂ x = x := rfl

lemma freeCastEquiv₁L_smul_apply (I₁ : Type u) (a₁ : A₁)
    (x : ↑((ModuleCat.free A₁).obj I₁)) (i : I₁) :
    freeCastEquiv₁L k A₁ I₁ (a₁ • x) i = a₁ * freeCastEquiv₁L k A₁ I₁ x i := by
  change (a₁ • freeCastEquiv₁L k A₁ I₁ x) i = _
  rw [Finsupp.smul_apply, smul_eq_mul]

lemma freeCastEquiv₂L_smul_apply (I₂ : Type u) (a₂ : A₂)
    (y : ↑((ModuleCat.free A₂).obj I₂)) (j : I₂) :
    freeCastEquiv₂L k A₂ I₂ (a₂ • y) j = a₂ * freeCastEquiv₂L k A₂ I₂ y j := by
  change (a₂ • freeCastEquiv₂L k A₂ I₂ y) j = _
  rw [Finsupp.smul_apply, smul_eq_mul]

/-- The `k`-linear equivalence
`↑((free A₁).obj I₁) ⊗[k] ↑((free A₂).obj I₂) ≃ₗ[k] (I₁ × I₂ →₀ A₁ ⊗[k] A₂)`, built for the
*restricted* `k`-structures on the free carriers via `finsuppTensorFinsupp`. -/
noncomputable def freeExtTensorEquivKL (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂).obj I₂))) ≃ₗ[k]
      (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)) :=
  (TensorProduct.congr (freeCastEquiv₁L k A₁ I₁) (freeCastEquiv₂L k A₂ I₂)) ≪≫ₗ
    (finsuppTensorFinsupp k k A₁ A₂ I₁ I₂)

lemma freeExtTensorEquivKL_tmul_apply (I₁ I₂ : Type u)
    (x : ↑((ModuleCat.free A₁).obj I₁)) (y : ↑((ModuleCat.free A₂).obj I₂))
    (i : I₁) (j : I₂) :
    freeExtTensorEquivKL k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) (i, j)
      = freeCastEquiv₁L k A₁ I₁ x i ⊗ₜ[k] freeCastEquiv₂L k A₂ I₂ y j := by
  simp only [freeExtTensorEquivKL, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    finsuppTensorFinsupp_apply]

/-- `freeExtTensorEquivKL` intertwines the external `A₁ ⊗[k] A₂`-action on a simple tensor `x ⊗ y`
with left multiplication on the free target. -/
lemma freeExtTensorEquivKL_smul_tmul (I₁ I₂ : Type u) (a₁ : A₁) (a₂ : A₂)
    (x : ↑((ModuleCat.free A₁).obj I₁)) (y : ↑((ModuleCat.free A₂).obj I₂)) :
    freeExtTensorEquivKL k A₁ A₂ I₁ I₂ ((a₁ • x) ⊗ₜ[k] (a₂ • y))
      = (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • freeExtTensorEquivKL k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) := by
  refine Finsupp.ext fun p => ?_
  obtain ⟨i, j⟩ := p
  rw [freeExtTensorEquivKL_tmul_apply, Finsupp.smul_apply, freeExtTensorEquivKL_tmul_apply,
    freeCastEquiv₁L_smul_apply, freeCastEquiv₂L_smul_apply, smul_eq_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The `A₁ ⊗[k] A₂`-linear equivalence promoting `freeExtTensorEquivKL` along the external action:
the external tensor of two free modules is *free* over `A₁ ⊗[k] A₂`, with basis `I₁ × I₂`. -/
noncomputable def freeExtTensorEquivL (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂).obj I₂)))
      ≃ₗ[(A₁ ⊗[k] A₂)] (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)) where
  toFun := freeExtTensorEquivKL k A₁ A₂ I₁ I₂
  map_add' := map_add _
  map_smul' r z := by
    induction r using TensorProduct.induction_on generalizing z with
    | zero => simp
    | tmul a₁ a₂ =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [extTensorFunctorLeft_smul_tmul, RingHom.id_apply, freeExtTensorEquivKL_smul_tmul]
      | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
    | add s1 s2 ih1 ih2 => simp only [add_smul, map_add, ih1, ih2]
  invFun := (freeExtTensorEquivKL k A₁ A₂ I₁ I₂).symm
  left_inv := (freeExtTensorEquivKL k A₁ A₂ I₁ I₂).left_inv
  right_inv := (freeExtTensorEquivKL k A₁ A₂ I₁ I₂).right_inv

/-- **Free case.** The external tensor of two free modules is projective (indeed free) over
`A₁ ⊗[k] A₂`. -/
theorem extTensorFunctorLeftObj_projective_of_free (I₁ I₂ : Type u) :
    Projective (extTensorFunctorLeftObj k A₁ A₂
      ((ModuleCat.free A₁).obj I₁)
      ((ModuleCat.free A₂).obj I₂)) :=
  ModuleCat.projective_of_free (Module.Basis.ofRepr (freeExtTensorEquivL k A₁ A₂ I₁ I₂))

/-! ### Retract case -/

variable {A₁ A₂}

/-- The external tensor of two morphisms assembles a pair of retracts into a retract of `X ⊗[k] Y`
inside the free external tensor. -/
noncomputable def extTensorRetractL
    {X F₁ : ModuleCat.{u} A₁} {Y F₂ : ModuleCat.{u} A₂}
    (hX : Retract X F₁) (hY : Retract Y F₂) :
    Retract (extTensorFunctorLeftObj k A₁ A₂ X Y) (extTensorFunctorLeftObj k A₁ A₂ F₁ F₂) where
  i := extTensorFunctorLeftMap k hX.i hY.i
  r := extTensorFunctorLeftMap k hX.r hY.r
  retract := by
    rw [← extTensorFunctorLeftMap_comp, hX.retract, hY.retract, extTensorFunctorLeftMap_id]

variable (A₁ A₂)

/-- **Projectivity of the external tensor of projectives.** If `X` is projective over `A₁` and `Y`
is projective over `A₂`, then `X ⊗[k] Y` with the external `A₁ ⊗[k] A₂`-action is projective. -/
theorem extTensor_projectiveLeft (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂)
    [Projective X] [Projective Y] :
    Projective ((extTensorFunctorLeft k A₁ A₂).obj X |>.obj Y) := by
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
  haveI : Projective (extTensorFunctorLeftObj k A₁ A₂
      ((ModuleCat.free A₁).obj ((forget (ModuleCat.{u} A₁)).obj X))
      ((ModuleCat.free A₂).obj ((forget (ModuleCat.{u} A₂)).obj Y))) :=
    extTensorFunctorLeftObj_projective_of_free k A₁ A₂ _ _
  exact (extTensorRetractL k hX hY).projective

end Etingof

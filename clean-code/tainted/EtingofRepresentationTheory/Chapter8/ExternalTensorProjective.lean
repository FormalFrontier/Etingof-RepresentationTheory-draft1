import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctor
import EtingofRepresentationTheory.Chapter8.TensorProjectiveExact
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite

set_option backward.isDefEq.respectTransparency false

/-!
# Projectivity of the external tensor product of projectives

The external-tensor bifunctor `Etingof.extTensorFunctor` (in `ExternalTensorFunctor.lean`) sends
`(X, Y)` with `X` a right `A₁`-module and `Y` a right `A₂`-module to `X ⊗[k] Y` with its
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action. This file proves that this bifunctor **preserves projectivity**:

* `Etingof.extTensor_projective`:
    if `X` is projective over `A₁ᵐᵒᵖ` and `Y` is projective over `A₂ᵐᵒᵖ`, then
    `(extTensorFunctor k A₁ A₂).obj X |>.obj Y` is projective over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`.

This is the projectivity of each term `(P₁)ⱼ ⊗[k] (P₂)ₘ` of a tensor of projective resolutions,
one of the proof obligations for the Künneth formula for `Tor` over a tensor product of algebras
(Problem 8.2.8).

## Proof route

1. **Free case** (`extTensorFunctorObj_projective_of_free`). The external tensor of two *free*
   modules `(I₁ →₀ A₁ᵐᵒᵖ) ⊗[k] (I₂ →₀ A₂ᵐᵒᵖ)` is free over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`, with basis indexed
   by `I₁ × I₂` (the elements `single i 1 ⊗ single j 1`).
2. **Retract case** (`extTensorRetract`, `extTensor_projective`). A projective `X` is a retract of
   the free module `↑X →₀ A₁ᵐᵒᵖ` (counit of the free/forget adjunction, split by projectivity),
   likewise `Y`. Applying the bifunctor sends this pair of retracts to a retract of `X ⊗[k] Y`
   inside the free external tensor, and a retract of a projective object is projective
   (`CategoryTheory.Retract.projective`).

## The free case, in detail

`finsuppTensorFinsupp` does **not** apply directly to the free case: `extTensorFunctorObj` gives the
free carriers their `k`-module structure by restriction of scalars along `k → A₁ᵐᵒᵖ`
(`Module.compHom`, the `restrictModule` local instances in `ExternalTensorFunctor.lean`), which is
*not* definitionally the standard `Finsupp` `k`-module. We bridge this with the identity `k`-linear
equivalences `freeCastEquiv₁`/`freeCastEquiv₂` (whose underlying map is `id`, `k`-linear because the
two `k`-actions agree by `algebraMap_smul`), transport `finsuppTensorFinsupp` across them
(`freeExtTensorEquivK`), relabel the tensor coefficients with `Algebra.TensorProduct.opAlgEquiv`,
and finally upgrade the `k`-linear equivalence to `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-linear (`freeExtTensorEquiv`) by
checking on the external simple-tensor action (`freeExtTensorEquivK_op_smul_tmul`, whose one
non-formal step is multiplicativity of `opAlgEquiv`).
-/

open TensorProduct MulOpposite CategoryTheory

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance] restrictModule₁ restrictModule₂ tower₁ tower₂ extModule

/-! ### Free case -/

/-- The restricted free module `↑((free A₁ᵐᵒᵖ).obj I₁)` and the standard free module `I₁ →₀ A₁ᵐᵒᵖ`
have the same underlying `k`-module (their `k`-actions agree by `algebraMap_smul`), so the identity
is a `k`-linear equivalence between them. This lets us feed the restricted carrier to
`finsuppTensorFinsupp`, whose statement uses the standard `Finsupp` `k`-module. -/
noncomputable def freeCastEquiv₁ (I₁ : Type u) :
    (↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) ≃ₗ[k] (I₁ →₀ A₁ᵐᵒᵖ) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₁ᵐᵒᵖ c (id x : I₁ →₀ A₁ᵐᵒᵖ)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- The second-factor analogue of `freeCastEquiv₁`. -/
noncomputable def freeCastEquiv₂ (I₂ : Type u) :
    (↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) ≃ₗ[k] (I₂ →₀ A₂ᵐᵒᵖ) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' c x := algebraMap_smul A₂ᵐᵒᵖ c (id x : I₂ →₀ A₂ᵐᵒᵖ)
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma freeCastEquiv₁_apply (I₁ : Type u) (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) :
    freeCastEquiv₁ k A₁ I₁ x = x := rfl

@[simp] lemma freeCastEquiv₂_apply (I₂ : Type u) (x : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) :
    freeCastEquiv₂ k A₂ I₂ x = x := rfl

lemma freeCastEquiv₁_smul_apply (I₁ : Type u) (a₁ : A₁)
    (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) (i : I₁) :
    freeCastEquiv₁ k A₁ I₁ (op a₁ • x) i = op a₁ * freeCastEquiv₁ k A₁ I₁ x i := by
  change (op a₁ • freeCastEquiv₁ k A₁ I₁ x) i = _
  rw [Finsupp.smul_apply, smul_eq_mul]

lemma freeCastEquiv₂_smul_apply (I₂ : Type u) (a₂ : A₂)
    (y : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) (j : I₂) :
    freeCastEquiv₂ k A₂ I₂ (op a₂ • y) j = op a₂ * freeCastEquiv₂ k A₂ I₂ y j := by
  change (op a₂ • freeCastEquiv₂ k A₂ I₂ y) j = _
  rw [Finsupp.smul_apply, smul_eq_mul]

/-- The `k`-linear equivalence
`↑((free A₁ᵐᵒᵖ).obj I₁) ⊗[k] ↑((free A₂ᵐᵒᵖ).obj I₂) ≃ₗ[k] (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)ᵐᵒᵖ)`,
built for the *restricted* `k`-structures on the free carriers via `finsuppTensorFinsupp` (relayed
through `freeCastEquiv₁`/`freeCastEquiv₂`) and `Algebra.TensorProduct.opAlgEquiv`. -/
noncomputable def freeExtTensorEquivK (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂))) ≃ₗ[k]
      (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)ᵐᵒᵖ) :=
  (TensorProduct.congr (freeCastEquiv₁ k A₁ I₁) (freeCastEquiv₂ k A₂ I₂)) ≪≫ₗ
    (finsuppTensorFinsupp k k A₁ᵐᵒᵖ A₂ᵐᵒᵖ I₁ I₂) ≪≫ₗ
    (Finsupp.mapRange.linearEquiv (Algebra.TensorProduct.opAlgEquiv k k A₁ A₂).toLinearEquiv)

lemma freeExtTensorEquivK_tmul_apply (I₁ I₂ : Type u)
    (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) (y : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂))
    (i : I₁) (j : I₂) :
    freeExtTensorEquivK k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) (i, j)
      = Algebra.TensorProduct.opAlgEquiv k k A₁ A₂
          (freeCastEquiv₁ k A₁ I₁ x i ⊗ₜ[k] freeCastEquiv₂ k A₂ I₂ y j) := by
  simp only [freeExtTensorEquivK, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply, finsuppTensorFinsupp_apply,
    AlgEquiv.toLinearEquiv_apply]

/-- `freeExtTensorEquivK` intertwines the external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action on a simple tensor
`x ⊗ y` with left multiplication on the free target. The single non-formal step is multiplicativity
of `Algebra.TensorProduct.opAlgEquiv`. -/
lemma freeExtTensorEquivK_op_smul_tmul (I₁ I₂ : Type u) (a₁ : A₁) (a₂ : A₂)
    (x : ↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) (y : ↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) :
    freeExtTensorEquivK k A₁ A₂ I₁ I₂ ((op a₁ • x) ⊗ₜ[k] (op a₂ • y))
      = (op (a₁ ⊗ₜ[k] a₂) : (A₁ ⊗[k] A₂)ᵐᵒᵖ) • freeExtTensorEquivK k A₁ A₂ I₁ I₂ (x ⊗ₜ[k] y) := by
  refine Finsupp.ext fun p => ?_
  obtain ⟨i, j⟩ := p
  rw [freeExtTensorEquivK_tmul_apply, Finsupp.smul_apply, freeExtTensorEquivK_tmul_apply,
    smul_eq_mul, freeCastEquiv₁_smul_apply, freeCastEquiv₂_smul_apply,
    ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, Algebra.TensorProduct.opAlgEquiv_tmul]
  rfl

/-- The `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-linear equivalence promoting `freeExtTensorEquivK` along the external
action: the external tensor of two free modules is *free* over `(A₁ ⊗[k] A₂)ᵐᵒᵖ`, with basis
`I₁ × I₂`. -/
noncomputable def freeExtTensorEquiv (I₁ I₂ : Type u) :
    ((↑((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)) ⊗[k] (↑((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)))
      ≃ₗ[(A₁ ⊗[k] A₂)ᵐᵒᵖ] (I₁ × I₂ →₀ (A₁ ⊗[k] A₂)ᵐᵒᵖ) where
  toFun := freeExtTensorEquivK k A₁ A₂ I₁ I₂
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
          rw [extTensorFunctor_op_smul_tmul, RingHom.id_apply,
            freeExtTensorEquivK_op_smul_tmul]
        | add z1 z2 h1 h2 => simp only [smul_add, map_add, h1, h2]
      | add s1 s2 ih1 ih2 => simp only [MulOpposite.op_add, add_smul, map_add, ih1, ih2]
  invFun := (freeExtTensorEquivK k A₁ A₂ I₁ I₂).symm
  left_inv := (freeExtTensorEquivK k A₁ A₂ I₁ I₂).left_inv
  right_inv := (freeExtTensorEquivK k A₁ A₂ I₁ I₂).right_inv

/-- **Free case.** The external tensor of two free modules is projective (indeed free) over
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`. This is the base case for the retract argument in `extTensor_projective`. -/
theorem extTensorFunctorObj_projective_of_free (I₁ I₂ : Type u) :
    Projective (extTensorFunctorObj k A₁ A₂
      ((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)
      ((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) :=
  ModuleCat.projective_of_free (Module.Basis.ofRepr (freeExtTensorEquiv k A₁ A₂ I₁ I₂))

/-! ### Retract case -/

variable {A₁ A₂}

/-- The external tensor of two morphisms assembles a pair of retracts (of `X` in a free module `F₁`
and `Y` in `F₂`) into a retract of `X ⊗[k] Y` inside the free external tensor `F₁ ⊗[k] F₂`. -/
noncomputable def extTensorRetract
    {X F₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {Y F₂ : ModuleCat.{u} A₂ᵐᵒᵖ}
    (hX : Retract X F₁) (hY : Retract Y F₂) :
    Retract (extTensorFunctorObj k A₁ A₂ X Y) (extTensorFunctorObj k A₁ A₂ F₁ F₂) where
  i := extTensorFunctorMap k hX.i hY.i
  r := extTensorFunctorMap k hX.r hY.r
  retract := by
    rw [← extTensorFunctorMap_comp, hX.retract, hY.retract, extTensorFunctorMap_id]

variable (A₁ A₂)

/-- **Projectivity of the external tensor of projectives.** If `X` is projective over `A₁ᵐᵒᵖ` and
`Y` is projective over `A₂ᵐᵒᵖ`, then `X ⊗[k] Y` with the external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action is
projective. Concretely, `(P₁)ⱼ ⊗[k] (P₂)ₘ` is projective over `(A₁ ⊗[k] A₂)ᵐᵒᵖ` when the factors
are projective over `A₁ᵐᵒᵖ`, `A₂ᵐᵒᵖ`. -/
theorem extTensor_projective (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ)
    [Projective X] [Projective Y] :
    Projective ((extTensorFunctor k A₁ A₂).obj X |>.obj Y) := by
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
  haveI : Projective (extTensorFunctorObj k A₁ A₂
      ((ModuleCat.free A₁ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₁ᵐᵒᵖ)).obj X))
      ((ModuleCat.free A₂ᵐᵒᵖ).obj ((forget (ModuleCat.{u} A₂ᵐᵒᵖ)).obj Y))) :=
    extTensorFunctorObj_projective_of_free k A₁ A₂ _ _
  exact (extTensorRetract k hX hY).projective

end Etingof

import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctor
import EtingofRepresentationTheory.Chapter8.TensorProjectiveExact
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Basic

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
   by `I₁ × I₂`.
2. **Retract case** (`extTensorRetract`, `extTensor_projective`). A projective `X` is a retract of
   the free module `↑X →₀ A₁ᵐᵒᵖ` (counit of the free/forget adjunction, split by projectivity),
   likewise `Y`. Applying the bifunctor sends this pair of retracts to a retract of `X ⊗[k] Y`
   inside the free external tensor, and a retract of a projective object is projective
   (`CategoryTheory.Retract.projective`).
-/

open TensorProduct MulOpposite CategoryTheory

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

/-! ### Free case -/

/-- **Free case.** The external tensor of two free modules is projective (indeed free) over
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`. This is the base case for the retract argument in `extTensor_projective`.

TODO (see issue): the underlying statement is that
`(I₁ →₀ A₁ᵐᵒᵖ) ⊗[k] (I₂ →₀ A₂ᵐᵒᵖ)` is free over `(A₁ ⊗[k] A₂)ᵐᵒᵖ` with basis `I₁ × I₂`, via the
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`-linear equivalence to `(I₁ × I₂) →₀ (A₁ ⊗[k] A₂)ᵐᵒᵖ` built from
`Algebra.TensorProduct.opAlgEquiv`. The subtlety is that the `k`-module structure on the free
modules used by `extTensorFunctorObj` is restriction of scalars along `k → A₁ᵐᵒᵖ` (`Module.compHom`),
which is *not definitionally* the standard `Finsupp` `k`-module, so `finsuppTensorFinsupp` does not
apply on the nose; the equivalence must be built directly for the external action. -/
theorem extTensorFunctorObj_projective_of_free (I₁ I₂ : Type u) :
    Projective (extTensorFunctorObj k A₁ A₂
      ((ModuleCat.free A₁ᵐᵒᵖ).obj I₁)
      ((ModuleCat.free A₂ᵐᵒᵖ).obj I₂)) := by
  sorry

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

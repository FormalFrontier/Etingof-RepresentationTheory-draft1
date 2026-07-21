import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctorLeft
import EtingofRepresentationTheory.Chapter8.HomTensorFGProjective

/-!
# The bidegree component iso and naturality for the `Ext` Künneth rearrangement

Cohomological, contravariant twin of `Etingof.rearrangeBifunctorNatIso`
(`Chapter8/RearrangeBifunctorNatIso.lean`, the `Tor` template). On the `Tor` side the complex-level
`Etingof.rearrangeComplex` is assembled from a bifunctor natural iso whose two naturality squares
discharge the two differential-commutation squares of the complex iso. This file provides the
`Hom`-cochain analogue: a component isomorphism together with the two naturality lemmas
(contravariant in each argument), packaging
`Etingof.HomTensorFGProj.homTensorHomEquiv` (`Chapter8/HomTensorFGProjective.lean`).

For `k`-algebras `A₁, A₂`, left modules `N₁` (over `A₁`), `N₂` (over `A₂`) with an external
`A₁ ⊗[k] A₂`-action on `N₁ ⊗[k] N₂` pinned by `hN`, and finitely generated projective left
modules `X₁ : ModuleCat A₁`, `X₂ : ModuleCat A₂`, the `k`-linear isomorphism

    Hom_{A₁⊗A₂}(extTensorFunctorLeftObj X₁ X₂, N₁ ⊗ₖ N₂) ≅ Hom_{A₁}(X₁, N₁) ⊗ₖ Hom_{A₂}(X₂, N₂)

is `Etingof.rearrangeHomComponentIso` (the source carrier `↥(extTensorFunctorLeftObj X₁ X₂)` is
defeq to `X₁ ⊗[k] X₂` with its external `A₁ ⊗[k] A₂`-action). Its inverse is `homTensorHomEquiv`.

## Contents

* `towerExtL`: the `IsScalarTower k (A₁⊗A₂) (X ⊗[k] Y)` needed by `homTensorHomEquiv`, from the
  external representation being a `k`-algebra map (mirrors `extModule_isScalarTower`).
* `rearrangeHomComponentEquiv` / `rearrangeHomComponentIso`: the component `k`-linear equiv and its
  packaging as a `ModuleCat k` iso.
* `homTensorHom_comp_lcompₖ_left` / `homTensorHom_comp_lcompₖ_right`: the two naturality squares
  for the uncurried comparison map `homTensorHom` (which underlies the equiv): precomposition by
  `f : X₁' ⟶ X₁` (resp. `g : X₂' ⟶ X₂`) on the big `Hom` corresponds to precomposition on the first
  (resp. second) `Hom` factor of the target tensor. Stated as equalities of `k`-linear maps out of
  `Hom(X₁,N₁) ⊗ₖ Hom(X₂,N₂)`, so the cochain-complex assembler can read off the two
  differential-commutation squares directly. No finiteness is needed for these (they are properties
  of `homTensorHom`); the equiv is used only for the component data.

The precomposition on the big `Hom` is by the external functor map
`extTensorFunctorLeftMapHom (𝟙/f) (g/𝟙)`, exactly the degreewise map of the source cochain complex
`Hom_{A₁⊗A₂}(P•₁ ⊗ P•₂, N₁⊗N₂)`.
-/

open CategoryTheory TensorProduct
open Etingof.HomTensorFGProj

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
  [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

/-! ### Instances on the external tensor of two `ModuleCat` objects

The same restriction-of-scalars and external-action `local instance`s as
`ExternalTensorFunctorLeft`, re-activated here (they leak their names but not their instance-ness).
We add the missing
`k`-scalar tower on the external tensor, which `homTensorHomEquiv` requires. -/

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

/-- The external `A₁ ⊗[k] A₂`-action on `X ⊗[k] Y` is a `k`-scalar tower, because it is realised by
the `k`-algebra map `extTensorRepLeft`. Mirrors `HomTensorFGProj.extModule_isScalarTower`. -/
local instance towerExtL (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    IsScalarTower k (A₁ ⊗[k] A₂) (X ⊗[k] Y) := by
  refine ⟨fun c s z => ?_⟩
  change extTensorRepLeft k A₁ A₂ X Y (c • s) z = c • extTensorRepLeft k A₁ A₂ X Y s z
  rw [map_smul]
  rfl

/-! ### The component isomorphism -/

variable {A₁ A₂}

include hN in
/-- The component `k`-linear equivalence of the `Ext` Künneth rearrangement at `(X₁, X₂)`:
`Hom_{A₁⊗A₂}(X₁ ⊗ₖ X₂, N₁ ⊗ₖ N₂) ≃ₗ[k] Hom_{A₁}(X₁, N₁) ⊗ₖ Hom_{A₂}(X₂, N₂)` for finitely generated
projective `X₁, X₂`. The inverse of `homTensorHomEquiv`. -/
noncomputable def rearrangeHomComponentEquiv (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂] :
    ((X₁ ⊗[k] X₂ →ₗ[A₁ ⊗[k] A₂] N₁ ⊗[k] N₂)) ≃ₗ[k]
      ((X₁ →ₗ[A₁] N₁) ⊗[k] (X₂ →ₗ[A₂] N₂)) :=
  (homTensorHomEquiv k A₁ A₂ X₁ X₂ N₁ N₂
    (extTensorFunctorLeft_smul_tmul k A₁ A₂ X₁ X₂) hN).symm

include hN in
/-- The component of the `Ext` Künneth rearrangement at `(X₁, X₂)` as an iso in `ModuleCat k`:

    Hom_{A₁⊗A₂}(extTensorFunctorLeftObj X₁ X₂, N₁ ⊗ₖ N₂) ≅ Hom_{A₁}(X₁, N₁) ⊗ₖ Hom_{A₂}(X₂, N₂).

The source carrier `↥(extTensorFunctorLeftObj X₁ X₂) →ₗ[A₁⊗A₂] N₁⊗N₂` is defeq to
`X₁ ⊗[k] X₂ →ₗ[A₁⊗A₂] N₁⊗N₂`. Cohomological, contravariant twin of
`rearrangeBifunctorComponentIso`. -/
noncomputable def rearrangeHomComponentIso (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂] :
    ModuleCat.of k (↥(extTensorFunctorLeftObj k A₁ A₂ X₁ X₂) →ₗ[A₁ ⊗[k] A₂] N₁ ⊗[k] N₂)
      ≅ ModuleCat.of k ((X₁ →ₗ[A₁] N₁) ⊗[k] (X₂ →ₗ[A₂] N₂)) :=
  (rearrangeHomComponentEquiv k N₁ N₂ hN X₁ X₂).toModuleIso

/-! ### The two naturality squares

Precomposition by a factor morphism on the big `Hom` corresponds, under `homTensorHom`, to
precomposition on the matching `Hom` factor of the target tensor. Stated for the uncurried
comparison `homTensorHom` (no finiteness needed), as equalities of `k`-linear maps out of
`Hom(X₁,N₁) ⊗ₖ Hom(X₂,N₂)`. The precomposition on the big `Hom` is by
`extTensorFunctorLeftMapHom`, the degreewise map of the source cochain complex. -/

/-- **Naturality in the first variable.** For `f : X₁' ⟶ X₁` (`A₁`-linear), precomposition by
`f ⊗ 𝟙` on `Hom_{A₁⊗A₂}(X₁ ⊗ X₂, N₁⊗N₂)` equals, through `homTensorHom`, precomposition by `f` on
the first `Hom` factor. -/
theorem homTensorHom_comp_lcompₖ_left {X₁ X₁' : ModuleCat.{u} A₁} (f : X₁' ⟶ X₁)
    (X₂ : ModuleCat.{u} A₂) :
    (lcompₖ k (extTensorFunctorLeftMapHom k f (𝟙 X₂))).comp
        (homTensorHom k A₁ A₂ X₁ X₂ N₁ N₂
          (extTensorFunctorLeft_smul_tmul k A₁ A₂ X₁ X₂) hN)
      = (homTensorHom k A₁ A₂ X₁' X₂ N₁ N₂
          (extTensorFunctorLeft_smul_tmul k A₁ A₂ X₁' X₂) hN).comp
          (TensorProduct.map (lcompₖ k f.hom) LinearMap.id) := by
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  refine hom_ext k A₁ A₂ X₁' X₂ N₁ N₂ fun x₁ x₂ => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, lcompₖ_apply,
    homTensorHom_tmul_tmul, extTensorFunctorLeftMapHom_tmul, ModuleCat.hom_id, LinearMap.id_coe]

/-- **Naturality in the second variable.** For `g : X₂' ⟶ X₂` (`A₂`-linear), precomposition by
`𝟙 ⊗ g` on `Hom_{A₁⊗A₂}(X₁ ⊗ X₂, N₁⊗N₂)` equals, through `homTensorHom`, precomposition by `g` on
the second `Hom` factor. -/
theorem homTensorHom_comp_lcompₖ_right (X₁ : ModuleCat.{u} A₁) {X₂ X₂' : ModuleCat.{u} A₂}
    (g : X₂' ⟶ X₂) :
    (lcompₖ k (extTensorFunctorLeftMapHom k (𝟙 X₁) g)).comp
        (homTensorHom k A₁ A₂ X₁ X₂ N₁ N₂
          (extTensorFunctorLeft_smul_tmul k A₁ A₂ X₁ X₂) hN)
      = (homTensorHom k A₁ A₂ X₁ X₂' N₁ N₂
          (extTensorFunctorLeft_smul_tmul k A₁ A₂ X₁ X₂') hN).comp
          (TensorProduct.map LinearMap.id (lcompₖ k g.hom)) := by
  refine TensorProduct.ext' fun φ₁ φ₂ => ?_
  refine hom_ext k A₁ A₂ X₁ X₂' N₁ N₂ fun x₁ x₂ => ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, lcompₖ_apply,
    homTensorHom_tmul_tmul, extTensorFunctorLeftMapHom_tmul, ModuleCat.hom_id, LinearMap.id_coe]

end Etingof

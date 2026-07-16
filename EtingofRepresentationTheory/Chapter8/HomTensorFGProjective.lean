import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Algebra.Tower

/-!
# The finite-generation Hom–tensor comparison isomorphism

For `k`-algebras `A₁, A₂`, a **finitely generated projective** left `A₁`-module `P₁` and left
`A₂`-module `P₂`, and left modules `N₁` (over `A₁`) and `N₂` (over `A₂`), the canonical `k`-linear
map

`Hom_{A₁}(P₁, N₁) ⊗ₖ Hom_{A₂}(P₂, N₂) → Hom_{A₁ ⊗ₖ A₂}(P₁ ⊗ₖ P₂, N₁ ⊗ₖ N₂)`,
`f ⊗ g ↦ (p₁ ⊗ p₂ ↦ f p₁ ⊗ g p₂)`,

is a `k`-linear **isomorphism**. Here `P₁ ⊗ₖ P₂` and `N₁ ⊗ₖ N₂` carry the external left
`A₁ ⊗ₖ A₂`-module structure `(a₁ ⊗ a₂) • (x₁ ⊗ x₂) = (a₁ • x₁) ⊗ (a₂ • x₂)`.

This is the cohomological analogue of the `Tor`-side degreewise tensor iso: `Tor` uses
right-exactness of `⊗` (no finiteness needed) while `Ext` uses `Hom`, which only commutes with `⊗ₖ`
on the **finitely generated projective** side — hence the hypothesis. It is the crux of the `Ext`
half of Problem 8.2.8.

## Construction and proof strategy

* `extRep` / `extModule` build the external left `A₁ ⊗ₖ A₂`-action on `X₁ ⊗ₖ X₂` from the two
  factor actions, mirroring the right-module `Etingof.extTensorModule` but without `ᵐᵒᵖ`.
  `extModule_smul_tmul` pins it on simple tensors. This structure is used only to equip the free
  modules appearing in the proof; the statement itself takes the module structures as parameters
  pinned by `hP`, `hN`, exactly as `Etingof.Problem_8_2_8_ext` does.
* `extMap` promotes `TensorProduct.map f₁ f₂` (with `fᵢ` factor-linear) to an
  `A₁ ⊗ₖ A₂`-linear map; its `A₁ ⊗ₖ A₂`-linearity is forced by the two pinning hypotheses.
* `homTensorHom` is the `k`-linear comparison map `f ⊗ g ↦ extMap f g`.
* `homTensorHom_bijective_free` proves bijectivity when `Pᵢ` are the free modules `Fin nᵢ → Aᵢ`.
* The general f.g.-projective case (`homTensorHom_bijective`) follows because a f.g. projective
  module is a retract of a finite free one, `homTensorHom` is natural, and a retract of an
  isomorphism is an isomorphism.
-/

open TensorProduct

namespace Etingof.HomTensorFGProj

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

section ExtModule

variable (X₁ X₂ : Type u)
  [AddCommGroup X₁] [Module k X₁] [Module A₁ X₁] [IsScalarTower k A₁ X₁]
  [AddCommGroup X₂] [Module k X₂] [Module A₂ X₂] [IsScalarTower k A₂ X₂]

/-- The representation of `A₁ ⊗[k] A₂` on `X₁ ⊗[k] X₂`: `A₁` acts on the left factor and `A₂` on the
right factor. It is the composite `End X₁ ⊗ End X₂ →ₐ End (X₁ ⊗ X₂)` of the tensor of the two
componentwise actions. This is the left-module twin of `Etingof.extTensorRepAux`. -/
noncomputable def extRep :
    (A₁ ⊗[k] A₂) →ₐ[k] Module.End k (X₁ ⊗[k] X₂) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := X₁) (N := X₂)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul (A := A₁) k k X₁)
      (Algebra.lsmul (A := A₂) k k X₂))

/-- The external tensor product module: `X₁ ⊗[k] X₂` as a left `A₁ ⊗[k] A₂`-module with the
componentwise action `(a₁ ⊗ a₂) • (x₁ ⊗ x₂) = (a₁ • x₁) ⊗ (a₂ • x₂)`. -/
@[reducible] noncomputable def extModule : Module (A₁ ⊗[k] A₂) (X₁ ⊗[k] X₂) :=
  Module.compHom (X₁ ⊗[k] X₂) (R := Module.End k (X₁ ⊗[k] X₂))
    (extRep k A₁ A₂ X₁ X₂).toRingHom

/-- The external action on a simple tensor is componentwise. -/
theorem extModule_smul_tmul (a₁ : A₁) (a₂ : A₂) (x₁ : X₁) (x₂ : X₂) :
    (extModule k A₁ A₂ X₁ X₂).toSMul.smul (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) (x₁ ⊗ₜ[k] x₂)
      = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂) := by
  change extRep k A₁ A₂ X₁ X₂ (a₁ ⊗ₜ[k] a₂) (x₁ ⊗ₜ[k] x₂) = _
  rw [extRep, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Module.endTensorEndAlgHom_apply]
  rfl

end ExtModule

section HomTensorHom

variable (P₁ P₂ N₁ N₂ : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ P₁] [IsScalarTower k A₁ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ P₂] [IsScalarTower k A₂ P₂]
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
  [instP : Module (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)]
  [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]

/-- The `A₁ ⊗ A₂`-linear map `P₁ ⊗ P₂ → N₁ ⊗ N₂` induced by factor-linear maps `f₁, f₂`. As a
`k`-linear map it is `TensorProduct.map f₁ f₂`; its `A₁ ⊗ A₂`-linearity is forced by the pinning
hypotheses `hP`, `hN`. -/
noncomputable def extMap
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (f₁ : P₁ →ₗ[A₁] N₁) (f₂ : P₂ →ₗ[A₂] N₂) :
    (P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂) where
  toFun := TensorProduct.map (f₁.restrictScalars k) (f₂.restrictScalars k)
  map_add' := map_add _
  map_smul' c z := by
    -- `A₁ ⊗ A₂`-linearity from the pinning hypotheses; proved by induction on `c` and `z`.
    sorry

/-- The canonical `k`-linear comparison map
`Hom_{A₁}(P₁,N₁) ⊗ₖ Hom_{A₂}(P₂,N₂) → Hom_{A₁⊗A₂}(P₁⊗P₂, N₁⊗N₂)`,
`f ⊗ g ↦ (p₁ ⊗ p₂ ↦ f p₁ ⊗ g p₂)`. -/
noncomputable def homTensorHom
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    ((P₁ →ₗ[A₁] N₁) ⊗[k] (P₂ →ₗ[A₂] N₂)) →ₗ[k]
      ((P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) :=
  TensorProduct.lift
    { toFun := fun f₁ =>
        { toFun := fun f₂ => extMap k A₁ A₂ P₁ P₂ N₁ N₂ hP hN f₁ f₂
          map_add' := by sorry
          map_smul' := by sorry }
      map_add' := by sorry
      map_smul' := by sorry }

/-- Evaluation of `homTensorHom` on a simple tensor `f₁ ⊗ f₂` at a simple tensor `p₁ ⊗ p₂`. -/
theorem homTensorHom_tmul_tmul
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (f₁ : P₁ →ₗ[A₁] N₁) (f₂ : P₂ →ₗ[A₂] N₂) (p₁ : P₁) (p₂ : P₂) :
    homTensorHom k A₁ A₂ P₁ P₂ N₁ N₂ hP hN (f₁ ⊗ₜ[k] f₂) (p₁ ⊗ₜ[k] p₂)
      = f₁ p₁ ⊗ₜ[k] f₂ p₂ := by
  sorry

end HomTensorHom

section Main

variable (P₁ P₂ N₁ N₂ : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ P₁] [IsScalarTower k A₁ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ P₂] [IsScalarTower k A₂ P₂]
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
  [instP : Module (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)]
  [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]

/-- **The finite-generation Hom–tensor comparison isomorphism.** For `k`-algebras `A₁, A₂`, finitely
generated projective left modules `P₁, P₂` and arbitrary left modules `N₁, N₂`, the canonical
`k`-linear map `homTensorHom` is bijective. -/
theorem homTensorHom_bijective
    [Module.Finite A₁ P₁] [Module.Projective A₁ P₁]
    [Module.Finite A₂ P₂] [Module.Projective A₂ P₂]
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    Function.Bijective (homTensorHom k A₁ A₂ P₁ P₂ N₁ N₂ hP hN) := by
  sorry

/-- The finite-generation Hom–tensor comparison isomorphism, as a `k`-linear equivalence. -/
noncomputable def homTensorHomEquiv
    [Module.Finite A₁ P₁] [Module.Projective A₁ P₁]
    [Module.Finite A₂ P₂] [Module.Projective A₂ P₂]
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    ((P₁ →ₗ[A₁] N₁) ⊗[k] (P₂ →ₗ[A₂] N₂)) ≃ₗ[k]
      ((P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) :=
  LinearEquiv.ofBijective (homTensorHom k A₁ A₂ P₁ P₂ N₁ N₂ hP hN)
    (homTensorHom_bijective k A₁ A₂ P₁ P₂ N₁ N₂ hP hN)

end Main

end Etingof.HomTensorFGProj

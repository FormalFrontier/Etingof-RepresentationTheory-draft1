import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Algebra.Tower

/-!
# The finite-generation Hom–tensor comparison isomorphism

For `k`-algebras `A₁, A₂`, a finitely generated projective left `A₁`-module `P₁` and left
`A₂`-module `P₂`, and left modules `N₁` (over `A₁`) and `N₂` (over `A₂`), the canonical `k`-linear
map

`Hom_{A₁}(P₁, N₁) ⊗ₖ Hom_{A₂}(P₂, N₂) → Hom_{A₁ ⊗ₖ A₂}(P₁ ⊗ₖ P₂, N₁ ⊗ₖ N₂)`,
`f ⊗ g ↦ (p₁ ⊗ p₂ ↦ f p₁ ⊗ g p₂)`,

is a `k`-linear isomorphism. Here `P₁ ⊗ₖ P₂` and `N₁ ⊗ₖ N₂` carry the external left
`A₁ ⊗ₖ A₂`-module structure `(a₁ ⊗ a₂) • (x₁ ⊗ x₂) = (a₁ • x₁) ⊗ (a₂ • x₂)`.

This is the cohomological analogue of the `Tor`-side degreewise tensor iso: `Tor` uses
right-exactness of `⊗` (no finiteness needed) while `Ext` uses `Hom`, which only commutes with `⊗ₖ`
on the finitely generated projective side, hence the hypothesis. It is the key step of the `Ext`
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

/-- The canonical external module structure is a `k`-scalar tower: `k` acts through the algebra map
`k → A₁ ⊗ A₂` compatibly. -/
theorem extModule_isScalarTower :
    @IsScalarTower k (A₁ ⊗[k] A₂) (X₁ ⊗[k] X₂) _ (extModule k A₁ A₂ X₁ X₂).toSMul _ := by
  letI := extModule k A₁ A₂ X₁ X₂
  refine ⟨fun c s z => ?_⟩
  change extRep k A₁ A₂ X₁ X₂ (c • s) z = c • extRep k A₁ A₂ X₁ X₂ s z
  rw [map_smul]
  rfl

end ExtModule

section Lcomp

variable {R : Type u} [Ring R] [Algebra k R] {L M M' : Type u}
  [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [AddCommGroup M'] [Module k M'] [Module R M'] [IsScalarTower k R M']

/-- Precomposition `φ ↦ φ ∘ₗ s` by a fixed `R`-linear map `s`, as a `k`-linear operator on the
`k`-modules of `R`-linear maps. -/
def lcompₖ (s : M →ₗ[R] M') : (M' →ₗ[R] L) →ₗ[k] (M →ₗ[R] L) where
  toFun φ := φ ∘ₗ s
  map_add' a b := by ext x; simp
  map_smul' c a := by ext x; simp

@[simp] theorem lcompₖ_apply (s : M →ₗ[R] M') (φ : M' →ₗ[R] L) :
    lcompₖ k s φ = φ ∘ₗ s := rfl

end Lcomp

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
    simp only [RingHom.id_apply]
    induction c using TensorProduct.induction_on generalizing z with
    | zero => simp
    | add c d hc hd => rw [add_smul, map_add, hc, hd, add_smul]
    | tmul a₁ a₂ =>
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
        | tmul p₁ p₂ =>
            rw [hP, TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
              LinearMap.restrictScalars_apply, LinearMap.map_smul, LinearMap.map_smul,
              TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
              LinearMap.restrictScalars_apply, hN]

variable (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))

@[simp] theorem extMap_tmul (f₁ : P₁ →ₗ[A₁] N₁) (f₂ : P₂ →ₗ[A₂] N₂) (p₁ : P₁) (p₂ : P₂) :
    extMap k A₁ A₂ P₁ P₂ N₁ N₂ hP hN f₁ f₂ (p₁ ⊗ₜ[k] p₂) = f₁ p₁ ⊗ₜ[k] f₂ p₂ :=
  rfl

/-- Two `A₁ ⊗ A₂`-linear maps out of `P₁ ⊗[k] P₂` agreeing on simple tensors are equal. -/
theorem hom_ext {g h : (P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)}
    (H : ∀ (p₁ : P₁) (p₂ : P₂), g (p₁ ⊗ₜ[k] p₂) = h (p₁ ⊗ₜ[k] p₂)) : g = h := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p₁ p₂ => exact H p₁ p₂
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The canonical `k`-linear comparison map
`Hom_{A₁}(P₁,N₁) ⊗ₖ Hom_{A₂}(P₂,N₂) → Hom_{A₁⊗A₂}(P₁⊗P₂, N₁⊗N₂)`,
`f ⊗ g ↦ (p₁ ⊗ p₂ ↦ f p₁ ⊗ g p₂)`. -/
noncomputable def homTensorHom :
    ((P₁ →ₗ[A₁] N₁) ⊗[k] (P₂ →ₗ[A₂] N₂)) →ₗ[k]
      ((P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) :=
  TensorProduct.lift
    { toFun := fun f₁ =>
        { toFun := fun f₂ => extMap k A₁ A₂ P₁ P₂ N₁ N₂ hP hN f₁ f₂
          map_add' := fun f₂ f₂' => hom_ext k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by
            simp [TensorProduct.tmul_add]
          map_smul' := fun c f₂ => hom_ext k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by
            simp [TensorProduct.tmul_smul] }
      map_add' := fun f₁ f₁' => LinearMap.ext fun f₂ =>
        hom_ext k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by simp [TensorProduct.add_tmul]
      map_smul' := fun c f₁ => LinearMap.ext fun f₂ =>
        hom_ext k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, extMap_tmul,
            TensorProduct.smul_tmul', RingHom.id_apply] }

/-- Evaluation of `homTensorHom` on a simple tensor `f₁ ⊗ f₂` at a simple tensor `p₁ ⊗ p₂`. -/
@[simp] theorem homTensorHom_tmul_tmul
    (f₁ : P₁ →ₗ[A₁] N₁) (f₂ : P₂ →ₗ[A₂] N₂) (p₁ : P₁) (p₂ : P₂) :
    homTensorHom k A₁ A₂ P₁ P₂ N₁ N₂ hP hN (f₁ ⊗ₜ[k] f₂) (p₁ ⊗ₜ[k] p₂)
      = f₁ p₁ ⊗ₜ[k] f₂ p₂ := by
  rw [homTensorHom, TensorProduct.lift.tmul]
  rfl

end HomTensorHom

section FreeCaseAux

/-- Uncurrying `Fin n → Fin m → X` to `Fin n × Fin m → X` as a `k`-linear equivalence. -/
def piProdEquiv (X : Type u) [AddCommGroup X] [Module k X] (n m : ℕ) :
    (Fin n → Fin m → X) ≃ₗ[k] (Fin n × Fin m → X) where
  toFun f := fun p => f p.1 p.2
  invFun g := fun i j => g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv g := by funext p; obtain ⟨i, j⟩ := p; rfl

@[simp] theorem piProdEquiv_apply (X : Type u) [AddCommGroup X] [Module k X] (n m : ℕ)
    (f : Fin n → Fin m → X) (i : Fin n) (j : Fin m) :
    piProdEquiv k X n m f (i, j) = f i j := rfl

/-- The tensor product of two finite free `k`-modules, distributed over the finite index sets:
`(Fin n → M₁) ⊗[k] (Fin m → M₂) ≃ₗ[k] (Fin n × Fin m → M₁ ⊗[k] M₂)`. -/
noncomputable def finTensorPiEquiv (M₁ M₂ : Type u)
    [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] (n m : ℕ) :
    ((Fin n → M₁) ⊗[k] (Fin m → M₂)) ≃ₗ[k] (Fin n × Fin m → M₁ ⊗[k] M₂) :=
  (TensorProduct.piLeft k (Fin m → M₂) (fun _ : Fin n => M₁)) ≪≫ₗ
    (LinearEquiv.piCongrRight fun _ : Fin n =>
      TensorProduct.piRight k k M₁ (fun _ : Fin m => M₂)) ≪≫ₗ
    piProdEquiv k (M₁ ⊗[k] M₂) n m

@[simp] theorem finTensorPiEquiv_tmul (M₁ M₂ : Type u)
    [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] (n m : ℕ)
    (x₁ : Fin n → M₁) (x₂ : Fin m → M₂) (i : Fin n) (j : Fin m) :
    finTensorPiEquiv k M₁ M₂ n m (x₁ ⊗ₜ[k] x₂) (i, j) = x₁ i ⊗ₜ[k] x₂ j := by
  simp [finTensorPiEquiv]

section Precomp

variable {R : Type u} [Ring R] [Algebra k R] {X Y L : Type u}
  [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]
  [AddCommGroup Y] [Module k Y] [Module R Y] [IsScalarTower k R Y]
  [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]

/-- Precomposition by an `R`-linear equivalence `e : X ≃ₗ[R] Y`, packaged as the `k`-linear
equivalence of Hom-spaces `(X →ₗ[R] L) ≃ₗ[k] (Y →ₗ[R] L)`, `φ ↦ φ ∘ₗ e.symm`. -/
def precompEquiv (e : X ≃ₗ[R] Y) : (X →ₗ[R] L) ≃ₗ[k] (Y →ₗ[R] L) where
  toFun φ := φ ∘ₗ (e.symm : Y →ₗ[R] X)
  invFun ψ := ψ ∘ₗ (e : X →ₗ[R] Y)
  map_add' a b := by ext y; simp
  map_smul' c a := by ext y; simp
  left_inv φ := by ext x; simp
  right_inv ψ := by ext y; simp

@[simp] theorem precompEquiv_apply (e : X ≃ₗ[R] Y) (φ : X →ₗ[R] L) (y : Y) :
    precompEquiv k e φ y = φ (e.symm y) := rfl

end Precomp

end FreeCaseAux

section Main

variable (P₁ P₂ N₁ N₂ : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ P₁] [IsScalarTower k A₁ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ P₂] [IsScalarTower k A₂ P₂]
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
  [instP : Module (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)]
  [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]

/-- **Base case.** The comparison map is bijective when the source modules are the finite free
modules `Fin n → A₁` and `Fin m → A₂`. Here `Hom_{Aᵢ}(Aᵢ^{nᵢ}, Nᵢ) ≅ Nᵢ^{nᵢ}` and
`(A₁^{n} ⊗ A₂^{m})` is `A₁ ⊗ A₂`-free on `Fin n × Fin m`, so the map is a matching of finite
products of `N₁ ⊗ N₂`. -/
theorem homTensorHom_bijective_free (n m : ℕ)
    [instF : Module (A₁ ⊗[k] A₂) ((Fin n → A₁) ⊗[k] (Fin m → A₂))]
    [IsScalarTower k (A₁ ⊗[k] A₂) ((Fin n → A₁) ⊗[k] (Fin m → A₂))]
    (hF : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : Fin n → A₁) (x₂ : Fin m → A₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : (Fin n → A₁) ⊗[k] (Fin m → A₂))
        = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    Function.Bijective
      (homTensorHom k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ hF hN) := by
  classical
  set F := homTensorHom k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ hF hN with hFdef
  -- Step 1: the external free-basis equivalence
  -- `B : (A₁^n) ⊗ₖ (A₂^m) ≃ₗ[A₁⊗A₂] (A₁⊗A₂)^{n×m}`. Its underlying function is the purely
  -- `k`-linear `finTensorPiEquiv`; the pinning `hF` upgrades it to `A₁ ⊗ A₂`-linearity.
  let Bfwd : ((Fin n → A₁) ⊗[k] (Fin m → A₂)) →ₗ[A₁ ⊗[k] A₂]
      (Fin n × Fin m → A₁ ⊗[k] A₂) :=
    { toFun := finTensorPiEquiv k A₁ A₂ n m
      map_add' := (finTensorPiEquiv k A₁ A₂ n m).map_add
      map_smul' := by
        intro c z
        simp only [RingHom.id_apply]
        induction c using TensorProduct.induction_on generalizing z with
        | zero => simp
        | add c d hc hd => rw [add_smul, map_add, hc, hd, add_smul]
        | tmul a₁ a₂ =>
            induction z using TensorProduct.induction_on with
            | zero => simp
            | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
            | tmul x₁ x₂ =>
                rw [hF]
                funext p; obtain ⟨i, j⟩ := p
                simp only [finTensorPiEquiv_tmul, Pi.smul_apply, smul_eq_mul,
                  Algebra.TensorProduct.tmul_mul_tmul] }
  have hBfwd_bij : Function.Bijective Bfwd := (finTensorPiEquiv k A₁ A₂ n m).bijective
  let B : ((Fin n → A₁) ⊗[k] (Fin m → A₂)) ≃ₗ[A₁ ⊗[k] A₂]
      (Fin n × Fin m → A₁ ⊗[k] A₂) := LinearEquiv.ofBijective Bfwd hBfwd_bij
  have hB_tmul : ∀ (x₁ : Fin n → A₁) (x₂ : Fin m → A₂) (i : Fin n) (j : Fin m),
      B (x₁ ⊗ₜ[k] x₂) (i, j) = x₁ i ⊗ₜ[k] x₂ j :=
    fun x₁ x₂ i j => finTensorPiEquiv_tmul k A₁ A₂ n m x₁ x₂ i j
  have hB_single : ∀ (i : Fin n) (j : Fin m),
      B.symm (Pi.single (i, j) 1)
        = (Pi.single i 1 : Fin n → A₁) ⊗ₜ[k] (Pi.single j 1 : Fin m → A₂) := by
    intro i j
    rw [LinearEquiv.symm_apply_eq]
    funext p; obtain ⟨i', j'⟩ := p
    rw [hB_tmul]
    simp only [Pi.single_apply, Prod.mk.injEq]
    by_cases hi : i' = i <;> by_cases hj : j' = j <;>
      simp [hi, hj, Algebra.TensorProduct.one_def]
  -- Step 2: coordinate equivalences on source, target and the middle matrix space.
  let c₁ : ((Fin n → A₁) →ₗ[A₁] N₁) ≃ₗ[k] (Fin n → N₁) :=
    ((Pi.basisFun A₁ (Fin n)).constr k).symm
  let c₂ : ((Fin m → A₂) →ₗ[A₂] N₂) ≃ₗ[k] (Fin m → N₂) :=
    ((Pi.basisFun A₂ (Fin m)).constr k).symm
  let srcE := TensorProduct.congr c₁ c₂
  let midE := finTensorPiEquiv k N₁ N₂ n m
  let cT : ((Fin n × Fin m → A₁ ⊗[k] A₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) ≃ₗ[k]
      (Fin n × Fin m → N₁ ⊗[k] N₂) :=
    ((Pi.basisFun (A₁ ⊗[k] A₂) (Fin n × Fin m)).constr k).symm
  let tgtE := (precompEquiv k B).trans cT
  let E : (((Fin n → A₁) →ₗ[A₁] N₁) ⊗[k] ((Fin m → A₂) →ₗ[A₂] N₂)) ≃ₗ[k]
      ((Fin n → A₁) ⊗[k] (Fin m → A₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) :=
    srcE.trans (midE.trans tgtE.symm)
  -- Step 3: `F` agrees with the equivalence `E`, hence is bijective.
  have key : ∀ z, F z = E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul f₁ f₂ =>
        have hEval : E (f₁ ⊗ₜ[k] f₂) = tgtE.symm (midE (srcE (f₁ ⊗ₜ[k] f₂))) := rfl
        have hgen : tgtE (F (f₁ ⊗ₜ[k] f₂)) = midE (srcE (f₁ ⊗ₜ[k] f₂)) := by
          funext p; obtain ⟨i, j⟩ := p
          have hlhs : tgtE (F (f₁ ⊗ₜ[k] f₂)) (i, j)
              = F (f₁ ⊗ₜ[k] f₂) (B.symm (Pi.single (i, j) 1)) := by
            change ((Pi.basisFun (A₁ ⊗[k] A₂) (Fin n × Fin m)).constr k).symm
                (precompEquiv k B (F (f₁ ⊗ₜ[k] f₂))) (i, j) = _
            rw [Module.Basis.constr_symm_apply, precompEquiv_apply, Pi.basisFun_apply]
          have hrhs : midE (srcE (f₁ ⊗ₜ[k] f₂)) (i, j)
              = f₁ (Pi.single i 1) ⊗ₜ[k] f₂ (Pi.single j 1) := by
            change finTensorPiEquiv k N₁ N₂ n m
                (TensorProduct.congr c₁ c₂ (f₁ ⊗ₜ[k] f₂)) (i, j) = _
            rw [TensorProduct.congr_tmul, finTensorPiEquiv_tmul]
            change (((Pi.basisFun A₁ (Fin n)).constr k).symm f₁) i ⊗ₜ[k]
                (((Pi.basisFun A₂ (Fin m)).constr k).symm f₂) j = _
            rw [Module.Basis.constr_symm_apply, Module.Basis.constr_symm_apply,
              Pi.basisFun_apply, Pi.basisFun_apply]
          rw [hlhs, hB_single, hFdef, homTensorHom_tmul_tmul, hrhs]
        rw [hEval, ← hgen, tgtE.symm_apply_apply]
  have hFE : ⇑F = ⇑E := funext key
  rw [hFE]
  exact E.bijective

/-- **The finite-generation Hom–tensor comparison isomorphism.** For `k`-algebras `A₁, A₂`, finitely
generated projective left modules `P₁, P₂` and arbitrary left modules `N₁, N₂`, the canonical
`k`-linear map `homTensorHom` is bijective.

The projective case is reduced to `homTensorHom_bijective_free`: a f.g. projective module is a
retract of a finite free one, `homTensorHom` is natural in the source, and a retract of an
isomorphism is an isomorphism. -/
theorem homTensorHom_bijective
    [Module.Finite A₁ P₁] [Module.Projective A₁ P₁]
    [Module.Finite A₂ P₂] [Module.Projective A₂ P₂]
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    Function.Bijective (homTensorHom k A₁ A₂ P₁ P₂ N₁ N₂ hP hN) := by
  obtain ⟨n, r₁, s₁, _, _, hrs₁⟩ := Module.Finite.exists_comp_eq_id_of_projective A₁ P₁
  obtain ⟨m, r₂, s₂, _, _, hrs₂⟩ := Module.Finite.exists_comp_eq_id_of_projective A₂ P₂
  -- `rᵢ : (Fin nᵢ → Aᵢ) →ₗ[Aᵢ] Pᵢ` is the retraction, `sᵢ : Pᵢ →ₗ[Aᵢ] (Fin nᵢ → Aᵢ)` the section,
  -- and `rᵢ ∘ₗ sᵢ = id`.
  letI iF := extModule k A₁ A₂ (Fin n → A₁) (Fin m → A₂)
  haveI := extModule_isScalarTower k A₁ A₂ (Fin n → A₁) (Fin m → A₂)
  have hF := extModule_smul_tmul k A₁ A₂ (Fin n → A₁) (Fin m → A₂)
  have hfree := homTensorHom_bijective_free k A₁ A₂ N₁ N₂ n m hF hN
  set Hfree := homTensorHom k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ hF hN with hHfree
  set HP := homTensorHom k A₁ A₂ P₁ P₂ N₁ N₂ hP hN with hHP
  set E := LinearEquiv.ofBijective Hfree hfree with hE
  -- External `A₁ ⊗ A₂`-linear maps `Fin n → A₁) ⊗ (Fin m → A₂) ↔ P₁ ⊗ P₂`.
  set t_r := extMap k A₁ A₂ (Fin n → A₁) (Fin m → A₂) P₁ P₂ hF hP r₁ r₂ with ht_r
  set t_s := extMap k A₁ A₂ P₁ P₂ (Fin n → A₁) (Fin m → A₂) hP hF s₁ s₂ with ht_s
  -- The `k`-linear retract maps on the `Hom ⊗ Hom` side.
  set S := TensorProduct.map (lcompₖ (L := N₁) k s₁) (lcompₖ (L := N₂) k s₂) with hS
  set R := TensorProduct.map (lcompₖ (L := N₁) k r₁) (lcompₖ (L := N₂) k r₂) with hR
  -- Naturality of `homTensorHom` in the source.
  have NAT1 : ∀ x, (HP x) ∘ₗ t_r = Hfree (R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, LinearMap.add_comp, ha, hb, map_add, map_add]
    | tmul f g =>
        refine hom_ext k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ fun x₁ x₂ => ?_
        simp only [hHP, hHfree, ht_r, hR, LinearMap.comp_apply, TensorProduct.map_tmul,
          lcompₖ_apply, extMap_tmul, homTensorHom_tmul_tmul]
  have NAT2 : ∀ y, HP (S y) = (Hfree y) ∘ₗ t_s := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, LinearMap.add_comp]
    | tmul f g =>
        refine hom_ext k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => ?_
        simp only [hHP, hHfree, ht_s, hS, LinearMap.comp_apply, TensorProduct.map_tmul,
          lcompₖ_apply, extMap_tmul, homTensorHom_tmul_tmul]
  -- `S ∘ R = id` on the `Hom ⊗ Hom` side.
  have RETR : ∀ x, S (R x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul f g =>
        simp only [hS, hR, TensorProduct.map_tmul, lcompₖ_apply, LinearMap.comp_assoc, hrs₁,
          hrs₂, LinearMap.comp_id]
  -- `t_r ∘ₗ t_s = id` on `P₁ ⊗ P₂`.
  have RETR' : t_r ∘ₗ t_s = LinearMap.id := by
    refine hom_ext k A₁ A₂ P₁ P₂ P₁ P₂ fun p₁ p₂ => ?_
    have e1 : r₁ (s₁ p₁) = p₁ := by rw [← LinearMap.comp_apply, hrs₁, LinearMap.id_apply]
    have e2 : r₂ (s₂ p₂) = p₂ := by rw [← LinearMap.comp_apply, hrs₂, LinearMap.id_apply]
    simp only [ht_r, ht_s, LinearMap.comp_apply, extMap_tmul, LinearMap.id_coe, id_eq, e1, e2]
  -- Construct the two-sided inverse.
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun Φ => S (E.symm (lcompₖ k t_r Φ)), fun x => ?_, fun Φ => ?_⟩
  · -- left inverse
    change S (E.symm (lcompₖ k t_r (HP x))) = x
    rw [lcompₖ_apply, NAT1 x, show Hfree (R x) = E (R x) from rfl,
      LinearEquiv.symm_apply_apply, RETR]
  · -- right inverse
    change HP (S (E.symm (lcompₖ k t_r Φ))) = Φ
    rw [NAT2 (E.symm (lcompₖ k t_r Φ)),
      show Hfree (E.symm (lcompₖ k t_r Φ)) = E (E.symm (lcompₖ k t_r Φ)) from rfl,
      LinearEquiv.apply_symm_apply, lcompₖ_apply, LinearMap.comp_assoc, RETR', LinearMap.comp_id]

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

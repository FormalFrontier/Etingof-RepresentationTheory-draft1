/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Algebra.Tower

/-!
# Linear maps on tensor products

This module constructs module structures on tensor products, maps induced by pairs of linear maps,
and comparison equivalences for finite projective modules.
-/

open TensorProduct

namespace RepresentationTheory.TensorProduct.LinearMap

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

section ExtModule

variable (X₁ X₂ : Type u)
  [AddCommGroup X₁] [Module k X₁] [Module A₁ X₁] [IsScalarTower k A₁ X₁]
  [AddCommGroup X₂] [Module k X₂] [Module A₂ X₂] [IsScalarTower k A₂ X₂]


/-- The tensor product algebra acts on the tensor product module through an algebra homomorphism into its base-linear endomorphisms. -/
noncomputable def TensorProduct.algebraHomEnd :
    (A₁ ⊗[k] A₂) →ₐ[k] Module.End k (X₁ ⊗[k] X₂) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := X₁) (N := X₂)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul (A := A₁) k k X₁)
      (Algebra.lsmul (A := A₂) k k X₂))


/-- Equips a tensor product of modules with a module structure over the tensor product of their scalar algebras. -/
@[reducible] noncomputable def TensorProduct.moduleOverTensorProduct : Module (A₁ ⊗[k] A₂) (X₁ ⊗[k] X₂) :=
  Module.compHom (X₁ ⊗[k] X₂) (R := Module.End k (X₁ ⊗[k] X₂))
    (TensorProduct.algebraHomEnd k A₁ A₂ X₁ X₂).toRingHom


/-- Multiplying a pure tensor by a pure tensor of scalars acts componentwise under the induced module structure. -/
theorem TensorProduct.smul_tmul_moduleOverTensorProduct (a₁ : A₁) (a₂ : A₂) (x₁ : X₁) (x₂ : X₂) :
    (TensorProduct.moduleOverTensorProduct k A₁ A₂ X₁ X₂).toSMul.smul (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) (x₁ ⊗ₜ[k] x₂)
      = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂) := by
  change TensorProduct.algebraHomEnd k A₁ A₂ X₁ X₂ (a₁ ⊗ₜ[k] a₂) (x₁ ⊗ₜ[k] x₂) = _
  rw [TensorProduct.algebraHomEnd, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Module.endTensorEndAlgHom_apply]
  rfl


/-- The base ring, tensor product algebra, and tensor product module form a scalar tower for the induced module structure. -/
theorem TensorProduct.isScalarTower_moduleOverTensorProduct :
    @IsScalarTower k (A₁ ⊗[k] A₂) (X₁ ⊗[k] X₂) _ (TensorProduct.moduleOverTensorProduct k A₁ A₂ X₁ X₂).toSMul _ := by
  letI := TensorProduct.moduleOverTensorProduct k A₁ A₂ X₁ X₂
  refine ⟨fun c s z => ?_⟩
  change TensorProduct.algebraHomEnd k A₁ A₂ X₁ X₂ (c • s) z = c • TensorProduct.algebraHomEnd k A₁ A₂ X₁ X₂ s z
  rw [map_smul]
  rfl

end ExtModule

section Lcomp

variable {R : Type u} [Ring R] [Algebra k R] {L M M' : Type u}
  [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]
  [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [AddCommGroup M'] [Module k M'] [Module R M'] [IsScalarTower k R M']


/-- Precomposition by a linear map defines a base-linear map between the corresponding spaces of linear maps. -/
def LinearMap.precompLinear (s : M →ₗ[R] M') : (M' →ₗ[R] L) →ₗ[k] (M →ₗ[R] L) where
  toFun φ := φ ∘ₗ s
  map_add' a b := by ext x; simp
  map_smul' c a := by ext x; simp

/-- Applying the precomposition map to a linear map yields its composition with the fixed map. -/
@[simp] theorem LinearMap.precompLinear_apply (s : M →ₗ[R] M') (φ : M' →ₗ[R] L) :
    LinearMap.precompLinear k s φ = φ ∘ₗ s := rfl

end Lcomp

section HomTensorHom

variable (P₁ P₂ N₁ N₂ : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ P₁] [IsScalarTower k A₁ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ P₂] [IsScalarTower k A₂ P₂]
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
  [instP : Module (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂)]
  [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)] [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]


/-- Forms the linear map on tensor products induced by a pair of linear maps, assuming the specified pure-tensor scalar actions. -/
noncomputable def TensorProduct.mapLinear
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

/-- The induced linear map sends a pure tensor to the tensor of the two componentwise images. -/
@[simp] theorem TensorProduct.mapLinear_tmul (f₁ : P₁ →ₗ[A₁] N₁) (f₂ : P₂ →ₗ[A₂] N₂) (p₁ : P₁) (p₂ : P₂) :
    TensorProduct.mapLinear k A₁ A₂ P₁ P₂ N₁ N₂ hP hN f₁ f₂ (p₁ ⊗ₜ[k] p₂) = f₁ p₁ ⊗ₜ[k] f₂ p₂ :=
  rfl


/-- Two linear maps out of a tensor product are equal when they agree on every pure tensor. -/
theorem LinearMap.ext_tmul {g h : (P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)}
    (H : ∀ (p₁ : P₁) (p₂ : P₂), g (p₁ ⊗ₜ[k] p₂) = h (p₁ ⊗ₜ[k] p₂)) : g = h := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p₁ p₂ => exact H p₁ p₂
  | add x y hx hy => rw [map_add, map_add, hx, hy]


/-- Maps a tensor of linear maps to the linear map induced between the corresponding tensor-product modules. -/
noncomputable def TensorProduct.linearMapTensor :
    ((P₁ →ₗ[A₁] N₁) ⊗[k] (P₂ →ₗ[A₂] N₂)) →ₗ[k]
      ((P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) :=
  TensorProduct.lift
    { toFun := fun f₁ =>
        { toFun := fun f₂ => TensorProduct.mapLinear k A₁ A₂ P₁ P₂ N₁ N₂ hP hN f₁ f₂
          map_add' := fun f₂ f₂' => LinearMap.ext_tmul k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by
            simp [TensorProduct.tmul_add]
          map_smul' := fun c f₂ => LinearMap.ext_tmul k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by
            simp [TensorProduct.tmul_smul] }
      map_add' := fun f₁ f₁' => LinearMap.ext fun f₂ =>
        LinearMap.ext_tmul k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by simp [TensorProduct.add_tmul]
      map_smul' := fun c f₁ => LinearMap.ext fun f₂ =>
        LinearMap.ext_tmul k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => by
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, TensorProduct.mapLinear_tmul,
            TensorProduct.smul_tmul', RingHom.id_apply] }


/-- A pure tensor of linear maps sends a pure tensor of vectors to the tensor of their componentwise images. -/
@[simp] theorem TensorProduct.linearMapTensor_tmul_apply_tmul
    (f₁ : P₁ →ₗ[A₁] N₁) (f₂ : P₂ →ₗ[A₂] N₂) (p₁ : P₁) (p₂ : P₂) :
    TensorProduct.linearMapTensor k A₁ A₂ P₁ P₂ N₁ N₂ hP hN (f₁ ⊗ₜ[k] f₂) (p₁ ⊗ₜ[k] p₂)
      = f₁ p₁ ⊗ₜ[k] f₂ p₂ := by
  rw [TensorProduct.linearMapTensor, TensorProduct.lift.tmul]
  rfl

end HomTensorHom

section FreeCaseAux


/-- Reindexes a doubly finite family as a family on the product of its two finite index types. -/
def LinearEquiv.finFunctionProd (X : Type u) [AddCommGroup X] [Module k X] (n m : ℕ) :
    (Fin n → Fin m → X) ≃ₗ[k] (Fin n × Fin m → X) where
  toFun f := fun p => f p.1 p.2
  invFun g := fun i j => g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv g := by funext p; obtain ⟨i, j⟩ := p; rfl

/-- The reindexed family has at each pair the value of the original doubly indexed family at its two components. -/
@[simp] theorem LinearEquiv.finFunctionProd_apply (X : Type u) [AddCommGroup X] [Module k X] (n m : ℕ)
    (f : Fin n → Fin m → X) (i : Fin n) (j : Fin m) :
    LinearEquiv.finFunctionProd k X n m f (i, j) = f i j := rfl


/-- Identifies the tensor product of two finite families with the family of tensor products indexed by pairs. -/
noncomputable def TensorProduct.finFunctionTensorEquiv (M₁ M₂ : Type u)
    [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] (n m : ℕ) :
    ((Fin n → M₁) ⊗[k] (Fin m → M₂)) ≃ₗ[k] (Fin n × Fin m → M₁ ⊗[k] M₂) :=
  (TensorProduct.piLeft k (Fin m → M₂) (fun _ : Fin n => M₁)) ≪≫ₗ
    (LinearEquiv.piCongrRight fun _ : Fin n =>
      TensorProduct.piRight k k M₁ (fun _ : Fin m => M₂)) ≪≫ₗ
    LinearEquiv.finFunctionProd k (M₁ ⊗[k] M₂) n m

/-- On a pure tensor of finite families, the coordinate at a pair is the tensor of the corresponding coordinates. -/
@[simp] theorem TensorProduct.finFunctionTensorEquiv_tmul_apply (M₁ M₂ : Type u)
    [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] (n m : ℕ)
    (x₁ : Fin n → M₁) (x₂ : Fin m → M₂) (i : Fin n) (j : Fin m) :
    TensorProduct.finFunctionTensorEquiv k M₁ M₂ n m (x₁ ⊗ₜ[k] x₂) (i, j) = x₁ i ⊗ₜ[k] x₂ j := by
  simp [TensorProduct.finFunctionTensorEquiv]

section Precomp

variable {R : Type u} [Ring R] [Algebra k R] {X Y L : Type u}
  [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]
  [AddCommGroup Y] [Module k Y] [Module R Y] [IsScalarTower k R Y]
  [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]


/-- A linear equivalence of domains induces a base-linear equivalence between linear-map spaces by precomposition with its inverse. -/
def LinearEquiv.precomp (e : X ≃ₗ[R] Y) : (X →ₗ[R] L) ≃ₗ[k] (Y →ₗ[R] L) where
  toFun φ := φ ∘ₗ (e.symm : Y →ₗ[R] X)
  invFun ψ := ψ ∘ₗ (e : X →ₗ[R] Y)
  map_add' a b := by ext y; simp
  map_smul' c a := by ext y; simp
  left_inv φ := by ext x; simp
  right_inv ψ := by ext y; simp

/-- The induced equivalence evaluates a linear map at the inverse image of the given argument. -/
@[simp] theorem LinearEquiv.precomp_apply (e : X ≃ₗ[R] Y) (φ : X →ₗ[R] L) (y : Y) :
    LinearEquiv.precomp k e φ y = φ (e.symm y) := rfl

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


/-- The map from tensors of linear maps is bijective when its source modules are finite families of their respective scalar algebras. -/
theorem TensorProduct.linearMapTensor_fin_bijective (n m : ℕ)
    [instF : Module (A₁ ⊗[k] A₂) ((Fin n → A₁) ⊗[k] (Fin m → A₂))]
    [IsScalarTower k (A₁ ⊗[k] A₂) ((Fin n → A₁) ⊗[k] (Fin m → A₂))]
    (hF : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : Fin n → A₁) (x₂ : Fin m → A₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : (Fin n → A₁) ⊗[k] (Fin m → A₂))
        = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    Function.Bijective
      (TensorProduct.linearMapTensor k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ hF hN) := by
  classical
  set F := TensorProduct.linearMapTensor k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ hF hN with hFdef
  -- Step 1: the external free-basis equivalence
  -- `B : (A₁^n) ⊗ₖ (A₂^m) ≃ₗ[A₁⊗A₂] (A₁⊗A₂)^{n×m}`. Its underlying function is the purely
  -- `k`-linear `TensorProduct.finFunctionTensorEquiv`; the pinning `hF` upgrades it to `A₁ ⊗ A₂`-linearity.
  let Bfwd : ((Fin n → A₁) ⊗[k] (Fin m → A₂)) →ₗ[A₁ ⊗[k] A₂]
      (Fin n × Fin m → A₁ ⊗[k] A₂) :=
    { toFun := TensorProduct.finFunctionTensorEquiv k A₁ A₂ n m
      map_add' := (TensorProduct.finFunctionTensorEquiv k A₁ A₂ n m).map_add
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
                simp only [TensorProduct.finFunctionTensorEquiv_tmul_apply, Pi.smul_apply, smul_eq_mul,
                  Algebra.TensorProduct.tmul_mul_tmul] }
  have hBfwd_bij : Function.Bijective Bfwd := (TensorProduct.finFunctionTensorEquiv k A₁ A₂ n m).bijective
  let B : ((Fin n → A₁) ⊗[k] (Fin m → A₂)) ≃ₗ[A₁ ⊗[k] A₂]
      (Fin n × Fin m → A₁ ⊗[k] A₂) := LinearEquiv.ofBijective Bfwd hBfwd_bij
  have hB_tmul : ∀ (x₁ : Fin n → A₁) (x₂ : Fin m → A₂) (i : Fin n) (j : Fin m),
      B (x₁ ⊗ₜ[k] x₂) (i, j) = x₁ i ⊗ₜ[k] x₂ j :=
    fun x₁ x₂ i j => TensorProduct.finFunctionTensorEquiv_tmul_apply k A₁ A₂ n m x₁ x₂ i j
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
  let midE := TensorProduct.finFunctionTensorEquiv k N₁ N₂ n m
  let cT : ((Fin n × Fin m → A₁ ⊗[k] A₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) ≃ₗ[k]
      (Fin n × Fin m → N₁ ⊗[k] N₂) :=
    ((Pi.basisFun (A₁ ⊗[k] A₂) (Fin n × Fin m)).constr k).symm
  let tgtE := (LinearEquiv.precomp k B).trans cT
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
                (LinearEquiv.precomp k B (F (f₁ ⊗ₜ[k] f₂))) (i, j) = _
            rw [Module.Basis.constr_symm_apply, LinearEquiv.precomp_apply, Pi.basisFun_apply]
          have hrhs : midE (srcE (f₁ ⊗ₜ[k] f₂)) (i, j)
              = f₁ (Pi.single i 1) ⊗ₜ[k] f₂ (Pi.single j 1) := by
            change TensorProduct.finFunctionTensorEquiv k N₁ N₂ n m
                (TensorProduct.congr c₁ c₂ (f₁ ⊗ₜ[k] f₂)) (i, j) = _
            rw [TensorProduct.congr_tmul, TensorProduct.finFunctionTensorEquiv_tmul_apply]
            change (((Pi.basisFun A₁ (Fin n)).constr k).symm f₁) i ⊗ₜ[k]
                (((Pi.basisFun A₂ (Fin m)).constr k).symm f₂) j = _
            rw [Module.Basis.constr_symm_apply, Module.Basis.constr_symm_apply,
              Pi.basisFun_apply, Pi.basisFun_apply]
          rw [hlhs, hB_single, hFdef, TensorProduct.linearMapTensor_tmul_apply_tmul, hrhs]
        rw [hEval, ← hgen, tgtE.symm_apply_apply]
  have hFE : ⇑F = ⇑E := funext key
  rw [hFE]
  exact E.bijective


/-- The map from tensors of linear maps to induced maps on tensor products is bijective when both source modules are finite and projective. -/
theorem TensorProduct.linearMapTensor_bijective
    [Module.Finite A₁ P₁] [Module.Projective A₁ P₁]
    [Module.Finite A₂ P₂] [Module.Projective A₂ P₂]
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    Function.Bijective (TensorProduct.linearMapTensor k A₁ A₂ P₁ P₂ N₁ N₂ hP hN) := by
  obtain ⟨n, r₁, s₁, _, _, hrs₁⟩ := Module.Finite.exists_comp_eq_id_of_projective A₁ P₁
  obtain ⟨m, r₂, s₂, _, _, hrs₂⟩ := Module.Finite.exists_comp_eq_id_of_projective A₂ P₂
  -- `rᵢ : (Fin nᵢ → Aᵢ) →ₗ[Aᵢ] Pᵢ` is the retraction, `sᵢ : Pᵢ →ₗ[Aᵢ] (Fin nᵢ → Aᵢ)` the section,
  -- and `rᵢ ∘ₗ sᵢ = id`.
  letI iF := TensorProduct.moduleOverTensorProduct k A₁ A₂ (Fin n → A₁) (Fin m → A₂)
  haveI := TensorProduct.isScalarTower_moduleOverTensorProduct k A₁ A₂ (Fin n → A₁) (Fin m → A₂)
  have hF := TensorProduct.smul_tmul_moduleOverTensorProduct k A₁ A₂ (Fin n → A₁) (Fin m → A₂)
  have hfree := TensorProduct.linearMapTensor_fin_bijective k A₁ A₂ N₁ N₂ n m hF hN
  set Hfree := TensorProduct.linearMapTensor k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ hF hN with hHfree
  set HP := TensorProduct.linearMapTensor k A₁ A₂ P₁ P₂ N₁ N₂ hP hN with hHP
  set E := LinearEquiv.ofBijective Hfree hfree with hE
  -- External `A₁ ⊗ A₂`-linear maps `Fin n → A₁) ⊗ (Fin m → A₂) ↔ P₁ ⊗ P₂`.
  set t_r := TensorProduct.mapLinear k A₁ A₂ (Fin n → A₁) (Fin m → A₂) P₁ P₂ hF hP r₁ r₂ with ht_r
  set t_s := TensorProduct.mapLinear k A₁ A₂ P₁ P₂ (Fin n → A₁) (Fin m → A₂) hP hF s₁ s₂ with ht_s
  -- The `k`-linear retract maps on the `Hom ⊗ Hom` side.
  set S := TensorProduct.map (LinearMap.precompLinear (L := N₁) k s₁) (LinearMap.precompLinear (L := N₂) k s₂) with hS
  set R := TensorProduct.map (LinearMap.precompLinear (L := N₁) k r₁) (LinearMap.precompLinear (L := N₂) k r₂) with hR
  -- Naturality of `TensorProduct.linearMapTensor` in the source.
  have NAT1 : ∀ x, (HP x) ∘ₗ t_r = Hfree (R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, LinearMap.add_comp, ha, hb, map_add, map_add]
    | tmul f g =>
        refine LinearMap.ext_tmul k A₁ A₂ (Fin n → A₁) (Fin m → A₂) N₁ N₂ fun x₁ x₂ => ?_
        simp only [hHP, hHfree, ht_r, hR, LinearMap.comp_apply, TensorProduct.map_tmul,
          LinearMap.precompLinear_apply, TensorProduct.mapLinear_tmul, TensorProduct.linearMapTensor_tmul_apply_tmul]
  have NAT2 : ∀ y, HP (S y) = (Hfree y) ∘ₗ t_s := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, LinearMap.add_comp]
    | tmul f g =>
        refine LinearMap.ext_tmul k A₁ A₂ P₁ P₂ N₁ N₂ fun p₁ p₂ => ?_
        simp only [hHP, hHfree, ht_s, hS, LinearMap.comp_apply, TensorProduct.map_tmul,
          LinearMap.precompLinear_apply, TensorProduct.mapLinear_tmul, TensorProduct.linearMapTensor_tmul_apply_tmul]
  -- `S ∘ R = id` on the `Hom ⊗ Hom` side.
  have RETR : ∀ x, S (R x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul f g =>
        simp only [hS, hR, TensorProduct.map_tmul, LinearMap.precompLinear_apply, LinearMap.comp_assoc, hrs₁,
          hrs₂, LinearMap.comp_id]
  -- `t_r ∘ₗ t_s = id` on `P₁ ⊗ P₂`.
  have RETR' : t_r ∘ₗ t_s = LinearMap.id := by
    refine LinearMap.ext_tmul k A₁ A₂ P₁ P₂ P₁ P₂ fun p₁ p₂ => ?_
    have e1 : r₁ (s₁ p₁) = p₁ := by rw [← LinearMap.comp_apply, hrs₁, LinearMap.id_apply]
    have e2 : r₂ (s₂ p₂) = p₂ := by rw [← LinearMap.comp_apply, hrs₂, LinearMap.id_apply]
    simp only [ht_r, ht_s, LinearMap.comp_apply, TensorProduct.mapLinear_tmul, LinearMap.id_coe, id_eq, e1, e2]
  -- Construct the two-sided inverse.
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun Φ => S (E.symm (LinearMap.precompLinear k t_r Φ)), fun x => ?_, fun Φ => ?_⟩
  · -- left inverse
    change S (E.symm (LinearMap.precompLinear k t_r (HP x))) = x
    rw [LinearMap.precompLinear_apply, NAT1 x, show Hfree (R x) = E (R x) from rfl,
      LinearEquiv.symm_apply_apply, RETR]
  · -- right inverse
    change HP (S (E.symm (LinearMap.precompLinear k t_r Φ))) = Φ
    rw [NAT2 (E.symm (LinearMap.precompLinear k t_r Φ)),
      show Hfree (E.symm (LinearMap.precompLinear k t_r Φ)) = E (E.symm (LinearMap.precompLinear k t_r Φ)) from rfl,
      LinearEquiv.apply_symm_apply, LinearMap.precompLinear_apply, LinearMap.comp_assoc, RETR', LinearMap.comp_id]


/-- For finite projective source modules, tensoring spaces of linear maps is linearly equivalent to the space of induced maps between tensor products. -/
noncomputable def TensorProduct.linearMapTensorEquiv
    [Module.Finite A₁ P₁] [Module.Projective A₁ P₁]
    [Module.Finite A₂ P₂] [Module.Projective A₂ P₂]
    (hP : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : P₁) (x₂ : P₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : P₁ ⊗[k] P₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (x₁ : N₁) (x₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (x₁ ⊗ₜ[k] x₂ : N₁ ⊗[k] N₂) = (a₁ • x₁) ⊗ₜ[k] (a₂ • x₂)) :
    ((P₁ →ₗ[A₁] N₁) ⊗[k] (P₂ →ₗ[A₂] N₂)) ≃ₗ[k]
      ((P₁ ⊗[k] P₂) →ₗ[A₁ ⊗[k] A₂] (N₁ ⊗[k] N₂)) :=
  LinearEquiv.ofBijective (TensorProduct.linearMapTensor k A₁ A₂ P₁ P₂ N₁ N₂ hP hN)
    (TensorProduct.linearMapTensor_bijective k A₁ A₂ P₁ P₂ N₁ N₂ hP hN)

end Main

end RepresentationTheory.TensorProduct.LinearMap


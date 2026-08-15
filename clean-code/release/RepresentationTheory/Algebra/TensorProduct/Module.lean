/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Tower

open TensorProduct

namespace RepresentationTheory.Algebra.TensorProduct.Module

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (M₁ M₂ : Type u)
  [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁] [IsScalarTower k A₁ M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂] [IsScalarTower k A₂ M₂]

/-- Packages the tensor-product algebra action as a homomorphism into module endomorphisms. -/
noncomputable def TensorProduct.moduleEndAlgHom :
    (A₁ ⊗[k] A₂) →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := M₁) (N := M₂)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul (A := A₁) k k M₁)
      (Algebra.lsmul (A := A₂) k k M₂))

/-- Provides the natural tensor-product algebra module structure on the tensor product of modules. -/
@[reducible] noncomputable def TensorProduct.instModule : Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂) :=
  Module.compHom (M₁ ⊗[k] M₂) (R := Module.End k (M₁ ⊗[k] M₂))
    (TensorProduct.moduleEndAlgHom k A₁ A₂ M₁ M₂).toRingHom

/-- Scalar multiplication of pure tensors is computed componentwise. -/
theorem TensorProduct.smul_tmul (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂) :
    (TensorProduct.instModule k A₁ A₂ M₁ M₂).toSMul.smul
        (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) (m₁ ⊗ₜ[k] m₂)
      = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂) := by
  change TensorProduct.moduleEndAlgHom k A₁ A₂ M₁ M₂
      (a₁ ⊗ₜ[k] a₂) (m₁ ⊗ₜ[k] m₂) = _
  rw [TensorProduct.moduleEndAlgHom, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Module.endTensorEndAlgHom_apply]
  rfl

end RepresentationTheory.Algebra.TensorProduct.Module

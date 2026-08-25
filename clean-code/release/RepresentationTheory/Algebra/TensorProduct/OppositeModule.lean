/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.Abelian.ObjectData
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.Algebra.Tower

open TensorProduct MulOpposite

namespace RepresentationTheory.Algebra.TensorProduct.OppositeModule

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (M₁ M₂ : Type u)
  [AddCommGroup M₁] [Module k M₁] [Module A₁ᵐᵒᵖ M₁] [IsScalarTower k A₁ᵐᵒᵖ M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ᵐᵒᵖ M₂] [IsScalarTower k A₂ᵐᵒᵖ M₂]

/-- The action homomorphism from the tensor product of opposite algebras to module endomorphisms. -/
noncomputable def TensorProduct.tensorProductOppositeAction :
    (A₁ᵐᵒᵖ ⊗[k] A₂ᵐᵒᵖ) →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := M₁) (N := M₂)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul (A := A₁ᵐᵒᵖ) k k M₁)
      (Algebra.lsmul (A := A₂ᵐᵒᵖ) k k M₂))

/-- The algebra action of the opposite tensor product on the tensor product of modules. -/
noncomputable def TensorProduct.opTensorProductAction :
    (A₁ ⊗[k] A₂)ᵐᵒᵖ →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (TensorProduct.tensorProductOppositeAction k A₁ A₂ M₁ M₂).comp
    (Algebra.TensorProduct.opAlgEquiv k k A₁ A₂).symm.toAlgHom

/-- The module structure on a tensor product induced by right actions on both factors. -/
@[reducible] noncomputable def TensorProduct.moduleOppositeTensorProduct :
    Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂) :=
  Module.compHom (M₁ ⊗[k] M₂) (R := Module.End k (M₁ ⊗[k] M₂))
    (TensorProduct.opTensorProductAction k A₁ A₂ M₁ M₂).toRingHom

/-- Acting by an opposite pure tensor on a pure module tensor acts componentwise. -/
theorem TensorProduct.op_tmul_smul_tmul (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂) :
    (TensorProduct.moduleOppositeTensorProduct k A₁ A₂ M₁ M₂).toSMul.smul
        (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) (m₁ ⊗ₜ[k] m₂)
      = (MulOpposite.op a₁ • m₁) ⊗ₜ[k] (MulOpposite.op a₂ • m₂) := by
  change TensorProduct.opTensorProductAction k A₁ A₂ M₁ M₂
    (MulOpposite.op (a₁ ⊗ₜ[k] a₂)) (m₁ ⊗ₜ[k] m₂) = _
  rw [TensorProduct.opTensorProductAction, AlgHom.comp_apply]
  rw [show (Algebra.TensorProduct.opAlgEquiv k k A₁ A₂).symm.toAlgHom
        (MulOpposite.op (a₁ ⊗ₜ[k] a₂)) = MulOpposite.op a₁ ⊗ₜ[k] MulOpposite.op a₂ from by
    rw [AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.opAlgEquiv_symm_apply]
    rfl]
  rw [TensorProduct.tensorProductOppositeAction, AlgHom.comp_apply,
    Algebra.TensorProduct.map_tmul, Module.endTensorEndAlgHom_apply]
  rfl

end RepresentationTheory.Algebra.TensorProduct.OppositeModule

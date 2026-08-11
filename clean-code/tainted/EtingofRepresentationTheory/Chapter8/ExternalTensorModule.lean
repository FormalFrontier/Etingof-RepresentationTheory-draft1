import EtingofRepresentationTheory.Chapter8.Definition8_2_1
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.Algebra.Tower

/-!
# The external tensor product module over a tensor product of algebras

Let `k` be a commutative ring, `A₁, A₂` be `k`-algebras, and let `M₁` be a right `A₁`-module
(i.e. a left `A₁ᵐᵒᵖ`-module) and `M₂` a right `A₂`-module, both `k`-linearly. Then the
`k`-vector space `M₁ ⊗[k] M₂` is a right `A₁ ⊗[k] A₂`-module (a left `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-module)
with the **external** action `(m₁ ⊗ m₂) · (a₁ ⊗ a₂) = (m₁ · a₁) ⊗ (m₂ · a₂)`.

This is the keystone module structure for the Künneth formula for `Tor` over a tensor product of
algebras (Problem 8.2.8): it is what equips each term `(P₁)ⱼ ⊗[k] (P₂)ₘ` of a tensor of
projective resolutions with its `(A₁ ⊗ A₂)ᵐᵒᵖ`-action.

## Construction

We build the action representation-theoretically, mirroring `Etingof.Problem3_8_4.rep`:

* `Algebra.lsmul k k Mᵢ : Aᵢᵐᵒᵖ →ₐ[k] Module.End k Mᵢ` is the action of `Aᵢᵐᵒᵖ` on `Mᵢ`;
* `Algebra.TensorProduct.map` tensors these to `A₁ᵐᵒᵖ ⊗[k] A₂ᵐᵒᵖ →ₐ[k] End M₁ ⊗[k] End M₂`;
* `Module.endTensorEndAlgHom` lands in `Module.End k (M₁ ⊗[k] M₂)`;
* `Algebra.TensorProduct.opAlgEquiv : A₁ᵐᵒᵖ ⊗[k] A₂ᵐᵒᵖ ≃ₐ[k] (A₁ ⊗[k] A₂)ᵐᵒᵖ` transports the
  action to `(A₁ ⊗[k] A₂)ᵐᵒᵖ`;
* `Module.compHom` turns the resulting algebra map into a `Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂)`.

`extTensorModule_op_smul_tmul` pins the action on simple tensors: this is exactly the hypothesis
`hM` axiomatised in `Etingof.Problem_8_2_8_tor`, now realised by an actual construction.
-/

open TensorProduct MulOpposite

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (M₁ M₂ : Type u)
  [AddCommGroup M₁] [Module k M₁] [Module A₁ᵐᵒᵖ M₁] [IsScalarTower k A₁ᵐᵒᵖ M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ᵐᵒᵖ M₂] [IsScalarTower k A₂ᵐᵒᵖ M₂]

/-- The representation of `A₁ᵐᵒᵖ ⊗[k] A₂ᵐᵒᵖ` on `M₁ ⊗[k] M₂`: `A₁ᵐᵒᵖ` acts on the left factor and
`A₂ᵐᵒᵖ` on the right factor. It is the composite
`End M₁ ⊗ End M₂ →ₐ End (M₁ ⊗ M₂)` of the tensor of the two componentwise actions. -/
noncomputable def extTensorRepAux :
    (A₁ᵐᵒᵖ ⊗[k] A₂ᵐᵒᵖ) →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := M₁) (N := M₂)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul (A := A₁ᵐᵒᵖ) k k M₁)
      (Algebra.lsmul (A := A₂ᵐᵒᵖ) k k M₂))

/-- The representation of `(A₁ ⊗[k] A₂)ᵐᵒᵖ` on `M₁ ⊗[k] M₂`, obtained from `extTensorRepAux` by
transporting along `Algebra.TensorProduct.opAlgEquiv`. -/
noncomputable def extTensorRep :
    (A₁ ⊗[k] A₂)ᵐᵒᵖ →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (extTensorRepAux k A₁ A₂ M₁ M₂).comp
    (Algebra.TensorProduct.opAlgEquiv k k A₁ A₂).symm.toAlgHom

/-- The **external tensor product module**: `M₁ ⊗[k] M₂` as a left `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-module,
i.e. a right `A₁ ⊗[k] A₂`-module, with the componentwise action
`(m₁ ⊗ m₂) · (a₁ ⊗ a₂) = (m₁ · a₁) ⊗ (m₂ · a₂)`. -/
@[reducible] noncomputable def extTensorModule : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂) :=
  Module.compHom (M₁ ⊗[k] M₂) (R := Module.End k (M₁ ⊗[k] M₂))
    (extTensorRep k A₁ A₂ M₁ M₂).toRingHom

/-- The external action on a simple tensor is componentwise:
`(m₁ ⊗ m₂) · (a₁ ⊗ a₂) = (m₁ · a₁) ⊗ (m₂ · a₂)`, phrased on the left `(A₁ ⊗ A₂)ᵐᵒᵖ`-module.
This is exactly the hypothesis `hM` of `Etingof.Problem_8_2_8_tor`. -/
theorem extTensorModule_op_smul_tmul (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂) :
    (extTensorModule k A₁ A₂ M₁ M₂).toSMul.smul
        (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) (m₁ ⊗ₜ[k] m₂)
      = (MulOpposite.op a₁ • m₁) ⊗ₜ[k] (MulOpposite.op a₂ • m₂) := by
  change extTensorRep k A₁ A₂ M₁ M₂ (MulOpposite.op (a₁ ⊗ₜ[k] a₂)) (m₁ ⊗ₜ[k] m₂) = _
  rw [extTensorRep, AlgHom.comp_apply]
  rw [show (Algebra.TensorProduct.opAlgEquiv k k A₁ A₂).symm.toAlgHom
        (MulOpposite.op (a₁ ⊗ₜ[k] a₂)) = MulOpposite.op a₁ ⊗ₜ[k] MulOpposite.op a₂ from by
    rw [AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.opAlgEquiv_symm_apply]
    rfl]
  rw [extTensorRepAux, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Module.endTensorEndAlgHom_apply]
  rfl

end Etingof

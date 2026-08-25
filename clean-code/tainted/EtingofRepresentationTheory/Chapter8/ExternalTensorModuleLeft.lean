import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Tower

/-!
# The external tensor product module over a tensor product of algebras (left modules)

Let `k` be a commutative ring, `A₁, A₂` be `k`-algebras, and let `M₁` be a **left** `A₁`-module and
`M₂` a **left** `A₂`-module, both `k`-linearly (`IsScalarTower k Aᵢ Mᵢ`). Then the `k`-vector space
`M₁ ⊗[k] M₂` is a **left** `A₁ ⊗[k] A₂`-module with the **external** action
`(a₁ ⊗ a₂) • (m₁ ⊗ m₂) = (a₁ • m₁) ⊗ (a₂ • m₂)`.

This is the left-module twin of `Etingof.extTensorModule` (in `ExternalTensorModule.lean`, phrased
through `ᵐᵒᵖ` for right modules and used by the `Tor` half of Problem 8.2.8). Here we need the plain
left-module version: it equips `M₁ ⊗[k] M₂` and `N₁ ⊗[k] N₂` with the module structures
`instM`/`instN` axiomatised in `Etingof.Problem_8_2_8_ext` (the `Ext` half), now realised by an
actual construction, and it is the structure the cohomological rearrangement machinery consumes.

## Construction

We build the action representation-theoretically, exactly as in the right-module case but without
the `Algebra.TensorProduct.opAlgEquiv` transport:

* `Algebra.lsmul k k Mᵢ : Aᵢ →ₐ[k] Module.End k Mᵢ` is the action of `Aᵢ` on `Mᵢ`;
* `Algebra.TensorProduct.map` tensors these to `A₁ ⊗[k] A₂ →ₐ[k] End M₁ ⊗[k] End M₂`;
* `Module.endTensorEndAlgHom` lands in `Module.End k (M₁ ⊗[k] M₂)`;
* `Module.compHom` turns the resulting algebra map into a `Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂)`.

`extTensorModuleLeft_smul_tmul` pins the action on simple tensors: this is exactly the hypothesis
`hM` / `hN` axiomatised in `Etingof.Problem_8_2_8_ext`, now realised by an actual construction.
-/

open TensorProduct

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (M₁ M₂ : Type u)
  [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁] [IsScalarTower k A₁ M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂] [IsScalarTower k A₂ M₂]

/-- The representation of `A₁ ⊗[k] A₂` on `M₁ ⊗[k] M₂`: `A₁` acts on the left factor and `A₂` on the
right factor. It is the composite `End M₁ ⊗ End M₂ →ₐ End (M₁ ⊗ M₂)` of the tensor of the two
componentwise actions. -/
noncomputable def extTensorRepLeft :
    (A₁ ⊗[k] A₂) →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := M₁) (N := M₂)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul (A := A₁) k k M₁)
      (Algebra.lsmul (A := A₂) k k M₂))

/-- The **external tensor product module** (left version): `M₁ ⊗[k] M₂` as a left
`A₁ ⊗[k] A₂`-module, with the componentwise action
`(a₁ ⊗ a₂) • (m₁ ⊗ m₂) = (a₁ • m₁) ⊗ (a₂ • m₂)`. -/
@[reducible] noncomputable def extTensorModuleLeft : Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂) :=
  Module.compHom (M₁ ⊗[k] M₂) (R := Module.End k (M₁ ⊗[k] M₂))
    (extTensorRepLeft k A₁ A₂ M₁ M₂).toRingHom

/-- The external action on a simple tensor is componentwise:
`(a₁ ⊗ a₂) • (m₁ ⊗ m₂) = (a₁ • m₁) ⊗ (a₂ • m₂)`. This is exactly the hypotheses `hM` / `hN` of
`Etingof.Problem_8_2_8_ext`. -/
theorem extTensorModuleLeft_smul_tmul (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂) :
    (extTensorModuleLeft k A₁ A₂ M₁ M₂).toSMul.smul
        (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) (m₁ ⊗ₜ[k] m₂)
      = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂) := by
  change extTensorRepLeft k A₁ A₂ M₁ M₂ (a₁ ⊗ₜ[k] a₂) (m₁ ⊗ₜ[k] m₂) = _
  rw [extTensorRepLeft, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Module.endTensorEndAlgHom_apply]
  rfl

end Etingof

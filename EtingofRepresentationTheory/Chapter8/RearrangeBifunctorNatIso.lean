import EtingofRepresentationTheory.Chapter8.RearrangeBidegreeNat
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The bifunctor natural isomorphism for the `Tor` Künneth rearrangement

Route **step 2** of milestone (c) of the four-fold rearrangement (Problem 8.2.8 `Tor`). Milestones
(a) `Etingof.rearrangeBidegree` (`RearrangeBidegree.lean`) and (b)
`Etingof.rearrangeBidegree_naturality` (`RearrangeBidegreeNat.lean`) provide, for each pair of right
modules `(X, Y)`, a `k`-linear isomorphism

  `tensorOver (A₁⊗A₂) (N₁⊗ₖN₂) (X⊗ₖY) ≃ₗ[k] (tensorOver A₁ N₁ X) ⊗ₖ (tensorOver A₂ N₂ Y)`

natural in `X` and `Y`. This file packages that data as a **natural isomorphism of bifunctors**

  `rearrangeBifunctorNatIso :`
  `extTensorFunctor ⋙ tensorRightₖ(N₁⊗ₖN₂)  ≅  (tensorRightₖ N₁ · ) ⊗ (tensorRightₖ N₂ · )`

of type `ModuleCat A₁ᵐᵒᵖ ⥤ ModuleCat A₂ᵐᵒᵖ ⥤ ModuleCat k`. The left bifunctor is a post-composition
of the external tensor bifunctor with `Etingof.tensorRightFunctorₖ k (A₁⊗A₂) (N₁⊗ₖN₂)`; the right is
`(X, Y) ↦ (X ⊗_{A₁} N₁) ⊗ₖ (Y ⊗_{A₂} N₂)`, assembled from the two factor functors and the monoidal
tensor on `ModuleCat k`.

Downstream (route step 3, the final assembly of the `ChainComplex (ModuleCat k) ℕ` rearrangement
iso) transports this natural iso through `HomologicalComplex.mapBifunctor`.
-/

open CategoryTheory MonoidalCategory TensorProduct MulOpposite

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

/-! ### Restriction-of-scalars instances on the `ModuleCat` carriers

The same `local instance`s as `ExternalTensorFunctor.lean` / `TensorRightFunctorK.lean`, brought
into scope so that `(tensorRightFunctorₖ k (A₁⊗A₂) (N₁⊗ₖN₂)).obj (extTensorFunctorObj X Y)` is the
`ModuleCat k` on `tensorOver (A₁⊗A₂) (N₁⊗ₖN₂) (X⊗ₖY)` with the external action expected by
`rearrangeBidegree`. -/

noncomputable local instance instModuleK₁ (X : ModuleCat.{u} A₁ᵐᵒᵖ) : Module k X :=
  Module.compHom X (algebraMap k A₁ᵐᵒᵖ)

noncomputable local instance instModuleK₂ (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : Module k Y :=
  Module.compHom Y (algebraMap k A₂ᵐᵒᵖ)

local instance instTower₁ (X : ModuleCat.{u} A₁ᵐᵒᵖ) : IsScalarTower k A₁ᵐᵒᵖ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance instTower₂ (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : IsScalarTower k A₂ᵐᵒᵖ Y :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance instComm₁ (X : ModuleCat.{u} A₁ᵐᵒᵖ) : SMulCommClass k A₁ᵐᵒᵖ X where
  smul_comm c a m := by
    change (algebraMap k A₁ᵐᵒᵖ c) • (a • m) = a • ((algebraMap k A₁ᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

local instance instComm₂ (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : SMulCommClass k A₂ᵐᵒᵖ Y where
  smul_comm c a m := by
    change (algebraMap k A₂ᵐᵒᵖ c) • (a • m) = a • ((algebraMap k A₂ᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action on `X ⊗[k] Y`, matching `ExternalTensorFunctor.lean`. -/
noncomputable local instance instExtModule (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) := extTensorModule k A₁ A₂ X Y

/-- `k` commutes with the external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action, because the action is realised by a
`k`-algebra map into `Module.End k (X ⊗[k] Y)`, whose values are `k`-linear endomorphisms. -/
local instance instCommExt (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) where
  smul_comm c r m := by
    change c • (extTensorRep k A₁ A₂ X Y r m) = extTensorRep k A₁ A₂ X Y r (c • m)
    rw [map_smul]

end Etingof

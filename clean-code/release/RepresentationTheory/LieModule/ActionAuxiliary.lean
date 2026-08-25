/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Lie.AuxiliaryEndomorphismKernelProfiles
import RepresentationTheory.Alignment.Attribute



























open RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices
open RepresentationTheory.LieAlgebra.Sl2Representations
open RepresentationTheory.Algebra.Lie.AuxiliaryEndomorphismKernelProfiles

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RepresentationTheory.LieModule.ActionAuxiliary

section Uniqueness

variable {V : Type*} [AddCommGroup V] [Module ℂ V]





/-- An auxiliary type-valued construction associated with a displayed complex Lie action. -/
@[nolint unusedArguments]
def AuxiliaryType (_ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V) : Type _ := V

namespace AuxiliaryType

variable (ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The additive commutative group structure on the auxiliary type. -/
instance addCommGroup : AddCommGroup (AuxiliaryType ρ) := inferInstanceAs (AddCommGroup V)
/-- The auxiliary type is a module over the complex numbers. -/
instance moduleInstance : Module ℂ (AuxiliaryType ρ) := inferInstanceAs (Module ℂ V)

/-- The auxiliary type is finite-dimensional when the ambient vector space is finite-dimensional. -/
instance finiteDimensional [FiniteDimensional ℂ V] : FiniteDimensional ℂ (AuxiliaryType ρ) :=
  inferInstanceAs (FiniteDimensional ℂ V)
/-- The auxiliary type has the corresponding Lie ring module structure. -/
noncomputable instance lieRingModule : LieRingModule complexTwoByTwoMatrixLieSubalgebra (AuxiliaryType ρ) := LieRingModule.compLieHom V ρ

/-- The auxiliary type carries the indicated complex Lie module structure. -/
instance lieModule : LieModule ℂ complexTwoByTwoMatrixLieSubalgebra (AuxiliaryType ρ) := LieModule.compLieHom V ρ


/-- The displayed value associated with the auxiliary type equals the stated action value. -/
theorem actionAtSpecifiedElement_eq : auxiliaryEndomorphism (AuxiliaryType ρ) = ρ raisingElement := by
  ext m
  change LieModule.toEnd ℂ complexTwoByTwoMatrixLieSubalgebra (AuxiliaryType ρ) raisingElement m = ρ raisingElement m
  rw [LieModule.toEnd_apply_apply]
  rfl

end AuxiliaryType

open AuxiliaryType in




/-- Lie actions with equal displayed action values have equivalent auxiliary types. -/
theorem auxiliaryTypeEquiv_of_actionAtSpecifiedElement_eq [FiniteDimensional ℂ V]
    (ρ ρ' : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V) (h : ρ raisingElement = ρ' raisingElement) :
    Nonempty (AuxiliaryType ρ ≃ₗ⁅ℂ,complexTwoByTwoMatrixLieSubalgebra⁆ AuxiliaryType ρ') := by
  refine nonempty_equiv_of_auxiliaryEndomorphism_kernelProfile_eq (fun k => ?_)
  rw [actionAtSpecifiedElement_eq, actionAtSpecifiedElement_eq, h]
  rfl





/-- A nilpotent endomorphism is the displayed action value of a Lie action, uniquely up to Lie-module equivalence of the auxiliary types. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem exists_auxiliaryLieAction_of_isNilpotent [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (hA : IsNilpotent A) :
    (∃ ρ : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V, ρ raisingElement = A) ∧
      (∀ ρ ρ' : complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V, ρ raisingElement = A → ρ' raisingElement = A →
        Nonempty (AuxiliaryType ρ ≃ₗ⁅ℂ,complexTwoByTwoMatrixLieSubalgebra⁆ AuxiliaryType ρ')) :=
  ⟨_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.exists_witness_aux2 A hA,
    fun ρ ρ' hρ hρ' => auxiliaryTypeEquiv_of_actionAtSpecifiedElement_eq ρ ρ' (hρ.trans hρ'.symm)⟩

end Uniqueness

end RepresentationTheory.LieModule.ActionAuxiliary

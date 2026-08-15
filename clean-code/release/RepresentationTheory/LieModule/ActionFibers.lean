/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Lie.ComplexMatrixModuleClassification
import RepresentationTheory.Alignment.Attribute

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RepresentationTheory.LieModule.ActionFibers

section Uniqueness

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The type associated to a complex Lie algebra action on a complex vector space. -/
@[nolint unusedArguments]
def ActionFiber (_ρ : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V) : Type _ := V

namespace ActionFiber

variable (ρ : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The additive commutative group structure on an action fiber. -/
instance addCommGroup : AddCommGroup (ActionFiber ρ) := inferInstanceAs (AddCommGroup V)

/-- The action fiber is a module over the complex numbers. -/
instance moduleInstance : Module ℂ (ActionFiber ρ) := inferInstanceAs (Module ℂ V)

/-- An action fiber is finite-dimensional when its ambient vector space is finite-dimensional. -/
instance finiteDimensional [FiniteDimensional ℂ V] : FiniteDimensional ℂ (ActionFiber ρ) :=
  inferInstanceAs (FiniteDimensional ℂ V)

/-- The action fiber has the corresponding Lie ring module structure. -/
noncomputable instance lieRingModule : LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (ActionFiber ρ) := LieRingModule.compLieHom V ρ

/-- The action fiber carries the indicated complex Lie module structure. -/
instance lieModule : LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (ActionFiber ρ) := LieModule.compLieHom V ρ

/-- Evaluating the action-fiber construction at the distinguished element recovers the original action. -/
theorem distinguishedElementAction_eq : _root_.RepresentationTheory.Algebra.Lie.ComplexMatrixModuleClassification.distinguishedActionEndomorphism (ActionFiber ρ) = ρ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement := by
  ext m
  change LieModule.toEnd ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (ActionFiber ρ) _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement m = ρ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement m
  rw [LieModule.toEnd_apply_apply]
  rfl

end ActionFiber

open ActionFiber in
/-- Actions agreeing at the distinguished element have equivalent action fibers. -/
theorem actionFiberEquiv_of_distinguishedElementAction_eq [FiniteDimensional ℂ V]
    (ρ ρ' : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V) (h : ρ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement = ρ' _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement) :
    Nonempty (ActionFiber ρ ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ ActionFiber ρ') := by
  refine _root_.RepresentationTheory.Algebra.Lie.ComplexMatrixModuleClassification.nonempty_equiv_of_distinguishedAction_kernelProfile_eq (fun k => ?_)
  rw [distinguishedElementAction_eq, distinguishedElementAction_eq, h]
  rfl

/-- A nilpotent endomorphism occurs as the action of the distinguished element, uniquely up to Lie module equivalence. -/
@[source_ref "Chapter2/Problem2.15.1" (role := primary)]
theorem exists_actionFiber_of_isNilpotent [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (hA : IsNilpotent A) :
    (∃ ρ : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V, ρ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement = A) ∧
      (∀ ρ ρ' : _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra →ₗ⁅ℂ⁆ Module.End ℂ V, ρ _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement = A → ρ' _root_.RepresentationTheory.LieAlgebra.Sl2Representations.raisingElement = A →
        Nonempty (ActionFiber ρ ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ ActionFiber ρ')) :=
  ⟨_root_.RepresentationTheory.LinearAlgebra.NilpotentOperators.exists_witness_aux2 A hA,
    fun ρ ρ' hρ hρ' => actionFiberEquiv_of_distinguishedElementAction_eq ρ ρ' (hρ.trans hρ'.symm)⟩

end Uniqueness

end RepresentationTheory.LieModule.ActionFibers

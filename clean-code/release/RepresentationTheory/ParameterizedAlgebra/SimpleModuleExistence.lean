/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.ParameterizedAlgebra.SimpleModuleClassification
import RepresentationTheory.Alignment.Attribute

/-! # Simple Module Existence -/

namespace RepresentationTheory.ParameterizedAlgebra.SimpleModuleExistence

open RepresentationTheory.Algebra.Module.TwistedLatticeShifts
  RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules
  RepresentationTheory.ParameterizedAlgebra.ModelModules
  RepresentationTheory.QuantumTorus.FiniteOrderModuleEquivalences

section Converse

variable (q α β : ℂˣ)

/-- The displayed parameterized model module is finite-dimensional over the complex numbers. -/
instance modelModule_finiteDimensional : FiniteDimensional ℂ (ThreeUnitParameterType q α β) :=
  inferInstanceAs (FiniteDimensional ℂ (Fin (orderOf q) → ℂ))

variable [NeZero (orderOf q)]

/-- The displayed parameterized model module is simple when the parameter order is nonzero. -/
theorem modelModule_isSimple :
    IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) (ThreeUnitParameterType q α β) :=
  finFunctionModule_isSimple q α β (orderOf q) rfl

omit [NeZero (orderOf q)] in
/-- A finite-order parameter yields a nontrivial finite-dimensional simple module of the stated dimension. -/
theorem exists_nontrivial_finiteSimpleModule_of_isOfFinOrder (hq : IsOfFinOrder q) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : Module (twistedLatticeShiftSubalgebra ℂ q) V)
      (_ : IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V),
      Nontrivial V ∧ FiniteDimensional ℂ V ∧
        IsSimpleModule (twistedLatticeShiftSubalgebra ℂ q) V ∧
        Module.finrank ℂ V = orderOf q := by
  haveI : NeZero (orderOf q) := ⟨(orderOf_pos_iff.mpr hq).ne'⟩
  exact ⟨ThreeUnitParameterType q 1 1, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, modelModule_isSimple q 1 1,
    finrank_threeUnitParameterType q 1 1⟩

omit [NeZero (orderOf q)] in
/-- The parameter has finite order exactly when a nontrivial finite-dimensional module exists. -/
@[source_ref "Chapter2/Problem2.7.5" (role := supporting)]
theorem isOfFinOrder_iff_exists_nontrivial_finiteModule :
    IsOfFinOrder q ↔
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (_ : Module (twistedLatticeShiftSubalgebra ℂ q) V)
        (_ : IsScalarTower ℂ (twistedLatticeShiftSubalgebra ℂ q) V),
        Nontrivial V ∧ FiniteDimensional ℂ V := by
  constructor
  · intro hq
    obtain ⟨V, iag, imc, imq, ist, hnt, hfd, -, -⟩ :=
      exists_nontrivial_finiteSimpleModule_of_isOfFinOrder q hq
    exact ⟨V, iag, imc, imq, ist, hnt, hfd⟩
  · rintro ⟨V, iag, imc, imq, ist, hnt, hfd⟩
    letI := iag; letI := imc; letI := imq; letI := ist
    haveI := hnt; haveI := hfd
    exact isOfFinOrder_of_nontrivial_finiteModule q V

end Converse

end RepresentationTheory.ParameterizedAlgebra.SimpleModuleExistence

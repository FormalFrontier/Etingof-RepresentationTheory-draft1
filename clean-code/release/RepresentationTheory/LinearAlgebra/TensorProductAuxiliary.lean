/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import RepresentationTheory.Alignment.Attribute

/-! # Tensor-product auxiliary constructions -/

open scoped TensorProduct

namespace RepresentationTheory.LinearAlgebra.TensorProductAuxiliary

/-- An auxiliary type. -/
abbrev AuxiliaryType : Type := Fin 2 → ℚ

/-- An auxiliary family indexed by two elements. -/
noncomputable def auxiliaryFamily (i : Fin 2) : AuxiliaryType := Pi.single i 1

/-- An auxiliary family of linear maps from the tensor square of the auxiliary type to the rationals. -/
noncomputable def tensorLinearMapAux (i j : Fin 2) :
    (AuxiliaryType ⊗[ℚ] AuxiliaryType) →ₗ[ℚ] ℚ :=
  TensorProduct.lift (((LinearMap.mul ℚ ℚ).comp (LinearMap.proj i)).compl₂ (LinearMap.proj j))

/-- Evaluating the auxiliary linear map family on a pure tensor is the product of the selected values. -/
@[simp]
lemma tensorLinearMapAux_tmul (i j : Fin 2) (v w : AuxiliaryType) :
    tensorLinearMapAux i j (v ⊗ₜ[ℚ] w) = v i * w j := by
  simp [tensorLinearMapAux]

/-- An auxiliary tensor in the tensor square of the auxiliary type. -/
noncomputable def tensorAux : AuxiliaryType ⊗[ℚ] AuxiliaryType :=
  auxiliaryFamily 0 ⊗ₜ[ℚ] auxiliaryFamily 0 +
    auxiliaryFamily 1 ⊗ₜ[ℚ] auxiliaryFamily 1

/-- Evaluating the auxiliary linear map family on the auxiliary tensor gives one for equal
indices and zero otherwise. -/
lemma tensorLinearMapAux_apply_tensorAux (i j : Fin 2) :
    tensorLinearMapAux i j tensorAux = if i = j then 1 else 0 := by
  simp only [tensorAux, map_add, tensorLinearMapAux_tmul, auxiliaryFamily,
    Pi.single_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The auxiliary tensor is unequal to every pure tensor. -/
@[source_ref "Chapter2/Discussion_pure_tensors" (role := primary)]
theorem tensorAux_ne_tmul (v w : AuxiliaryType) :
    tensorAux ≠ v ⊗ₜ[ℚ] w := by
  intro h
  have h00 : v 0 * w 0 = 1 := by
    have := congrArg (tensorLinearMapAux 0 0) h
    rw [tensorLinearMapAux_apply_tensorAux, tensorLinearMapAux_tmul,
      if_pos rfl] at this
    exact this.symm
  have h01 : v 0 * w 1 = 0 := by
    have := congrArg (tensorLinearMapAux 0 1) h
    rw [tensorLinearMapAux_apply_tensorAux, tensorLinearMapAux_tmul,
      if_neg (by decide)] at this
    exact this.symm
  have h11 : v 1 * w 1 = 1 := by
    have := congrArg (tensorLinearMapAux 1 1) h
    rw [tensorLinearMapAux_apply_tensorAux, tensorLinearMapAux_tmul,
      if_pos rfl] at this
    exact this.symm
  have hv0 : v 0 ≠ 0 := by
    intro hv
    rw [hv, zero_mul] at h00
    exact one_ne_zero h00.symm
  have hw1 : w 1 = 0 := by
    rcases mul_eq_zero.mp h01 with hv | hw
    · exact absurd hv hv0
    · exact hw
  rw [hw1, mul_zero] at h11
  exact one_ne_zero h11.symm

open scoped TensorProduct

/-- An auxiliary type depending on a module and two natural-number parameters. -/
@[source_ref "Chapter2/Discussion_pure_tensors" (role := supporting)]
abbrev moduleAuxiliaryType (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V]
    (m n : ℕ) : Type _ :=
  (⨂[k] (_ : Fin n), V) ⊗[k] (⨂[k] (_ : Fin m), Module.Dual k V)

/-- Constructs a basis indexed by pairs of finite functions from a basis of the underlying module. -/
@[source_ref "Chapter2/Discussion_tensors_type" (role := supporting)]
noncomputable def moduleAuxiliaryType_basis {k V ι : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Finite ι] (b : Module.Basis ι k V) (m n : ℕ) :
    Module.Basis ((Fin n → ι) × (Fin m → ι)) k (moduleAuxiliaryType k V m n) := by
  classical
  exact (Basis.piTensorProduct (fun _ : Fin n => b)).tensorProduct
    (Basis.piTensorProduct (fun _ : Fin m => b.dualBasis))

end RepresentationTheory.LinearAlgebra.TensorProductAuxiliary

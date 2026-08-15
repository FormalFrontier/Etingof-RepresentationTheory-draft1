/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import RepresentationTheory.Alignment.Attribute

/-! # Tensor-product auxiliary constructions -/

open scoped TensorProduct

namespace RepresentationTheory.LinearAlgebra.TensorProductAuxiliary

/-- An auxiliary type used with two rational coordinates. -/
abbrev TwoCoordinateSpaceAux : Type := Fin 2 → ℚ

/-- A selected two-element family in the auxiliary coordinate space. -/
noncomputable def coordinateVectorAux (i : Fin 2) : TwoCoordinateSpaceAux := Pi.single i 1

/-- A family of linear maps that extracts selected coordinate products from a tensor square. -/
noncomputable def tensorCoordinateLinearMap (i j : Fin 2) :
    (TwoCoordinateSpaceAux ⊗[ℚ] TwoCoordinateSpaceAux) →ₗ[ℚ] ℚ :=
  TensorProduct.lift (((LinearMap.mul ℚ ℚ).comp (LinearMap.proj i)).compl₂ (LinearMap.proj j))

/-- The coordinate linear map on a pure tensor is the product of the selected coordinates. -/
@[simp]
lemma tensorCoordinateLinearMap_tmul (i j : Fin 2) (v w : TwoCoordinateSpaceAux) :
    tensorCoordinateLinearMap i j (v ⊗ₜ[ℚ] w) = v i * w j := by
  simp [tensorCoordinateLinearMap]

/-- A selected tensor in the tensor square of the auxiliary rational coordinate space. -/
noncomputable def diagonalTensorAux : TwoCoordinateSpaceAux ⊗[ℚ] TwoCoordinateSpaceAux :=
  coordinateVectorAux 0 ⊗ₜ[ℚ] coordinateVectorAux 0 +
    coordinateVectorAux 1 ⊗ₜ[ℚ] coordinateVectorAux 1

/-- Evaluating the coordinate linear map on the selected tensor gives one on equal indices and
zero otherwise. -/
lemma tensorCoordinateLinearMap_diagonalTensorAux (i j : Fin 2) :
    tensorCoordinateLinearMap i j diagonalTensorAux = if i = j then 1 else 0 := by
  simp only [diagonalTensorAux, map_add, tensorCoordinateLinearMap_tmul, coordinateVectorAux,
    Pi.single_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The selected tensor is not equal to any pure tensor formed from two vectors. -/
@[source_ref "Chapter2/Discussion_pure_tensors" (role := primary)]
theorem diagonalTensorAux_ne_tmul (v w : TwoCoordinateSpaceAux) :
    diagonalTensorAux ≠ v ⊗ₜ[ℚ] w := by
  intro h
  have h00 : v 0 * w 0 = 1 := by
    have := congrArg (tensorCoordinateLinearMap 0 0) h
    rw [tensorCoordinateLinearMap_diagonalTensorAux, tensorCoordinateLinearMap_tmul,
      if_pos rfl] at this
    exact this.symm
  have h01 : v 0 * w 1 = 0 := by
    have := congrArg (tensorCoordinateLinearMap 0 1) h
    rw [tensorCoordinateLinearMap_diagonalTensorAux, tensorCoordinateLinearMap_tmul,
      if_neg (by decide)] at this
    exact this.symm
  have h11 : v 1 * w 1 = 1 := by
    have := congrArg (tensorCoordinateLinearMap 1 1) h
    rw [tensorCoordinateLinearMap_diagonalTensorAux, tensorCoordinateLinearMap_tmul,
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

/-- An auxiliary type depending on a module and two natural-number parameters. -/
@[source_ref "Chapter2/Discussion_pure_tensors" (role := supporting)]
abbrev PairedPowerSpaceAux (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V]
    (m n : ℕ) : Type _ :=
  (⨂[k] (_ : Fin n), V) ⊗[k] (⨂[k] (_ : Fin m), Module.Dual k V)

/-- Constructs a basis indexed by pairs of finite coordinate functions from a basis of the
underlying vector space. -/
@[source_ref "Chapter2/Discussion_tensors_type" (role := supporting)]
noncomputable def pairedPowerSpaceAux_basis {k V ι : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Finite ι] (b : Module.Basis ι k V) (m n : ℕ) :
    Module.Basis ((Fin n → ι) × (Fin m → ι)) k (PairedPowerSpaceAux k V m n) := by
  classical
  exact (Basis.piTensorProduct (fun _ : Fin n => b)).tensorProduct
    (Basis.piTensorProduct (fun _ : Fin m => b.dualBasis))

end RepresentationTheory.LinearAlgebra.TensorProductAuxiliary

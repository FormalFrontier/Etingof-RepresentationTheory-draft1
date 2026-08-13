/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.Alignment.Attribute

/-!
# Twice the Identity Minus a Matrix

This module defines the operation of subtracting a square integer matrix from twice the identity matrix.
-/

namespace RepresentationTheory.Matrix.TwoIdentitySub

open Matrix

/-- Returns twice the identity matrix minus the given square integer matrix. -/
@[source_ref "Chapter6/Problem6.1.3" (role := supporting)]
def twoIdentitySub {n : ℕ} (R : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  2 • (1 : Matrix (Fin n) (Fin n) ℤ) - R

/-- Expresses the transformed matrix as twice the identity matrix minus the original matrix. -/
theorem twoIdentitySub_eq_two_smul_one_sub {n : ℕ} (R : Matrix (Fin n) (Fin n) ℤ) :
    twoIdentitySub R = 2 • (1 : Matrix (Fin n) (Fin n) ℤ) - R := rfl

/-- Twice the identity minus a zero-diagonal integer matrix has every diagonal entry equal to two. -/
theorem twoIdentitySub_apply_self_of_apply_self_eq_zero {n : ℕ} {R : Matrix (Fin n) (Fin n) ℤ}
    (hloop : ∀ i, R i i = 0) (i : Fin n) : twoIdentitySub R i i = 2 := by
  rw [twoIdentitySub, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, hloop i]
  norm_num

/-- Subtracting a symmetric integer matrix from twice the identity matrix preserves symmetry. -/
theorem isSymm_twoIdentitySub {n : ℕ} {R : Matrix (Fin n) (Fin n) ℤ}
    (hR : R.IsSymm) : (twoIdentitySub R).IsSymm := by
  unfold Matrix.IsSymm twoIdentitySub
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hR.eq]

end RepresentationTheory.Matrix.TwoIdentitySub

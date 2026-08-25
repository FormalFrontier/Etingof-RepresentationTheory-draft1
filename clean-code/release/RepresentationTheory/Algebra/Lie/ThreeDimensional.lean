/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # A three-dimensional Lie algebra construction -/

namespace RepresentationTheory.Algebra.Lie.ThreeDimensional

open Matrix LieAlgebra

attribute [local instance] Cross.lieRing

/-- Lie algebra structure on three-dimensional real vectors associated with the cross product. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples" (role := primary)]
noncomputable local instance crossProductLieAlgebra : LieAlgebra ℝ (Fin 3 → ℝ) where
  lie_smul c x y := by
    change crossProduct x (c • y) = c • crossProduct x y
    rw [map_smul]

/-- The bracket on three-dimensional real vectors is their cross product. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples" (role := primary)]
theorem bracket_eq_crossProduct (u v : Fin 3 → ℝ) : ⁅u, v⁆ = u ⨯₃ v := rfl

/-- A three-by-three real matrix belongs to the orthogonal Lie subalgebra exactly when its transpose is its negative. -/
theorem mem_orthogonal_iff_transpose_eq_neg (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ Orthogonal.so (Fin 3) ℝ ↔ Aᵀ = -A :=
  Orthogonal.mem_so (n := Fin 3) (R := ℝ) A

/-- A matrix-valued map on three-dimensional real vectors. -/
def crossProductMatrix (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]

/-- The matrix associated with a vector belongs to the orthogonal Lie subalgebra. -/
theorem crossProductMatrix_mem_orthogonal (v : Fin 3 → ℝ) :
    crossProductMatrix v ∈ Orthogonal.so (Fin 3) ℝ := by
  rw [mem_orthogonal_iff_transpose_eq_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossProductMatrix]

/-- The matrix associated with a cross product is the commutator of the associated matrices. -/
theorem crossProductMatrix_bracket (u v : Fin 3 → ℝ) :
    crossProductMatrix (u ⨯₃ v) =
      crossProductMatrix u * crossProductMatrix v - crossProductMatrix v * crossProductMatrix u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossProductMatrix, cross_apply] <;> ring

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lie equivalence between three-dimensional real vectors and the orthogonal Lie subalgebra. -/
@[source_ref "Chapter2/Exercise2.9.5" (role := supporting)]
noncomputable def crossProductLieEquivOrthogonal :
    (Fin 3 → ℝ) ≃ₗ⁅ℝ⁆ Orthogonal.so (Fin 3) ℝ where
  toFun v := ⟨crossProductMatrix v, crossProductMatrix_mem_orthogonal v⟩
  map_add' u v := by
    apply Subtype.ext
    change crossProductMatrix (u + v) = crossProductMatrix u + crossProductMatrix v
    ext i j; fin_cases i <;> fin_cases j <;> simp [crossProductMatrix] <;> ring
  map_smul' c v := by
    apply Subtype.ext
    change crossProductMatrix (c • v) = c • crossProductMatrix v
    ext i j; fin_cases i <;> fin_cases j <;> simp [crossProductMatrix]
  map_lie' {u v} := by
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket]
    change crossProductMatrix ⁅u, v⁆ = ⁅crossProductMatrix u, crossProductMatrix v⁆
    rw [bracket_eq_crossProduct, Ring.lie_def, crossProductMatrix_bracket]
  invFun A := ![A.val 2 1, A.val 0 2, A.val 1 0]
  left_inv v := by
    funext i; fin_cases i <;> simp [crossProductMatrix]
  right_inv A := by
    apply Subtype.ext
    change crossProductMatrix ![A.val 2 1, A.val 0 2, A.val 1 0] = A.val
    have hA : (A.val)ᵀ = -A.val :=
      (mem_orthogonal_iff_transpose_eq_neg A.val).1 A.property
    have h : ∀ i j, A.val j i = -A.val i j := fun i j => by
      have := congrFun (congrFun hA i) j
      simpa [Matrix.transpose_apply, Matrix.neg_apply] using this
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [crossProductMatrix] <;>
      linarith [h 0 0, h 0 1, h 0 2, h 1 0, h 1 1, h 1 2, h 2 0, h 2 1, h 2 2]

/-- There exists a Lie equivalence from the orthogonal Lie subalgebra to three-dimensional real vectors. -/
@[source_ref "Chapter2/Exercise2.9.5" (role := supporting)]
theorem orthogonalLieEquiv_nonempty :
    Nonempty (Orthogonal.so (Fin 3) ℝ ≃ₗ⁅ℝ⁆ (Fin 3 → ℝ)) :=
  ⟨crossProductLieEquivOrthogonal.symm⟩

end RepresentationTheory.Algebra.Lie.ThreeDimensional

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.Algebra.Lie.ThreeDimensional
import RepresentationTheory.LieAlgebra.SpecialLinearPresentation
import RepresentationTheory.LieAlgebra.ThreeGeneratorPresentations

/-! # Auxiliary three-by-three matrix Lie algebra constructions -/

namespace RepresentationTheory.LieAlgebra.ThreeByThreeMatrixAuxiliary

open scoped Matrix
open RepresentationTheory.LieAlgebra.ThreeGeneratorPresentations

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [CommRing k]

/-- A selected Lie subalgebra of three-by-three matrices over a commutative ring. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples" (role := supporting)]
def matrixLieSubalgebraAux : LieSubalgebra k (Matrix (Fin 3) (Fin 3) k) where
  carrier := {A | ∃ a b d : k, A = !![0, b, d; 0, 0, a; 0, 0, 0]}
  zero_mem' := ⟨0, 0, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  add_mem' := by
    rintro A B ⟨a, b, d, rfl⟩ ⟨a', b', d', rfl⟩
    refine ⟨a + a', b + b', d + d', ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  smul_mem' := by
    rintro t A ⟨a, b, d, rfl⟩
    refine ⟨t * a, t * b, t * d, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul]
  lie_mem' := by
    rintro A B ⟨a, b, d, rfl⟩ ⟨a', b', d', rfl⟩
    refine ⟨0, 0, b * a' - b' * a, ?_⟩
    rw [LieRing.of_associative_ring_bracket]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- An auxiliary map from the displayed Lie algebra to three-by-three matrices. -/
def toMatrixAux (u : AuxiliaryType k) : Matrix (Fin 3) (Fin 3) k :=
  !![0, u.2.1, u.2.2; 0, 0, u.1; 0, 0, 0]

/-- The matrix produced by the auxiliary map belongs to the selected matrix Lie subalgebra. -/
theorem toMatrixAux_mem_matrixLieSubalgebraAux (u : AuxiliaryType k) :
    toMatrixAux k u ∈ matrixLieSubalgebraAux k :=
  ⟨u.1, u.2.1, u.2.2, rfl⟩

/-- An auxiliary Lie equivalence from the displayed Lie algebra to the selected matrix Lie subalgebra. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples" (role := supporting)]
noncomputable def matrixLieEquivAux :
    AuxiliaryType k ≃ₗ⁅k⁆ matrixLieSubalgebraAux k where
  toFun u := ⟨toMatrixAux k u, toMatrixAux_mem_matrixLieSubalgebraAux k u⟩
  map_add' u v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrixAux]
  map_smul' t u := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrixAux]
  map_lie' {u v} := by
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrixAux, bracket_eq]
    ring
  invFun A := (A.val 1 2, A.val 0 1, A.val 0 2)
  left_inv u := by
    apply AuxiliaryType.ext <;> simp [toMatrixAux]
  right_inv A := by
    rcases A.property with ⟨a, b, d, hA⟩
    apply Subtype.ext
    change toMatrixAux k (A.val 1 2, A.val 0 1, A.val 0 2) = A.val
    simp_rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrixAux]

/-- On the specified element, the auxiliary Lie equivalence has value equal to the matrix unit in row one and column two. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples" (role := primary), simp]
theorem matrixLieEquivAux_apply_eq_single_12 :
    ((matrixLieEquivAux k
        (distinguishedElement_aux5 : AuxiliaryType k) : matrixLieSubalgebraAux k) :
      Matrix (Fin 3) (Fin 3) k) = Matrix.single 1 2 1 := by
  change toMatrixAux k (distinguishedElement_aux5 : AuxiliaryType k) = Matrix.single 1 2 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrixAux, distinguishedElement_aux5]

/-- On the specified element, the auxiliary Lie equivalence has value equal to the matrix unit in row zero and column one. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples" (role := primary), simp]
theorem matrixLieEquivAux_apply_eq_single_01 :
    ((matrixLieEquivAux k
        (distinguishedElement_aux6 : AuxiliaryType k) : matrixLieSubalgebraAux k) :
      Matrix (Fin 3) (Fin 3) k) = Matrix.single 0 1 1 := by
  change toMatrixAux k (distinguishedElement_aux6 : AuxiliaryType k) = Matrix.single 0 1 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrixAux, distinguishedElement_aux6]

/-- On the specified element, the auxiliary Lie equivalence has value equal to the matrix unit in row zero and column two. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples" (role := primary), simp]
theorem matrixLieEquivAux_apply_eq_single_02 :
    ((matrixLieEquivAux k
        (distinguishedElement_aux2 : AuxiliaryType k) : matrixLieSubalgebraAux k) :
      Matrix (Fin 3) (Fin 3) k) = Matrix.single 0 2 1 := by
  change toMatrixAux k (distinguishedElement_aux2 : AuxiliaryType k) = Matrix.single 0 2 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrixAux, distinguishedElement_aux2]

end RepresentationTheory.LieAlgebra.ThreeByThreeMatrixAuxiliary

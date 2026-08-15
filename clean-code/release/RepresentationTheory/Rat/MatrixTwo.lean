/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.RingTheory.Morita.Matrix
import RepresentationTheory.CategoryTheory.LinearAlgebra.Auxiliary
import RepresentationTheory.Alignment.Attribute

/-!
# Rational modules and two-by-two matrix modules

The rational module category is equivalent to the module category of two-by-two rational matrices,
although the corresponding rings are not equivalent.
-/

open CategoryTheory

namespace RepresentationTheory.Rat.MatrixTwo

/-- Rational modules and modules over two-by-two rational matrices form equivalent categories. -/
theorem rat_moduleCat_equivalence_matrix_fin_two :
    Nonempty (ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ)) :=
  ⟨ModuleCat.matrixEquivalence ℚ (0 : Fin 2)⟩

/-- There is no ring equivalence from the rationals to two-by-two rational matrices. -/
theorem rat_matrix_fin_two_ringEquiv_isEmpty :
    IsEmpty (ℚ ≃+* Matrix (Fin 2) (Fin 2) ℚ) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨x, y, hxy⟩ :=
    RepresentationTheory.CategoryTheory.LinearAlgebra.Auxiliary.exists_noncommuting_elements_of_ne
      (k := ℚ) (m := Fin 2) (a := 0) (b := 1) (by decide)
  refine hxy ?_
  -- A ring equivalence transports commutativity of `ℚ` to `Matrix (Fin 2) (Fin 2) ℚ`.
  have ha : f (f.symm x) = x := f.apply_symm_apply x
  have hb : f (f.symm y) = y := f.apply_symm_apply y
  calc
    x * y = f (f.symm x) * f (f.symm y) := by rw [ha, hb]
    _ = f (f.symm x * f.symm y) := (f.map_mul _ _).symm
    _ = f (f.symm y * f.symm x) := by rw [mul_comm]
    _ = f (f.symm y) * f (f.symm x) := f.map_mul _ _
    _ = y * x := by rw [ha, hb]

/-- The rational module categories are equivalent, while the corresponding rings admit no equivalence. -/
@[source_ref "Chapter7/Remark7.7.4" (role := primary)]
theorem rat_moduleCat_equivalence_matrix_fin_two_and_ringEquiv_isEmpty :
    Nonempty (ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ)) ∧
      IsEmpty (ℚ ≃+* Matrix (Fin 2) (Fin 2) ℚ) :=
  ⟨rat_moduleCat_equivalence_matrix_fin_two, rat_matrix_fin_two_ringEquiv_isEmpty⟩

end RepresentationTheory.Rat.MatrixTwo

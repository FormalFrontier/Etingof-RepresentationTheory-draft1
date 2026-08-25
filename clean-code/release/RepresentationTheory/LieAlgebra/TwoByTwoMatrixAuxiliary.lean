/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.LieAlgebra.ModularRepresentations
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary two-by-two matrix Lie algebra constructions -/

namespace RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary

open scoped Matrix
open Module
open RepresentationTheory.LieAlgebra.ModularRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type) [Field k]

/-- A selected Lie subalgebra of two-by-two matrices over a field. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples_continued" (role := supporting)]
noncomputable abbrev matrixLieSubalgebraAux :
    LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  matrixLieSubalgebra k

/-- An element of the matrix subalgebra equals the linear combination of two matrix units given by
its first-row entries. -/
theorem matrix_eq_linearCombination_entries (z : matrixLieSubalgebra k) :
    (z : Matrix (Fin 2) (Fin 2) k)
      = (z : Matrix (Fin 2) (Fin 2) k) 0 0 • Matrix.single 0 0 1
        + (z : Matrix (Fin 2) (Fin 2) k) 0 1 • Matrix.single 0 1 1 := by
  obtain ⟨h10, h11⟩ := property_and k z
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, h10, h11]

/-- The displayed vector of two matrices is linearly independent. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples_continued" (role := supporting)]
theorem twoElementVector_linearIndependent :
    LinearIndependent k ![distinguishedElement k, distinguishedElement_aux1 k] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcoe : c 0 • Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k)
      + c 1 • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k) = 0 := by
    have h2 : ((∑ j, c j • (![distinguishedElement k, distinguishedElement_aux1 k] j) :
        matrixLieSubalgebra k) : Matrix (Fin 2) (Fin 2) k)
        = ((0 : matrixLieSubalgebra k) : Matrix (Fin 2) (Fin 2) k) := congrArg _ hc
    rw [Fin.sum_univ_two] at h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    push_cast at h2
    rw [matrixSingle_eq, matrixSingle_eq_aux1] at h2
    simpa using h2
  fin_cases i
  · have h00 := congrFun (congrFun hcoe 0) 0
    simpa [Matrix.single_apply, Matrix.add_apply, Matrix.smul_apply] using h00
  · have h01 := congrFun (congrFun hcoe 0) 1
    simpa [Matrix.single_apply, Matrix.add_apply, Matrix.smul_apply] using h01

/-- The displayed two-element vector spans the ambient module. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples_continued" (role := supporting)]
theorem twoElementVector_span_eq_top :
    Submodule.span k (Set.range ![distinguishedElement k, distinguishedElement_aux1 k]) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hz : z = (z : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement k
      + (z : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux1 k := by
    apply Subtype.ext
    push_cast
    rw [matrixSingle_eq, matrixSingle_eq_aux1]
    exact matrix_eq_linearCombination_entries k z
  rw [hz]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩

/-- An auxiliary basis indexed by two elements for the displayed matrix Lie subalgebra. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples_continued" (role := supporting)]
noncomputable def subalgebraBasisAux : Basis (Fin 2) k (matrixLieSubalgebra k) :=
  Basis.mk (twoElementVector_linearIndependent k)
    (le_of_eq (twoElementVector_span_eq_top k).symm)

/-- Each basis index selects the corresponding entry of the displayed two-element vector. -/
@[simp] theorem subalgebraBasisAux_apply (i : Fin 2) :
    subalgebraBasisAux k i = ![distinguishedElement k, distinguishedElement_aux1 k] i :=
  Basis.mk_apply _ _ i

/-- The displayed matrix subalgebra has dimension two over its field. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples_continued" (role := supporting)]
theorem finrank_eq_two : Module.finrank k (matrixLieSubalgebra k) = 2 := by
  rw [Module.finrank_eq_card_basis (subalgebraBasisAux k), Fintype.card_fin]

/-- The two displayed matrix Lie subalgebras are equal. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples_continued" (role := supporting)]
theorem matrixLieSubalgebrasAux_eq :
    matrixLieSubalgebra k = matrixLieSubalgebra_aux1 k := by
  refine le_antisymm ?_ ?_
  · intro z hz
    exact property_and k ⟨z, hz⟩
  · intro A hA
    obtain ⟨h10, h11⟩ := hA
    have hA_eq : A = A 0 0 • Matrix.single 0 0 1 + A 0 1 • Matrix.single 0 1 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, h10, h11]
    rw [hA_eq]
    refine (matrixLieSubalgebra k).toSubmodule.add_mem
      ((matrixLieSubalgebra k).toSubmodule.smul_mem _ ?_)
      ((matrixLieSubalgebra k).toSubmodule.smul_mem _ ?_)
    · exact LieSubalgebra.subset_lieSpan (by left; rfl)
    · exact LieSubalgebra.subset_lieSpan (by right; rfl)

end RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary

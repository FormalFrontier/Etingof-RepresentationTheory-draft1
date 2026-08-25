/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryIntegerMatrixProperty
import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty
import RepresentationTheory.IntegerMatrixVectorPredicates
import RepresentationTheory.AuxiliaryIntegerVectorTransforms
import RepresentationTheory.LinearAlgebra.IntegerMatrixReflections

section BilinearFormPreservation

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

/-- For a symmetric integer matrix, the displayed map associated with a vector of quadratic value two preserves the quadratic form. -/
theorem RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_vector_map_preserves_quadratic_form
    (hA : A.IsSymm)
    (α : Fin n → ℤ) (hα : dotProduct α (A.mulVec α) = 2)
    (v : Fin n → ℤ) :
    dotProduct (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v)
      (A.mulVec (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A α v)) =
    dotProduct v (A.mulVec v) := by
  unfold RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform
  set c := dotProduct v (A.mulVec α) with hc_def
  have hsymm : dotProduct α (A.mulVec v) = c := by
    rw [Matrix.dotProduct_mulVec, ← hA.eq, Matrix.vecMul_transpose, dotProduct_comm]
  have h1 : A.mulVec (v - c • α) = A.mulVec v - c • A.mulVec α := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [h1]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hsymm, hα]
  ring

/-- For a symmetric integer matrix whose selected coordinate vector has quadratic value two, the corresponding displayed map preserves the quadratic form. -/
theorem RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_index_map_preserves_quadratic_form
    (hA : A.IsSymm)
    (i : Fin n)
    (hroot : dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2)
    (v : Fin n → ℤ) :
    dotProduct (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v)
      (A.mulVec (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i v)) =
    dotProduct v (A.mulVec v) :=
  RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_vector_map_preserves_quadratic_form A hA _ hroot v

/-- For a symmetric integer matrix with the stated diagonal values, the displayed map indexed by a finite list preserves the associated quadratic form. -/
theorem RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_list_map_preserves_quadratic_form
    (hA : A.IsSymm)
    (hroots : ∀ i : Fin n, dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) = 2)
    (vertices : List (Fin n)) (v : Fin n → ℤ) :
    dotProduct (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vertices v)
      (A.mulVec (RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n A vertices v)) =
    dotProduct v (A.mulVec v) := by
  unfold RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection
  induction vertices generalizing v with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_index_map_preserves_quadratic_form A hA j (hroots j)]

end BilinearFormPreservation

section Corollary

/-- Under the displayed matrix hypothesis, a nonzero nonnegative integer vector has the auxiliary property whenever the stated existential equality holds. -/
theorem RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_property_of_exists_eq
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj)
    (d : Fin n → ℤ)
    (hd_pos : ∀ i, 0 ≤ d i)
    (hd_nonzero : d ≠ 0)
    (hreflect : ∃ (vertices : List (Fin n)) (p : Fin n),
      RepresentationTheory.LinearAlgebra.IntegerMatrixReflections.iteratedCoordinateReflection n (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) vertices d =
        RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue n p) :
    RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition n adj d := by
  obtain ⟨vertices, p, hrefl⟩ := hreflect
  refine ⟨⟨hd_nonzero, ?_⟩, hd_pos⟩

  change dotProduct d ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec d) = 2

  have hA_symm : (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).IsSymm := by
    unfold RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform
    rw [Matrix.IsSymm]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    rw [hDynkin.1.eq]
  have hroots : ∀ i : Fin n,
      dotProduct (Pi.single i 1)
        ((RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj).mulVec (Pi.single i 1)) = 2 := by
    intro i
    unfold RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform
    simp only [Matrix.sub_mulVec]
    simp only [dotProduct_sub]
    have hsmul : (2 • (1 : Matrix (Fin n) (Fin n) ℤ)).mulVec (Pi.single i 1) =
        2 • Pi.single i 1 := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hdot1 : dotProduct (Pi.single i (1 : ℤ)) (2 • Pi.single i (1 : ℤ)) = 2 := by
      simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    have hadj : dotProduct (Pi.single i (1 : ℤ)) (adj.mulVec (Pi.single i 1)) = adj i i := by
      simp [dotProduct, Pi.single_apply, Matrix.mulVec, Finset.sum_ite_eq', Finset.mem_univ]
    rw [hsmul, hdot1, hadj, hDynkin.2.1 i]
    ring
  have h := RepresentationTheory.AuxiliaryIntegralQuadraticFormMaps.auxiliary_list_map_preserves_quadratic_form
    (RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj) hA_symm hroots vertices d
  rw [hrefl] at h
  simp only [RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue] at h
  rw [hroots p] at h
  linarith

end Corollary

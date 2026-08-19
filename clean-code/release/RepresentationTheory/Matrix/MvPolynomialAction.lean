/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Matrix.MvPolynomialRightMul

namespace RepresentationTheory.Matrix.MvPolynomialAction.Matrix

set_option linter.dupNamespace false

open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The algebra endomorphism of the matrix-coordinate polynomial ring that sends the coordinate
matrix to the transpose of a given matrix times the coordinate matrix. -/
noncomputable def transposeMulMvPolynomialAlgHom (M : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval
    (fun ij : Fin N × Fin N =>
      ∑ l : Fin N, M l ij.1 • MvPolynomial.X (l, ij.2))

/-- The transpose-multiplication algebra homomorphism sends the coordinate indexed by `(i, j)`
to the sum of `M (l, i)` times the coordinates indexed by `(l, j)`. -/
@[simp] theorem transposeMulMvPolynomialAlgHom_X
    (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    transposeMulMvPolynomialAlgHom M (MvPolynomial.X (i, j)) =
      ∑ l, M l i • MvPolynomial.X (l, j) := by
  simp [transposeMulMvPolynomialAlgHom]

/-- The polynomial algebra homomorphism associated with the identity matrix is the identity. -/
theorem transposeMulMvPolynomialAlgHom_one :
    transposeMulMvPolynomialAlgHom (1 : Matrix (Fin N) (Fin N) k) =
      AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [transposeMulMvPolynomialAlgHom_X]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, AlgHom.id_apply]
  rw [Finset.sum_ite_eq' Finset.univ i (fun l => MvPolynomial.X (l, j))]
  simp

/-- The polynomial algebra homomorphism associated with a product of matrices is the composition
of the associated homomorphisms. -/
theorem transposeMulMvPolynomialAlgHom_mul (M₁ M₂ : Matrix (Fin N) (Fin N) k) :
    transposeMulMvPolynomialAlgHom (M₁ * M₂) =
      (transposeMulMvPolynomialAlgHom M₁).comp
        (transposeMulMvPolynomialAlgHom M₂) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, transposeMulMvPolynomialAlgHom_X,
    transposeMulMvPolynomialAlgHom_X, map_sum]
  simp_rw [map_smul, transposeMulMvPolynomialAlgHom_X, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm]

/-- The representation of the general linear group on the matrix-coordinate polynomial ring
whose action uses the transpose coefficients of the underlying matrix. -/
noncomputable def GeneralLinearGroup.transposeMulMvPolynomialRepresentation
    (k : Type*) [CommRing k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k) where
  toFun g :=
    (transposeMulMvPolynomialAlgHom
      (g : Matrix (Fin N) (Fin N) k)).toLinearMap
  map_one' := by
    change (transposeMulMvPolynomialAlgHom
      ((1 : Matrix.GeneralLinearGroup (Fin N) k) :
        Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_one, transposeMulMvPolynomialAlgHom_one]
    rfl
  map_mul' g₁ g₂ := by
    change (transposeMulMvPolynomialAlgHom
      ((g₁ * g₂ : Matrix.GeneralLinearGroup (Fin N) k) :
        Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_mul, transposeMulMvPolynomialAlgHom_mul]
    rfl

/-- An invertible matrix sends the coordinate indexed by `(i, j)` to the sum of its entries at
`(l, i)` times the coordinates indexed by `(l, j)`. -/
@[simp] theorem GeneralLinearGroup.transposeMulMvPolynomialRepresentation_apply_X
    (g : Matrix.GeneralLinearGroup (Fin N) k) (i j : Fin N) :
    GeneralLinearGroup.transposeMulMvPolynomialRepresentation k N g
        (MvPolynomial.X (i, j)) =
      ∑ l, (g : Matrix (Fin N) (Fin N) k) l i • MvPolynomial.X (l, j) :=
  transposeMulMvPolynomialAlgHom_X _ i j

/-- The action of an invertible matrix in the representation is the algebra homomorphism
associated with its underlying matrix. -/
theorem GeneralLinearGroup.transposeMulMvPolynomialRepresentation_apply
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (f : MvPolynomial (Fin N × Fin N) k) :
    GeneralLinearGroup.transposeMulMvPolynomialRepresentation k N g f =
      transposeMulMvPolynomialAlgHom (↑g) f :=
  rfl

/-- The transpose-multiplication polynomial algebra homomorphism commutes under composition with
an auxiliary algebra homomorphism. -/
theorem transposeMulMvPolynomialAlgHom_commute_auxiliary
    (M₁ M₂ : Matrix (Fin N) (Fin N) k) :
    (transposeMulMvPolynomialAlgHom M₁).comp (mvPolynomialRightMul M₂) =
      (mvPolynomialRightMul M₂).comp (transposeMulMvPolynomialAlgHom M₁) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, AlgHom.comp_apply, mvPolynomialRightMul_apply_X,
    transposeMulMvPolynomialAlgHom_X, map_sum, map_sum]
  simp_rw [map_smul, transposeMulMvPolynomialAlgHom_X,
    mvPolynomialRightMul_apply_X, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

/-- Each endofunction arising from the transpose-coefficient action commutes with the auxiliary
endofunction associated with another invertible matrix. -/
theorem GeneralLinearGroup.transposeMulMvPolynomialRepresentation_commute_auxiliary
    (g h : Matrix.GeneralLinearGroup (Fin N) k) :
    Commute (GeneralLinearGroup.transposeMulMvPolynomialRepresentation k N g)
      (generalLinearGroupMvPolynomialRightMul k N h) := by
  have key :
      GeneralLinearGroup.transposeMulMvPolynomialRepresentation k N g *
          generalLinearGroupMvPolynomialRightMul k N h =
        generalLinearGroupMvPolynomialRightMul k N h *
          GeneralLinearGroup.transposeMulMvPolynomialRepresentation k N g := by
    apply LinearMap.ext
    intro f
    rw [Module.End.mul_apply, Module.End.mul_apply,
      GeneralLinearGroup.transposeMulMvPolynomialRepresentation_apply,
      generalLinearGroupMvPolynomialRightMul_apply,
      generalLinearGroupMvPolynomialRightMul_apply,
      GeneralLinearGroup.transposeMulMvPolynomialRepresentation_apply]
    have h2 := AlgHom.congr_fun
      (transposeMulMvPolynomialAlgHom_commute_auxiliary (↑g) (↑h)) f
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at h2
    exact h2
  exact key

/-- Applying the transpose-multiplication polynomial algebra homomorphism entrywise to the
coordinate matrix yields the coefficientwise constant image of the transposed matrix times the
coordinate matrix. -/
theorem transposeMulMvPolynomialAlgHom_map_mvPolynomialX
    (M : Matrix (Fin N) (Fin N) k) :
    (transposeMulMvPolynomialAlgHom M).mapMatrix
        (Matrix.mvPolynomialX (Fin N) (Fin N) k) =
      (Matrix.transpose M).map
          (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k) *
        Matrix.mvPolynomialX (Fin N) (Fin N) k := by
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX,
    Matrix.of_apply, transposeMulMvPolynomialAlgHom_X, Matrix.mul_apply,
    MvPolynomial.smul_eq_C_mul, Matrix.transpose_apply]

/--
The transpose-multiplication polynomial algebra homomorphism maps the determinant of the
coordinate matrix to the product of the constant polynomial associated with the matrix
determinant and the coordinate-matrix determinant.
-/
theorem transposeMulMvPolynomialAlgHom_det_mvPolynomialX
    (M : Matrix (Fin N) (Fin N) k) :
    transposeMulMvPolynomialAlgHom M
        (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)) =
      MvPolynomial.C M.det *
        Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k) := by
  have hmap :
      ((Matrix.transpose M).map
        (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)).det =
          MvPolynomial.C M.det := by
    rw [← Matrix.det_transpose M]
    exact (RingHom.map_det _ _).symm
  rw [AlgHom.map_det, transposeMulMvPolynomialAlgHom_map_mvPolynomialX,
    Matrix.det_mul, hmap]

/-- The transpose-multiplication polynomial algebra homomorphism preserves membership in the
ideal generated by the determinant of the coordinate matrix. -/
theorem transposeMulMvPolynomialAlgHom_mem_span_det_mvPolynomialX
    (M : Matrix (Fin N) (Fin N) k) {f : MvPolynomial (Fin N × Fin N) k}
    (hf : f ∈ Ideal.span
      {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)}) :
    transposeMulMvPolynomialAlgHom M f ∈
      Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)} := by
  rw [Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, transposeMulMvPolynomialAlgHom_det_mvPolynomialX]
  exact ⟨MvPolynomial.C M.det * transposeMulMvPolynomialAlgHom M q, by ring⟩

end RepresentationTheory.Matrix.MvPolynomialAction.Matrix

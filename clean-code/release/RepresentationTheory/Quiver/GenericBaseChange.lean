/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.Representation.MatrixModel
import Mathlib

/-! # Generic base change -/

open Matrix MvPolynomial

namespace RepresentationTheory.Quiver.GenericBaseChange

variable {k : Type} [Field k] {n : ℕ}

/-- The finite index type for entries of one square matrix of size `m i` at every vertex `i`. -/
abbrev VertexMatrixIndex (m : Fin n → ℕ) : Type := Σ i : Fin n, Fin (m i) × Fin (m i)

/-- The finite index type for matrix entries attached to the arrows of a finite quiver with dimension vector `m`. -/
abbrev ArrowMatrixIndex [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]
    (m : Fin n → ℕ) : Type :=
  Σ i : Fin n, Σ j : Fin n, (i ⟶ j) × (Fin (m j) × Fin (m i))

/-- The cardinality of the vertex-coordinate index equals the sum over vertices of each dimension multiplied by itself. -/
theorem card_vertexMatrixIndex (m : Fin n → ℕ) :
    Fintype.card (VertexMatrixIndex m) = ∑ i : Fin n, (m i) ^ 2 := by
  simp only [VertexMatrixIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_congr rfl fun i _ => (pow_two (m i)).symm

/-- The number of arrow-matrix coordinates is the sum, over ordered vertex pairs, of the arrow count times the two vertex dimensions. -/
theorem card_arrowMatrixIndex [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]
    (m : Fin n → ℕ) :
    Fintype.card (ArrowMatrixIndex m) =
      ∑ i : Fin n, ∑ j : Fin n,
        RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount i j * (m i * m j) := by
  simp only [ArrowMatrixIndex]
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    RepresentationTheory.Quiver.Representation.MatrixModel.arrowCount,
    mul_comm (m j) (m i)]

/-- The square matrix at a vertex whose entries are the corresponding coordinate variables in the multivariable polynomial ring. -/
noncomputable def genericVertexMatrix (m : Fin n → ℕ) (i : Fin n) :
    Matrix (Fin (m i)) (Fin (m i)) (MvPolynomial (VertexMatrixIndex m) k) :=
  fun a b => X ⟨i, (a, b)⟩

/-- The product of the determinants of the generic square matrices associated with the vertices of a dimension vector. -/
noncomputable def genericVertexDeterminantProduct (m : Fin n → ℕ) :
    MvPolynomial (VertexMatrixIndex m) k :=
  ∏ i : Fin n, (genericVertexMatrix (k := k) m i).det

/-- The polynomial evaluation homomorphism that specializes every generic vertex matrix to the corresponding identity matrix. -/
noncomputable def evalGenericVertexMatricesAtIdentity (m : Fin n → ℕ) :
    MvPolynomial (VertexMatrixIndex m) k →ₐ[k] k :=
  aeval (fun w : VertexMatrixIndex m => if w.2.1 = w.2.2 then (1 : k) else 0)

/-- Entrywise identity specialization sends each generic vertex matrix to the identity matrix. -/
theorem evalGenericVertexMatricesAtIdentity_genericVertexMatrix
    (m : Fin n → ℕ) (i : Fin n) :
    (evalGenericVertexMatricesAtIdentity m).mapMatrix (genericVertexMatrix (k := k) m i) = 1 := by
  ext a b
  simp [genericVertexMatrix, evalGenericVertexMatricesAtIdentity, AlgHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.one_apply]

/-- Specializing all generic vertex matrices to identity sends their determinant product to one. -/
theorem evalGenericVertexMatricesAtIdentity_genericVertexDeterminantProduct (m : Fin n → ℕ) :
    evalGenericVertexMatricesAtIdentity m (genericVertexDeterminantProduct (k := k) m) = 1 := by
  rw [genericVertexDeterminantProduct, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [AlgHom.map_det, evalGenericVertexMatricesAtIdentity_genericVertexMatrix, Matrix.det_one]

/-- The product of the generic vertex-matrix determinants is a nonzero polynomial over any field. -/
theorem genericVertexDeterminantProduct_ne_zero (m : Fin n → ℕ) :
    genericVertexDeterminantProduct (k := k) m ≠
      (0 : MvPolynomial (VertexMatrixIndex m) k) := by
  intro h
  have h1 := evalGenericVertexMatricesAtIdentity_genericVertexDeterminantProduct (k := k) m
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

section Comorphism

variable (m : Fin n → ℕ)
variable {B : Type} [CommRing B]
  [Algebra (MvPolynomial (VertexMatrixIndex m) k) B]
  [IsLocalization (Submonoid.powers (genericVertexDeterminantProduct (k := k) m)) B]

/-- The generic square matrix at a vertex after transporting its polynomial entries into a commutative algebra. -/
noncomputable def mappedGenericVertexMatrix (i : Fin n) : Matrix (Fin (m i)) (Fin (m i)) B :=
  (genericVertexMatrix (k := k) m i).map
    (algebraMap (MvPolynomial (VertexMatrixIndex m) k) B)

/-- The determinant of every mapped generic vertex matrix is a unit in the localization at the common determinant product. -/
theorem isUnit_det_mappedGenericVertexMatrix (i : Fin n) :
    IsUnit ((mappedGenericVertexMatrix (k := k) (B := B) m i).det) := by
  have hmap : (mappedGenericVertexMatrix (k := k) (B := B) m i).det =
      algebraMap (MvPolynomial (VertexMatrixIndex m) k) B
        ((genericVertexMatrix (k := k) m i).det) := by
    unfold mappedGenericVertexMatrix
    exact (RingHom.map_det _ _).symm
  rw [hmap]
  have hdvd : (genericVertexMatrix (k := k) m i).det ∣
      genericVertexDeterminantProduct (k := k) m :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hunit : IsUnit (algebraMap (MvPolynomial (VertexMatrixIndex m) k) B
      (genericVertexDeterminantProduct (k := k) m)) :=
    IsLocalization.map_units B
      ⟨genericVertexDeterminantProduct (k := k) m, Submonoid.mem_powers _⟩
  exact isUnit_of_dvd_unit (map_dvd _ hdvd) hunit

/-- The inverse candidate for a mapped generic vertex matrix, which is an actual inverse after localizing at the determinant product. -/
noncomputable def mappedGenericVertexMatrixInv (i : Fin n) :
    Matrix (Fin (m i)) (Fin (m i)) B :=
  (mappedGenericVertexMatrix (k := k) (B := B) m i)⁻¹

/-- In the localization at the generic determinant product, a mapped generic vertex matrix multiplied by its inverse is the identity matrix. -/
theorem mappedGenericVertexMatrix_mul_inv (i : Fin n) :
    mappedGenericVertexMatrix (k := k) (B := B) m i *
      mappedGenericVertexMatrixInv (k := k) (B := B) m i = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_mappedGenericVertexMatrix m i)

variable [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] [Algebra k B]
  [IsScalarTower k (MvPolynomial (VertexMatrixIndex m) k) B]

/-- The algebra homomorphism that evaluates arrow-matrix coordinates after applying the generic vertexwise change of basis to a given family of arrow matrices. -/
noncomputable def genericBaseChangeAlgHom
    (v₀ : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m) :
    MvPolynomial (ArrowMatrixIndex m) k →ₐ[k] B :=
  aeval (fun w : ArrowMatrixIndex m =>
    (mappedGenericVertexMatrix (k := k) (B := B) m w.2.1 *
        (v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k B) *
        mappedGenericVertexMatrixInv (k := k) (B := B) m w.1) w.2.2.2.1 w.2.2.2.2)

omit [IsScalarTower k (MvPolynomial (VertexMatrixIndex m) k) B]
  [IsLocalization (Submonoid.powers (genericVertexDeterminantProduct (k := k) m)) B] in
/-- On an arrow-coordinate variable, generic base change gives the corresponding entry of the target generic matrix times the arrow matrix times the inverse source generic matrix. -/
@[simp]
theorem genericBaseChangeAlgHom_apply_X
    (v₀ : RepresentationTheory.Quiver.Representation.MatrixModel.MatrixData (k := k) m)
    (w : ArrowMatrixIndex m) :
    genericBaseChangeAlgHom (B := B) m v₀ (X w) =
      (mappedGenericVertexMatrix (k := k) (B := B) m w.2.1 *
          (v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k B) *
          mappedGenericVertexMatrixInv (k := k) (B := B) m w.1)
        w.2.2.2.1 w.2.2.2.2 := by
  rw [genericBaseChangeAlgHom, aeval_X]

end Comorphism

end RepresentationTheory.Quiver.GenericBaseChange

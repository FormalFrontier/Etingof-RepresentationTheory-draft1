/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.Quiver.Finite
import Mathlib

namespace RepresentationTheory.Quiver.Representation.MatrixModel

open Matrix

universe u

variable {k : Type u} [Field k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- Collections of matrices assigned to the arrows of a quiver, with sizes prescribed by a dimension vector. -/
abbrev MatrixData (m : Fin n → ℕ) : Type u :=
  ∀ i j : Fin n, (i ⟶ j) → Matrix (Fin (m j)) (Fin (m i)) k

/-- The product of the general linear groups at the vertices for a prescribed dimension vector. -/
abbrev BaseChangeGroup (k : Type u) [Field k] {n : ℕ} (m : Fin n → ℕ) : Type u :=
  ∀ i : Fin n, GL (Fin (m i)) k

/-- The number of arrows from one vertex to another in a finite quiver. -/
def arrowCount [∀ i j : Fin n, Fintype (i ⟶ j)] (i j : Fin n) : ℕ := Fintype.card (i ⟶ j)

/-- The dimension of the arrow-matrix data is the sum over ordered vertex pairs of the arrow count times the product of the two vertex dimensions. -/
theorem finrank_matrixData [∀ i j : Fin n, Fintype (i ⟶ j)] (m : Fin n → ℕ) :
    Module.finrank k (MatrixData (k := k) m) =
      ∑ i : Fin n, ∑ j : Fin n, arrowCount i j * (m i * m j) := by
  classical
  rw [Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Module.finrank_pi_fintype k]
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, arrowCount, Fintype.card_fin]
  ring

omit [Quiver.{0} (Fin n)] in

/-- The space of vertex-indexed square matrices has dimension equal to the sum of the squared vertex dimensions. -/
theorem finrank_vertexMatrixFamily (m : Fin n → ℕ) :
    Module.finrank k (∀ i : Fin n, Matrix (Fin (m i)) (Fin (m i)) k) =
      ∑ i : Fin n, (m i) ^ 2 := by
  rw [Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin, pow_two]

/-- The scalar action of vertexwise invertible matrices on arrow-matrix data by change of basis. -/
instance baseChangeSMul (m : Fin n → ℕ) : SMul (BaseChangeGroup k m) (MatrixData (k := k) m) where
  smul g x := fun i j e =>
    (↑(g j) : Matrix (Fin (m j)) (Fin (m j)) k) * x i j e *
      (↑(g i)⁻¹ : Matrix (Fin (m i)) (Fin (m i)) k)

/-- Changing bases sends an arrow matrix to the target change-of-basis matrix times that matrix times the inverse source change-of-basis matrix. -/
@[simp]
theorem baseChange_smul_apply (m : Fin n → ℕ) (g : BaseChangeGroup k m) (x : MatrixData (k := k) m)
    (i j : Fin n) (e : i ⟶ j) :
    (g • x) i j e =
      (↑(g j) : Matrix (Fin (m j)) (Fin (m j)) k) * x i j e *
        (↑(g i)⁻¹ : Matrix (Fin (m i)) (Fin (m i)) k) := rfl

/-- Vertexwise invertible matrices act on arrow-matrix data by simultaneous changes of basis. -/
instance baseChangeMulAction (m : Fin n → ℕ) :
    MulAction (BaseChangeGroup k m) (MatrixData (k := k) m) where
  one_smul x := by
    funext i j e
    rw [baseChange_smul_apply]
    simp
  mul_smul g h x := by
    funext i j e
    rw [baseChange_smul_apply, baseChange_smul_apply, baseChange_smul_apply]
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_assoc]

/-- The quiver representation on coordinate spaces determined by a collection of arrow matrices. -/
noncomputable def matrixDataToRepresentation (m : Fin n → ℕ) (x : MatrixData (k := k) m) :
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k (Fin n) where
  obj := fun i => Fin (m i) → k
  map := fun {i j} e => Matrix.toLin' (x i j e)

/-- The vector space at a vertex of the representation determined by arrow matrices is the corresponding coordinate space. -/
@[simp]
theorem matrixDataToRepresentation_obj (m : Fin n → ℕ) (x : MatrixData (k := k) m) (i : Fin n) :
    (matrixDataToRepresentation m x).obj i = (Fin (m i) → k) := rfl

/-- In the representation determined by arrow matrices, each arrow acts by the linear map represented by its assigned matrix. -/
@[simp]
theorem matrixDataToRepresentation_map (m : Fin n → ℕ) (x : MatrixData (k := k) m)
    {i j : Fin n} (e : i ⟶ j) :
    (matrixDataToRepresentation m x).map e = Matrix.toLin' (x i j e) := rfl

/-- The linear automorphism of a finite coordinate space induced by an invertible square matrix. -/
noncomputable def generalLinearGroupToLinearEquiv {p : ℕ} (g : GL (Fin p) k) :
    (Fin p → k) ≃ₗ[k] (Fin p → k) :=
  LinearEquiv.ofLinear (Matrix.toLin' (g : Matrix _ _ k))
    (Matrix.toLin' ((g⁻¹ : GL (Fin p) k) : Matrix _ _ k))
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.toLin'_one])

/-- The linear map underlying the coordinate-space equivalence of an invertible matrix is its usual matrix action. -/
@[simp]
theorem generalLinearGroupToLinearEquiv_toLinearMap {p : ℕ} (g : GL (Fin p) k) :
    (generalLinearGroupToLinearEquiv g).toLinearMap = Matrix.toLin' (g : Matrix _ _ k) := rfl

/-- The invertible matrix representing a linear equivalence of a finite coordinate space. -/
noncomputable def linearEquivToGeneralLinearGroup {p : ℕ} (e : (Fin p → k) ≃ₗ[k] (Fin p → k)) :
    GL (Fin p) k :=
  ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by
      rw [← LinearMap.toMatrix'_comp,
        show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from by ext x; simp,
        LinearMap.toMatrix'_id],
    by
      rw [← LinearMap.toMatrix'_comp,
        show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from by ext x; simp,
        LinearMap.toMatrix'_id]⟩

/-- The matrix underlying the general linear group element obtained from a coordinate-space equivalence is the matrix of its linear map. -/
@[simp]
theorem linearEquivToGeneralLinearGroup_val {p : ℕ} (e : (Fin p → k) ≃ₗ[k] (Fin p → k)) :
    (linearEquivToGeneralLinearGroup e : Matrix (Fin p) (Fin p) k) = LinearMap.toMatrix' e.toLinearMap := rfl

/-- Two collections of arrow matrices differ by vertexwise changes of basis exactly when their associated quiver representations are isomorphic. -/
theorem matrixData_sameOrbit_iff_isomorphicRepresentations (m : Fin n → ℕ) (x y : MatrixData (k := k) m) :
    (∃ g : BaseChangeGroup k m, g • x = y) ↔
      (matrixDataToRepresentation m x).Related (matrixDataToRepresentation m y) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun i => generalLinearGroupToLinearEquiv (g i), ?_⟩
    intro a b f
    change Matrix.toLin' (g b : Matrix _ _ k) ∘ₗ Matrix.toLin' (x a b f) =
      Matrix.toLin' ((g • x) a b f) ∘ₗ Matrix.toLin' (g a : Matrix _ _ k)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, baseChange_smul_apply]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
  · rintro ⟨e, he⟩

    refine ⟨fun v => linearEquivToGeneralLinearGroup (e v), ?_⟩
    funext i j f

    have key : LinearMap.toMatrix' (e j).toLinearMap * x i j f
        = y i j f * LinearMap.toMatrix' (e i).toLinearMap := by
      let e' (v : Fin n) : (Fin (m v) → k) ≃ₗ[k] (Fin (m v) → k) := e v
      have h : (e' j).toLinearMap ∘ₗ Matrix.toLin' (x i j f) =
          Matrix.toLin' (y i j f) ∘ₗ (e' i).toLinearMap := he f
      apply_fun LinearMap.toMatrix' at h
      rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
        LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at h
      simpa [e'] using h
    rw [baseChange_smul_apply, linearEquivToGeneralLinearGroup_val, key, ← linearEquivToGeneralLinearGroup_val,
      Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]

end RepresentationTheory.Quiver.Representation.MatrixModel

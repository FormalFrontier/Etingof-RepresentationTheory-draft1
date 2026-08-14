/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization

set_option linter.style.longLine false
set_option linter.dupNamespace false

namespace RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix

open MvPolynomial

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The algebra endomorphism of matrix-indexed multivariate polynomials induced by right multiplication by a matrix. -/
noncomputable def mvPolynomialRightMul (M : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval
    (fun ij : Fin N × Fin N => ∑ l : Fin N, M l ij.2 • MvPolynomial.X (ij.1, l))

/-- The polynomial map induced by a matrix sends each coordinate variable to the linear combination determined by its column. -/
@[simp] theorem mvPolynomialRightMul_apply_X (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    mvPolynomialRightMul M (MvPolynomial.X (i, j)) = ∑ l, M l j • MvPolynomial.X (i, l) := by
  simp [mvPolynomialRightMul]

/-- The polynomial map induced by the identity matrix is the identity algebra homomorphism. -/
theorem mvPolynomialRightMul_one :
    mvPolynomialRightMul (1 : Matrix (Fin N) (Fin N) k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [mvPolynomialRightMul_apply_X]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, AlgHom.id_apply]
  rw [Finset.sum_ite_eq' Finset.univ j (fun l => MvPolynomial.X (i, l))]
  simp

/-- The polynomial map induced by a product of matrices is the composition of the maps induced by its factors. -/
theorem mvPolynomialRightMul_mul (M₁ M₂ : Matrix (Fin N) (Fin N) k) :
    mvPolynomialRightMul (M₁ * M₂) =
      (mvPolynomialRightMul M₁).comp (mvPolynomialRightMul M₂) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, mvPolynomialRightMul_apply_X, mvPolynomialRightMul_apply_X, map_sum]
  simp_rw [map_smul, mvPolynomialRightMul_apply_X, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm]

/-- The representation of the general linear group on matrix-indexed multivariate polynomials induced by right multiplication. -/
noncomputable def generalLinearGroupMvPolynomialRightMul (k : Type*) [CommRing k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (MvPolynomial (Fin N × Fin N) k) where
  toFun g := (mvPolynomialRightMul (g : Matrix (Fin N) (Fin N) k)).toLinearMap
  map_one' := by
    change (mvPolynomialRightMul ((1 : Matrix.GeneralLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_one, mvPolynomialRightMul_one]
    rfl
  map_mul' g₁ g₂ := by
    change (mvPolynomialRightMul ((g₁ * g₂ : Matrix.GeneralLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k)).toLinearMap = _
    rw [Units.val_mul, mvPolynomialRightMul_mul]
    rfl

/-- The right-multiplication representation sends a coordinate variable to the corresponding linear combination in its row. -/
@[simp] theorem generalLinearGroupMvPolynomialRightMul_apply_X
    (g : Matrix.GeneralLinearGroup (Fin N) k) (i j : Fin N) :
    generalLinearGroupMvPolynomialRightMul k N g (MvPolynomial.X (i, j)) =
      ∑ l, (g : Matrix (Fin N) (Fin N) k) l j • MvPolynomial.X (i, l) :=
  mvPolynomialRightMul_apply_X _ i j

/-- The action of an invertible matrix in the right-multiplication representation is the polynomial map induced by its underlying matrix. -/
theorem generalLinearGroupMvPolynomialRightMul_apply
    (g : Matrix.GeneralLinearGroup (Fin N) k) (f : MvPolynomial (Fin N × Fin N) k) :
    generalLinearGroupMvPolynomialRightMul k N g f = mvPolynomialRightMul (↑g) f :=
  rfl

/-- Applying the polynomial map induced by a matrix to the generic matrix of variables gives its right product with that matrix. -/
theorem mvPolynomialRightMul_map_mvPolynomialX (M : Matrix (Fin N) (Fin N) k) :
    (mvPolynomialRightMul M).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) k) =
      Matrix.mvPolynomialX (Fin N) (Fin N) k *
        M.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k) := by
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX,
    Matrix.of_apply, mvPolynomialRightMul_apply_X, Matrix.mul_apply,
    MvPolynomial.smul_eq_C_mul]
  simp only [mul_comm]

/-- The polynomial map induced by a matrix sends the determinant of the generic matrix to the scalar determinant times that determinant. -/
theorem mvPolynomialRightMul_apply_det (M : Matrix (Fin N) (Fin N) k) :
    mvPolynomialRightMul M (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)) =
      MvPolynomial.C M.det * Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k) := by
  have hmap : (M.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)).det =
      MvPolynomial.C M.det :=
    (RingHom.map_det _ _).symm
  rw [AlgHom.map_det, mvPolynomialRightMul_map_mvPolynomialX, Matrix.det_mul, hmap, mul_comm]

/-- The polynomial map induced by any matrix preserves the principal ideal generated by the determinant of the generic matrix. -/
theorem mvPolynomialRightMul_mapsTo_detIdeal (M : Matrix (Fin N) (Fin N) k)
    {f : MvPolynomial (Fin N × Fin N) k}
    (hf : f ∈ Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)}) :
    mvPolynomialRightMul M f ∈
      Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)} := by
  rw [Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, mvPolynomialRightMul_apply_det]
  exact ⟨MvPolynomial.C M.det * mvPolynomialRightMul M q, by ring⟩

/-- Right multiplication by a diagonal matrix scales each coordinate variable by the diagonal entry indexed by its column. -/
@[simp] theorem mvPolynomialRightMul_diagonal_apply_X (v : Fin N → k) (p : Fin N × Fin N) :
    mvPolynomialRightMul (Matrix.diagonal v) (MvPolynomial.X p) =
      v p.2 • MvPolynomial.X p := by
  obtain ⟨i, j⟩ := p
  rw [mvPolynomialRightMul_apply_X, Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply_eq]
  · intro l _ hl
    rw [Matrix.diagonal_apply_ne v hl, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Right multiplication by a diagonal matrix scales a monomial by the product of the corresponding diagonal powers. -/
theorem mvPolynomialRightMul_diagonal_apply_monomial (v : Fin N → k)
    (s : (Fin N × Fin N) →₀ ℕ) (c : k) :
    mvPolynomialRightMul (Matrix.diagonal v) (MvPolynomial.monomial s c) =
      (s.prod fun p e => v p.2 ^ e) • MvPolynomial.monomial s c := by
  have hC : mvPolynomialRightMul (Matrix.diagonal v) (MvPolynomial.C c) =
      MvPolynomial.C c := by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq]
  have hP : mvPolynomialRightMul (Matrix.diagonal v)
      (s.prod fun n e => MvPolynomial.X n ^ e) =
        MvPolynomial.C (s.prod fun p e => v p.2 ^ e) *
          (s.prod fun n e => MvPolynomial.X n ^ e) := by
    simp only [Finsupp.prod, map_prod, map_pow, mvPolynomialRightMul_diagonal_apply_X,
      MvPolynomial.smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib]
  rw [MvPolynomial.monomial_eq, map_mul, hC, hP, MvPolynomial.smul_eq_C_mul]
  ring

end RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix

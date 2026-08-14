import Mathlib
import RepresentationTheory.Auxiliary.AuxiliaryPolynomialSubrepresentation

set_option linter.style.longLine false

namespace RepresentationTheory.MatrixPolynomialHomogeneity

open MvPolynomial RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
  RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
  RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
  RepresentationTheory.Auxiliary.AuxiliaryPolynomialSubrepresentation

variable {k : Type*} [Field k] {N : ℕ}

/-- The polynomial transformation parametrized by a square matrix sends every homogeneous polynomial to one of the same degree. -/
theorem matrixMap_preserves_isHomogeneous (M : Matrix (Fin N) (Fin N) k) {d : ℕ}
    {f : MvPolynomial (Fin N × Fin N) k} (hf : f.IsHomogeneous d) :
    (mvPolynomialRightMul M f).IsHomogeneous d := by
  have hgen : ∀ ij : Fin N × Fin N,
      (∑ l : Fin N, M l ij.2 • MvPolynomial.X (ij.1, l) :
        MvPolynomial (Fin N × Fin N) k).IsHomogeneous 1 := by
    intro ij
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    refine Submodule.sum_mem _ fun l _ => ?_
    exact Submodule.smul_mem _ _
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X k _))
  have h := hf.aeval (fun ij => ∑ l : Fin N, M l ij.2 • MvPolynomial.X (ij.1, l)) hgen
  rwa [one_mul] at h

/-- Acting by an invertible matrix on the matrix-polynomial representation preserves homogeneity and its degree. -/
theorem generalLinearAction_preserves_isHomogeneous
    (g : Matrix.GeneralLinearGroup (Fin N) k) {d : ℕ}
    {f : MvPolynomial (Fin N × Fin N) k} (hf : f.IsHomogeneous d) :
    (generalLinearGroupMvPolynomialRightMul k N g f).IsHomogeneous d := by
  rw [generalLinearGroupMvPolynomialRightMul_apply]
  exact matrixMap_preserves_isHomogeneous _ hf

/-- The degree-indexed subrepresentation whose underlying subspace consists of homogeneous matrix polynomials of the corresponding degree. -/
noncomputable def homogeneousSubrepresentation (k : Type*) [Field k] (N : ℕ) (d : ℕ) :
    Subrepresentation (generalLinearGroupMvPolynomialRightMul k N) where
  toSubmodule := MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d
  apply_mem_toSubmodule g _f hf :=
    (MvPolynomial.mem_homogeneousSubmodule d _).2
      (generalLinearAction_preserves_isHomogeneous g
        ((MvPolynomial.mem_homogeneousSubmodule d _).1 hf))

/-- The underlying submodule of the degree-d subrepresentation is precisely the homogeneous submodule of matrix polynomials of degree d. -/
@[simp] theorem homogeneousSubrepresentation_toSubmodule (d : ℕ) :
    (homogeneousSubrepresentation k N d).toSubmodule =
      MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d :=
  rfl

/-- The action of a general linear group element through the associated representation sends a homogeneous matrix polynomial to one of the same degree. -/
theorem generalLinearActionOnAssociatedRepresentation_preserves_isHomogeneous
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    {d : ℕ} {f : MvPolynomial (Fin N × Fin N) k} (hf : f.IsHomogeneous d) :
    (twistByCharacter (generalLinearGroupToUnits k N)
      (generalLinearGroupMvPolynomialRightMul k N) g f).IsHomogeneous d := by
  rw [twistByCharacter_apply, ← MvPolynomial.mem_homogeneousSubmodule]
  exact Submodule.smul_mem _ _
    ((MvPolynomial.mem_homogeneousSubmodule d _).2
      (generalLinearAction_preserves_isHomogeneous g hf))

/-- A natural-number-indexed family of subrepresentations for the associated action on matrix polynomials. -/
noncomputable def natIndexedSubrepresentationOfAssociatedAction
    (k : Type*) [Field k] (N : ℕ) (d : ℕ) :
    Subrepresentation
      (twistByCharacter (generalLinearGroupToUnits k N)
        (generalLinearGroupMvPolynomialRightMul k N)) where
  toSubmodule := MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d
  apply_mem_toSubmodule g _f hf :=
    (MvPolynomial.mem_homogeneousSubmodule d _).2
      (generalLinearActionOnAssociatedRepresentation_preserves_isHomogeneous g
        ((MvPolynomial.mem_homogeneousSubmodule d _).1 hf))

/-- The specified polynomial in the entries of an N-by-N matrix has uniform total degree N. -/
theorem polynomial_isHomogeneous_of_degree_matrixSize :
    (auxiliary_matrix_polynomial k N).IsHomogeneous N := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, auxiliary_matrix_polynomial,
    Matrix.det_apply]
  apply Submodule.sum_mem
  intro σ _
  have hprod : (∏ i : Fin N, Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i)
      ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k N := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin N))
      (fun i => Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X k (σ i, i))
    simpa using h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rw [hσ, one_smul]
    exact hprod
  · have hneg : ((-1 : ℤˣ)) •
        (∏ i : Fin N, Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i) =
        -(∏ i : Fin N, Matrix.mvPolynomialX (Fin N) (Fin N) k (σ i) i) := by
      rw [Units.smul_def]
      simp
    rw [hσ, hneg]
    exact Submodule.neg_mem _ hprod

/-- The specified map takes a homogeneous polynomial of degree d to one of degree N+d. -/
theorem degreeShiftMap_preserves_isHomogeneous
    {d : ℕ} {Q : MvPolynomial (Fin N × Fin N) k} (hQ : Q.IsHomogeneous d) :
    (mul_auxiliary_polynomial_linearMap k N Q).IsHomogeneous (N + d) := by
  rw [mul_auxiliary_polynomial_linearMap_apply]
  exact polynomial_isHomogeneous_of_degree_matrixSize.mul hQ

/-- The image of the degree-d homogeneous subspace under the specified map lies in the homogeneous subspace of degree N+d. -/
theorem degreeShiftMap_homogeneousSubmodule_le (d : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
        (mul_auxiliary_polynomial_linearMap k N) ≤
      MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k (N + d) := by
  rintro _ ⟨Q, hQ, rfl⟩
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (degreeShiftMap_preserves_isHomogeneous
      ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hQ))

/-- For the specified degree-N polynomial, the degree-(N+e) part of its product with Q is that polynomial times the degree-e part of Q. -/
theorem homogeneousComponent_matrixSizePolynomial_mul
    (Q : MvPolynomial (Fin N × Fin N) k) (e : ℕ) :
    MvPolynomial.homogeneousComponent (N + e) (auxiliary_matrix_polynomial k N * Q) =
      auxiliary_matrix_polynomial k N * MvPolynomial.homogeneousComponent e Q := by
  conv_lhs =>
    rw [← MvPolynomial.sum_homogeneousComponent Q, Finset.mul_sum, map_sum]
  rw [show (∑ j ∈ Finset.range (Q.totalDegree + 1),
        MvPolynomial.homogeneousComponent (N + e)
          (auxiliary_matrix_polynomial k N * MvPolynomial.homogeneousComponent j Q)) =
      ∑ j ∈ Finset.range (Q.totalDegree + 1),
        (if e = j then
          auxiliary_matrix_polynomial k N * MvPolynomial.homogeneousComponent j Q else 0) from
      Finset.sum_congr rfl fun j _ => by
        rw [MvPolynomial.homogeneousComponent_of_mem
          ((MvPolynomial.mem_homogeneousSubmodule (N + j) _).2
            (polynomial_isHomogeneous_of_degree_matrixSize.mul
              (MvPolynomial.homogeneousComponent_isHomogeneous j Q)))]
        exact if_congr (by omega) rfl rfl]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · next h =>
    have he : Q.totalDegree < e := by
      simp only [Finset.mem_range, not_lt] at h
      omega
    rw [MvPolynomial.homogeneousComponent_eq_zero e Q he, mul_zero]

/-- When d is at least N, the intersection of the specified submodule with the degree-d homogeneous submodule equals the image of the degree-(d-N) homogeneous submodule under the specified map. -/
theorem inf_homogeneousSubmodule_eq_map_homogeneousSubmodule (d : ℕ) (hd : N ≤ d) :
    matrixIndexedPolynomialSubmodule k N ⊓
        MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d =
      (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k (d - N)).map
        (mul_auxiliary_polynomial_linearMap k N) := by
  have hNd : N + (d - N) = d := by omega
  apply le_antisymm
  · rintro x ⟨hxdet, hxhom⟩
    rw [← range_mul_auxiliary_polynomial_linearMap] at hxdet
    obtain ⟨Q, hQ⟩ := LinearMap.mem_range.1 hxdet
    rw [mul_auxiliary_polynomial_linearMap_apply] at hQ
    refine ⟨MvPolynomial.homogeneousComponent (d - N) Q,
      MvPolynomial.homogeneousComponent_mem _ _, ?_⟩
    rw [mul_auxiliary_polynomial_linearMap_apply,
      ← homogeneousComponent_matrixSizePolynomial_mul Q (d - N), hNd, hQ,
      MvPolynomial.homogeneousComponent_of_mem hxhom]
    simp
  · rintro y ⟨Q, hQ, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← range_mul_auxiliary_polynomial_linearMap]
      exact ⟨Q, rfl⟩
    · refine (MvPolynomial.mem_homogeneousSubmodule d _).2 ?_
      rw [mul_auxiliary_polynomial_linearMap_apply]
      have h := polynomial_isHomogeneous_of_degree_matrixSize.mul
        ((MvPolynomial.mem_homogeneousSubmodule (d - N) _).1 hQ)
      rwa [hNd] at h

end RepresentationTheory.MatrixPolynomialHomogeneity

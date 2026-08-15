/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.WeightCharacter
import RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial
import RepresentationTheory.Algebra.MonoidAlgebra.Coefficients

noncomputable section

namespace RepresentationTheory.MvPolynomial.DeterminantFormulas

open MvPolynomial Finset
open RepresentationTheory.SymmetricPolynomials.Alternant

/-- The determinant of the specified polynomial matrix is the sign of the reversal permutation
times the product of the variable differences X j - X i for i < j. -/
theorem det_matrix_eq_sign_revPerm_mul_prod_sub (N : ℕ) :
    (alternantMatrix N (staircaseExponents N)).det =
      ((Equiv.Perm.sign (@Fin.revPerm N) : ℤ) : MvPolynomial (Fin N) ℚ) *
        ∏ i : Fin N, ∏ j ∈ Ioi i,
          (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ) := by
  have h1 : alternantMatrix N (staircaseExponents N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [alternantMatrix, Matrix.vandermonde, staircaseExponents, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]

/-- The complex cast of the specified rational value equals the indicated coefficient of the
scalar-mapped product of the determinant and the partition power-sum polynomial. -/
theorem cast_value_eq_coeff_map_det_mul_psumPart (N n : ℕ) (lam : FinPartition N n)
    (μ : Nat.Partition n) :
    (partitionExpansionCoeff N lam μ : ℂ) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts))
        (MvPolynomial.map (algebraMap ℚ ℂ)
          ((alternantMatrix N (staircaseExponents N)).det *
            MvPolynomial.psumPart (Fin N) ℚ μ)) := by
  rw [MvPolynomial.coeff_map]
  rfl

end RepresentationTheory.MvPolynomial.DeterminantFormulas

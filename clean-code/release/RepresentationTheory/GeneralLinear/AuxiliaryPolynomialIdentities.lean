/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Combinatorics.AuxiliaryPolynomialSums
import RepresentationTheory.GeneralLinear.AuxiliaryPolynomialEmbedding
import RepresentationTheory.AuxiliaryCharacter

open MvPolynomial

namespace RepresentationTheory.GeneralLinear.AuxiliaryPolynomialIdentities

open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.Combinatorics.AuxiliaryPolynomialSums
open RepresentationTheory.GeneralLinear.AuxiliaryPolynomialEmbedding
open RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.SymmetricPolynomials.Alternant

/-- For an exponent function of total degree `d`, the sum of the coefficient at that exponent in
each auxiliary polynomial, weighted by evaluation at one, equals the displayed product of binomial
coefficients. -/
theorem sum_evalOne_mul_coeff_eq_prod_choose (N d : ℕ) (μ : Fin N →₀ ℕ)
    (hμ : ∑ j, μ j = d) :
    ∑ ν : FinPartition N d,
        (MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts)) *
          (partitionPolynomial N ν.parts).coeff μ =
      ((∏ j, (μ j + N - 1).choose (N - 1) : ℕ) : ℚ) := by
  simpa [Nat.cast_prod] using
    sum_auxiliaryPolynomial_coeff_mul_evalOne_eq_prod_choose (N := N) (d := d) μ hμ

/-- The auxiliary polynomial value of the indexed representation equals the sum of the displayed
auxiliary polynomials weighted by their evaluations at one. -/
theorem auxiliaryIndexedGeneralLinearFDRep_auxiliaryPolynomial_eq_weightedSum
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N d : ℕ) :
    weightCharacter k N (auxiliaryIndexedGeneralLinearFDRep k N d) =
      ∑ ν : FinPartition N d,
        (MvPolynomial.eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts)) •
          partitionPolynomial N ν.parts := by
  apply MvPolynomial.ext
  intro μ
  rw [auxiliaryPolynomial_coeff, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases h : (∑ j, μ j) = d
  · rw [if_pos h]
    exact (sum_evalOne_mul_coeff_eq_prod_choose N d μ h).symm
  · rw [if_neg h]
    refine (Finset.sum_eq_zero ?_).symm
    intro ν _
    have hdeg : (partitionPolynomial N ν.parts).coeff μ = 0 :=
      (auxiliaryPolynomial_isHomogeneous N ν.parts).coeff_eq_zero
        (by rw [Finsupp.degree_eq_sum, ν.sum_parts]; exact h)
    rw [hdeg, mul_zero]

end RepresentationTheory.GeneralLinear.AuxiliaryPolynomialIdentities

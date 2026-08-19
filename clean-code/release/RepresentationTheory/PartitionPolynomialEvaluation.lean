/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SymmetricPolynomials.Alternant
import RepresentationTheory.Alignment.Attribute

open Finset MvPolynomial Matrix

noncomputable section

namespace RepresentationTheory.PartitionPolynomialEvaluation

/-- The rational-valued ring homomorphism from multivariate polynomials indexed by a finite type. -/
def evaluationAtRat (N : ℕ) (z : ℚ) : MvPolynomial (Fin N) ℚ →+* ℚ :=
  MvPolynomial.eval (fun i => z ^ (i : ℕ))

private lemma evalGeometric_alternantMatrix_det (N : ℕ) (e : Fin N → ℕ) (z : ℚ) :
    evaluationAtRat N z (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (z ^ e j - z ^ e i) := by
  rw [RingHom.map_det]
  have h : (evaluationAtRat N z).mapMatrix (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e) =
      (vandermonde (fun j : Fin N => z ^ e j))ᵀ := by
    ext i j
    change (evaluationAtRat N z) ((RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e) i j) = _
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.of_apply, evaluationAtRat, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, vandermonde_apply, Matrix.transpose_apply]
    ring
  rw [h, det_transpose, det_vandermonde]

private lemma prod_Ioi_eq_prod_filter {M : Type*} [CommMonoid M] {N : ℕ}
    (f : Fin N → Fin N → M) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
      ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        f p.1 p.2 := by
  rw [← Finset.prod_finset_product']
  intro p
  simp [Finset.mem_filter, Finset.mem_Ioi]

private lemma prod_Ioi_sub_eq_neg_pow_mul {R : Type*} [CommRing R] {N : ℕ} (f : Fin N → R) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (f j - f i)) =
      (-1) ^ (Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ).card *
        ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
          (f p.1 - f p.2) := by
  rw [prod_Ioi_eq_prod_filter (fun i j => f j - f i)]
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ
  conv_lhs => arg 2; ext p; rw [show f p.2 - f p.1 = (-1) * (f p.1 - f p.2) by ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The field-valued ring homomorphism from rational multivariate polynomials indexed by a finite type. -/
def evaluationAtField (N : ℕ) (K : Type*) [Field K] [CharZero K] (z : K) :
    MvPolynomial (Fin N) ℚ →+* K :=
  MvPolynomial.eval₂Hom (Rat.castHom K) (fun i : Fin N => z ^ (i : ℕ))

/-- The field-valued evaluation agrees with the rational evaluation after specializing the field to the rationals. -/
@[simp] lemma evaluationAtField_rat (N : ℕ) (z : ℚ) :
    evaluationAtField N ℚ z = evaluationAtRat N z := by
  have h : (Rat.castHom ℚ) = RingHom.id ℚ := RingHom.ext fun q => Rat.cast_id q
  rw [evaluationAtField, h]
  rfl

section Field

variable {K : Type*} [Field K] [CharZero K]

private lemma evalGeometricAt_alternantMatrix_det (N : ℕ) (e : Fin N → ℕ) (z : K) :
    evaluationAtField N K z (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (z ^ e j - z ^ e i) := by
  rw [RingHom.map_det]
  have h : (evaluationAtField N K z).mapMatrix (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e) =
      (vandermonde (fun j : Fin N => z ^ e j))ᵀ := by
    ext i j
    change (evaluationAtField N K z) ((RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N e) i j) = _
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix, Matrix.of_apply, evaluationAtField, map_pow,
      MvPolynomial.eval₂Hom_X', vandermonde_apply, Matrix.transpose_apply]
    ring
  rw [h, det_transpose, det_vandermonde]

/-- States the denominator-cleared form of a field-valued auxiliary polynomial evaluation. -/
theorem auxiliaryFieldEvaluationMulFormula (N : ℕ) (lam : Fin N → ℕ) (z : K) :
    evaluationAtField N K z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) *
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) =
      ∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ))) := by
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ with hF

  have h_eval : evaluationAtField N K z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) *
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i)) =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i) := by
    rw [← evalGeometricAt_alternantMatrix_det, ← evalGeometricAt_alternantMatrix_det,
      ← map_mul, RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase]

  rw [prod_Ioi_sub_eq_neg_pow_mul (fun j => z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j),
    prod_Ioi_sub_eq_neg_pow_mul (fun j => z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j), ← hF] at h_eval
  have hsign : ((-1 : K)) ^ F.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_cancel : evaluationAtField N K z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) *
      (∏ p ∈ F, (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N p.1 - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N p.2)) =
      ∏ p ∈ F, (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam p.1 - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam p.2) :=
    mul_left_cancel₀ hsign (by linear_combination h_eval)

  have hden : (∏ p ∈ F, (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) =
      ∏ p ∈ F, (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N p.1 - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N p.2) := rfl
  have hnum :
      (∏ p ∈ F, (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) =
      ∏ p ∈ F, (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam p.1 - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam p.2) :=
    Finset.prod_congr rfl fun p _ => by
      congr 1 <;> (congr 1; simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]; omega)
  rw [hden, hnum]
  exact h_cancel

/-- Gives a field-valued specialization of an auxiliary polynomial as a quotient of pairwise power differences. -/
@[source_ref "Chapter5/Proposition5.21.2" (role := primary)]
theorem auxiliaryFieldEvaluationFormula
    (N : ℕ) (lam : Fin N → ℕ) (z : K)
    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evaluationAtField N K z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) := by
  refine (eq_div_iff ?_).mpr (auxiliaryFieldEvaluationMulFormula N lam z)
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact hz p.1 p.2 hp

/-- Evaluates an auxiliary polynomial over a field using negative power differences under the stated nonvanishing assumptions. -/
theorem auxiliaryFieldInversePowerEvaluationFormula
    (N : ℕ) (lam : Fin N → ℕ) (z : K) (hz0 : z ≠ 0)
    (hz : ∀ (i j : Fin N), i < j →
      z ^ (-((i : ℕ) : ℤ) - 1) - z ^ (-((j : ℕ) : ℤ) - 1) ≠ 0) :
    evaluationAtField N K z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ ((lam p.1 : ℤ) - ((p.1 : ℕ) : ℤ) - 1) -
          z ^ ((lam p.2 : ℤ) - ((p.2 : ℕ) : ℤ) - 1))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (-((p.1 : ℕ) : ℤ) - 1) - z ^ (-((p.2 : ℕ) : ℤ) - 1))) := by
  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ with hF

  have key : ∀ (c : Fin N → ℕ) (p : Fin N × Fin N), p ∈ F →
      z ^ ((c p.1 : ℤ) - ((p.1 : ℕ) : ℤ) - 1) - z ^ ((c p.2 : ℤ) - ((p.2 : ℕ) : ℤ) - 1) =
      z ^ (-(N : ℤ)) *
        (z ^ (c p.1 + N - 1 - (p.1 : ℕ)) - z ^ (c p.2 + N - 1 - (p.2 : ℕ))) := by
    intro c p hp
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h1 : (p.1 : ℕ) < N := p.1.isLt
    have h2 : (p.2 : ℕ) < N := p.2.isLt
    have e1 : ((c p.1 + N - 1 - (p.1 : ℕ) : ℕ) : ℤ) = (c p.1 : ℤ) - (p.1 : ℕ) - 1 + N := by
      omega
    have e2 : ((c p.2 + N - 1 - (p.2 : ℕ) : ℕ) : ℤ) = (c p.2 : ℤ) - (p.2 : ℕ) - 1 + N := by
      omega
    rw [mul_sub, ← zpow_natCast z (c p.1 + N - 1 - (p.1 : ℕ)),
      ← zpow_natCast z (c p.2 + N - 1 - (p.2 : ℕ)), e1, e2,
      ← zpow_add₀ hz0, ← zpow_add₀ hz0]
    ring_nf

  have hnum := Finset.prod_congr rfl (key lam)
  have hden := Finset.prod_congr rfl (key (fun _ => 0))
  simp only [Nat.zero_add, Nat.cast_zero, zero_sub] at hden
  rw [hnum, hden, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    mul_div_mul_left _ _ (pow_ne_zero _ (zpow_ne_zero _ hz0))]
  refine auxiliaryFieldEvaluationFormula N lam z fun i j hij => ?_
  have hkey := key (fun _ => 0) (i, j) (by simp [hF, hij])
  simp only [Nat.zero_add, Nat.cast_zero, zero_sub] at hkey
  intro h0
  exact hz i j hij (by rw [hkey, h0, mul_zero])

end Field

/-- Gives a rational specialization of an auxiliary polynomial as a quotient of pairwise power differences. -/
theorem auxiliaryRatEvaluationFormula
    (N : ℕ) (lam : Fin N → ℕ) (z : ℚ)
    (_hN : 1 ≤ N)

    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evaluationAtRat N z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) := by
  rw [← evaluationAtField_rat]
  exact auxiliaryFieldEvaluationFormula N lam z hz

/-- Gives a complex specialization of an auxiliary polynomial as a quotient of pairwise power differences. -/
theorem auxiliaryComplexEvaluationFormula
    (N : ℕ) (lam : Fin N → ℕ) (z : ℂ)
    (hz : ∀ (i j : Fin N), i < j → z ^ (N - 1 - (i : ℕ)) - z ^ (N - 1 - (j : ℕ)) ≠ 0) :
    evaluationAtField N ℂ z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (lam p.1 + N - 1 - (p.1 : ℕ)) - z ^ (lam p.2 + N - 1 - (p.2 : ℕ)))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (N - 1 - (p.1 : ℕ)) - z ^ (N - 1 - (p.2 : ℕ)))) :=
  auxiliaryFieldEvaluationFormula N lam z hz

/-- Evaluates an auxiliary polynomial over the complex numbers using negative power differences under the stated nonvanishing assumptions. -/
@[source_ref "Chapter5/Proposition5.21.2" (role := primary)]
theorem auxiliaryComplexInversePowerEvaluationFormula
    (N : ℕ) (lam : Fin N → ℕ) (z : ℂ) (hz0 : z ≠ 0)
    (hz : ∀ (i j : Fin N), i < j →
      z ^ (-((i : ℕ) : ℤ) - 1) - z ^ (-((j : ℕ) : ℤ) - 1) ≠ 0) :
    evaluationAtField N ℂ z (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ ((lam p.1 : ℤ) - ((p.1 : ℕ) : ℤ) - 1) -
          z ^ ((lam p.2 : ℤ) - ((p.2 : ℕ) : ℤ) - 1))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (z ^ (-((p.1 : ℕ) : ℤ) - 1) - z ^ (-((p.2 : ℕ) : ℤ) - 1))) :=
  auxiliaryFieldInversePowerEvaluationFormula N lam z hz0 hz

private lemma pow_sub_eq_mul_geom_sum (z : ℚ) {a b : ℕ} (hab : a ≤ b) :
    z ^ a - z ^ b = (1 - z) * (z ^ a * ∑ k ∈ Finset.range (b - a), z ^ k) := by
  have h := geom_sum_mul_neg z (b - a)
  have h2 : z ^ a * (1 - z ^ (b - a)) = z ^ a - z ^ b := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab]
  rw [← h2, ← h]; ring

private lemma nested_prod_factor_const {N : ℕ} (c : ℚ) (g : Fin N → Fin N → ℚ) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (c * g i j)) =
    c ^ (Finset.univ.sum (fun i : Fin N => (Finset.Ioi i).card)) *
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, g i j) := by
  conv_lhs => arg 2; ext i; rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

private def geomEmbed (N : ℕ) : MvPolynomial (Fin N) ℚ →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval (fun i : Fin N => (Polynomial.X : Polynomial ℚ) ^ (i : ℕ))

private lemma geomEmbed_eval (N : ℕ) (z : ℚ) (p : MvPolynomial (Fin N) ℚ) :
    (geomEmbed N p).eval z = evaluationAtRat N z p := by
  have h : (Polynomial.evalRingHom z).comp (geomEmbed N).toRingHom =
      (evaluationAtRat N z : MvPolynomial (Fin N) ℚ →+* ℚ) :=
    MvPolynomial.ringHom_ext
      (fun r => by simp [geomEmbed, evaluationAtRat, Polynomial.eval_C,
        RingHom.comp_apply])
      (fun i => by simp [geomEmbed, evaluationAtRat, MvPolynomial.aeval_X, Polynomial.eval_pow,
        Polynomial.eval_X, RingHom.comp_apply])
  exact RingHom.congr_fun h p

/-- Expresses the value at one of an auxiliary multivariate polynomial as a quotient of products over ordered index pairs. -/
@[source_ref "Chapter5/Proposition5.21.2" (role := primary)]
theorem auxiliaryEvaluationAtOneFormula
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    MvPolynomial.eval (fun _ : Fin N => (1 : ℚ)) (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) =
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        ((lam p.1 : ℚ) - (lam p.2 : ℚ) + ((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) /
      (∏ p ∈ Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ,
        (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) := by

  let φ := geomEmbed N

  set F := Finset.filter (fun p : Fin N × Fin N => p.1 < p.2) Finset.univ with hF_def

  have hφ1 : ∀ p : MvPolynomial (Fin N) ℚ,
      Polynomial.eval 1 (φ p) = MvPolynomial.eval (fun _ : Fin N => (1 : ℚ)) p := by
    intro p; rw [geomEmbed_eval]; unfold evaluationAtRat; simp [one_pow]

  have h_fund : φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) * φ (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det =
      φ (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam)).det := by
    have := congr_arg φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase N lam)
    rwa [map_mul] at this

  have h_eval_z : ∀ z : ℚ,
      (φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam)).eval z *
        (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i)) =
        (∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i)) := by
    intro z
    have hv : (φ (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det).eval z =
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i) := by
      rw [geomEmbed_eval, evalGeometric_alternantMatrix_det]
    have hs : (φ (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam)).det).eval z =
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
          (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i) := by
      rw [geomEmbed_eval, evalGeometric_alternantMatrix_det]
    have h := congr_arg (Polynomial.eval z) h_fund
    simp only [Polynomial.eval_mul] at h
    rw [hv, hs] at h; exact h

  let D : Polynomial ℚ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
    (Polynomial.X ^ (N - 1 - (j : ℕ)) *
     ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), Polynomial.X ^ k)
  let Num : Polynomial ℚ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
    (Polynomial.X ^ (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j) *
     ∑ k ∈ Finset.range (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j), Polynomial.X ^ k)

  have h_cancel : φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) * D = Num := by

    suffices h : φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam) * D - Num = 0 from sub_eq_zero.mp h
    apply Polynomial.eq_zero_of_infinite_isRoot

    apply (Set.Finite.infinite_compl (Set.finite_singleton (1 : ℚ))).mono
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul]

    have h_vand : ∀ (i : Fin N) (j : Fin N), j ∈ Finset.Ioi i →
        z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i =
        (1 - z) * (z ^ (N - 1 - (j : ℕ)) *
          ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), z ^ k) := by
      intro i j hj
      have hij := Finset.mem_Ioi.mp hj
      simp only [RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents]
      have hab : N - 1 - (j : ℕ) ≤ N - 1 - (i : ℕ) := by omega
      have heq : (N - 1 - (i : ℕ)) - (N - 1 - (j : ℕ)) = (j : ℕ) - (i : ℕ) := by omega
      rw [← heq]; exact pow_sub_eq_mul_geom_sum z hab

    have h_shift : ∀ (i : Fin N) (j : Fin N), j ∈ Finset.Ioi i →
        z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i =
        (1 - z) * (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j *
          ∑ k ∈ Finset.range (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j), z ^ k) := by
      intro i j hj
      have hij := Finset.mem_Ioi.mp hj
      have h_lam : lam j ≤ lam i := hlam (by omega : (i : ℕ) ≤ (j : ℕ))
      have hab : RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j ≤ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i := by
        simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]; omega
      exact pow_sub_eq_mul_geom_sum z hab

    have h_vand_prod : ∀ (i : Fin N),
        ∏ j ∈ Finset.Ioi i, (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N i) =
        ∏ j ∈ Finset.Ioi i,
          ((1 - z) * (z ^ (N - 1 - (j : ℕ)) *
            ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), z ^ k)) := by
      intro i; apply Finset.prod_congr rfl; intro j hj; exact h_vand i j hj
    have h_shift_prod : ∀ (i : Fin N),
        ∏ j ∈ Finset.Ioi i, (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j - z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i) =
        ∏ j ∈ Finset.Ioi i,
          ((1 - z) * (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j *
            ∑ k ∈ Finset.range (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j), z ^ k)) := by
      intro i; apply Finset.prod_congr rfl; intro j hj; exact h_shift i j hj

    set M := Finset.univ.sum (fun i : Fin N => (Finset.Ioi i).card) with hM_def

    have h_factored := h_eval_z z
    simp_rw [h_vand_prod] at h_factored
    simp_rw [h_shift_prod] at h_factored
    rw [nested_prod_factor_const] at h_factored
    rw [nested_prod_factor_const] at h_factored

    have h1z : (1 - z) ^ M ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hz))

    have hD_eval : D.eval z = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ (N - 1 - (j : ℕ)) * ∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)), z ^ k) := by
      simp only [D, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_finsetSum]
    have hNum_eval : Num.eval z = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        (z ^ RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j *
          ∑ k ∈ Finset.range (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j), z ^ k) := by
      simp only [Num, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_finsetSum]
    rw [← hD_eval, ← hNum_eval] at h_factored

    have h_cancel' : (φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam)).eval z * D.eval z = Num.eval z := by
      have h2 : (1 - z) ^ M * ((φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam)).eval z * D.eval z) =
          (1 - z) ^ M * Num.eval z := by linear_combination h_factored
      exact mul_left_cancel₀ h1z h2
    linarith

  have h_at_1 : (φ (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam)).eval 1 * D.eval 1 = Num.eval 1 := by
    have := congr_arg (Polynomial.eval (1 : ℚ)) h_cancel
    simp only [Polynomial.eval_mul] at this
    exact this

  have hD1 : D.eval 1 = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      ((j : ℕ) - (i : ℕ) : ℚ) := by
    simp only [D, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, one_mul, Polynomial.eval_finsetSum]
    apply Finset.prod_congr rfl; intro i _
    apply Finset.prod_congr rfl; intro j hj
    have hij : (i : ℕ) ≤ (j : ℕ) := (Finset.mem_Ioi.mp hj).le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_sub hij]
  have hNum1 : Num.eval 1 = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam i - RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j : ℚ) := by
    simp only [Num, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, one_mul, Polynomial.eval_finsetSum]
    apply Finset.prod_congr rfl; intro i _
    apply Finset.prod_congr rfl; intro j hj
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hij := Finset.mem_Ioi.mp hj
    exact Nat.cast_sub (by simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]; have := hlam (le_of_lt hij); omega)

  have hD1_ne : D.eval 1 ≠ 0 := by
    rw [hD1]
    apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    have hij := Finset.mem_Ioi.mp hj
    exact ne_of_gt (sub_pos.mpr (Nat.cast_lt.mpr hij))

  have hD1_filter : D.eval 1 =
      ∏ p ∈ F, (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ)) := by
    rw [hD1, prod_Ioi_eq_prod_filter]

  have hNum1_filter : Num.eval 1 =
      ∏ p ∈ F, ((lam p.1 : ℚ) - (lam p.2 : ℚ) + ((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ)) := by
    rw [hNum1, prod_Ioi_eq_prod_filter]
    apply Finset.prod_congr rfl; intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]
    have h_lam : lam p.2 ≤ lam p.1 := hlam (by omega : (p.1 : ℕ) ≤ (p.2 : ℕ))
    push_cast
    rw [Nat.cast_sub (by omega : (p.1 : ℕ) ≤ N - 1)]
    rw [Nat.cast_sub (by omega : (p.2 : ℕ) ≤ N - 1)]
    rw [Nat.cast_sub (by omega)]
    ring

  have hD1_filter_ne : (∏ p ∈ F, (((p.2 : ℕ) : ℚ) - ((p.1 : ℕ) : ℚ))) ≠ 0 := by
    rw [← hD1_filter]; exact hD1_ne

  rw [← hφ1, eq_div_iff hD1_filter_ne, ← hNum1_filter, ← hD1_filter, ← h_at_1]

end RepresentationTheory.PartitionPolynomialEvaluation

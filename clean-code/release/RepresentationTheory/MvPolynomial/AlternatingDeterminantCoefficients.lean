/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Combinatorics.PermutationPowerSeries
import RepresentationTheory.FinsuppPermutationAuxiliary
import RepresentationTheory.SymmetricPolynomials.Alternant
import RepresentationTheory.GeneralLinearGroup.WeightCharacter

open MvPolynomial Finset

noncomputable section

namespace RepresentationTheory.MvPolynomial.AlternatingDeterminantCoefficients

open Auxiliary.PermutationPolynomials
open Combinatorics.PermutationPowerSeries
open FinsuppPermutationAuxiliary
open GeneralLinearGroup.WeightCharacter
open LinearAlgebra.AuxiliaryPowerSeriesMatrix
open SymmetricPolynomials.Alternant

/-- The exponent tuple obtained by applying a permutation to the staircase exponents. -/
private def permutedStaircaseExponent (N : ℕ) (π : Equiv.Perm (Fin N)) : Fin N → ℕ :=
  fun i => staircaseExponents N (π⁻¹ i)

/-- A coefficient of a polynomial multiplied by the displayed determinant is an alternating sum
of shifted coefficients over permutations. -/
theorem coeff_det_mul_eq_alternating_sum (N : ℕ) (e : Fin N →₀ ℕ)
    (f : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff e ((alternantMatrix N (staircaseExponents N)).det * f) =
    ∑ π : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) *
      (if ∀ i, permutedStaircaseExponent N π i ≤ e i
       then MvPolynomial.coeff
         (e - Finsupp.equivFunOnFinite.symm (permutedStaircaseExponent N π)) f
       else 0) := by
  rw [Matrix.det_apply, Finset.sum_mul]
  simp only [MvPolynomial.coeff_sum, smul_mul_assoc, MvPolynomial.coeff_smul]
  simp_rw [show ∀ σ : Equiv.Perm (Fin N),
      ∏ j, alternantMatrix N (staircaseExponents N) (σ j) j =
        monomial (Finsupp.equivFunOnFinite.symm (staircaseExponents N ∘ ⇑σ.symm)) 1
      from fun σ => by
        rw [show ∏ j, alternantMatrix N (staircaseExponents N) (σ j) j =
            ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ staircaseExponents N j
            from rfl,
          show ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ staircaseExponents N j =
            ∏ i, X i ^ staircaseExponents N (σ.symm i)
            from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
        exact prod_X_pow_eq_monomial _]
  apply Finset.sum_congr rfl
  intro π _
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
  congr 1
  rw [MvPolynomial.coeff_monomial_mul', one_mul]
  have heq : Finsupp.equivFunOnFinite.symm (staircaseExponents N ∘ ⇑π.symm) =
      Finsupp.equivFunOnFinite.symm (permutedStaircaseExponent N π) := by
    ext i
    simp [permutedStaircaseExponent, Equiv.Perm.inv_def]
  rw [heq]
  congr 1

/-- An auxiliary value is an alternating sum of coefficients indexed by permutations satisfying
componentwise bounds. -/
theorem auxiliary_value_eq_alternating_coeff_sum
    (N : ℕ) {n : ℕ} (lam : FinPartition N n) (μ : n.Partition) :
    partitionExpansionCoeff N lam μ =
    ∑ π : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) *
      (if ∀ i, permutedStaircaseExponent N π i ≤ addStaircase N lam.parts i
       then MvPolynomial.coeff
         (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts) -
          Finsupp.equivFunOnFinite.symm (permutedStaircaseExponent N π))
         (MvPolynomial.psumPart (Fin N) ℚ μ)
       else 0) := by
  unfold partitionExpansionCoeff
  exact coeff_det_mul_eq_alternating_sum N
    (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts))
    (MvPolynomial.psumPart (Fin N) ℚ μ)

/-- Subtracting permuted staircase exponents from the shifted partition preserves its total. -/
private lemma sum_addStaircase_sub_permutedStaircaseExponent
    (N : ℕ) {n : ℕ} (lam : FinPartition N n)
    (π : Equiv.Perm (Fin N))
    (hle : ∀ i, permutedStaircaseExponent N π i ≤ addStaircase N lam.parts i) :
    ∑ i, (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts) -
      Finsupp.equivFunOnFinite.symm (permutedStaircaseExponent N π) : Fin N →₀ ℕ) i = n := by
  have heval : ∀ (g : Fin N → ℕ) (i : Fin N),
      (Finsupp.equivFunOnFinite.symm g : Fin N →₀ ℕ) i = g i := by
    intros
    simp [Finsupp.equivFunOnFinite]
  simp_rw [show ∀ i,
      (Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts) -
        Finsupp.equivFunOnFinite.symm
          (permutedStaircaseExponent N π) : Fin N →₀ ℕ) i =
        addStaircase N lam.parts i - permutedStaircaseExponent N π i
      from by
        intro i
        simp [Finsupp.equivFunOnFinite, Finsupp.coe_tsub]]
  have key :
      ∑ i : Fin N,
          (addStaircase N lam.parts i - permutedStaircaseExponent N π i) +
        ∑ i : Fin N, permutedStaircaseExponent N π i =
      ∑ i : Fin N, addStaircase N lam.parts i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
  have hsum_shifted : ∑ i : Fin N, addStaircase N lam.parts i =
      n + ∑ i : Fin N, staircaseExponents N i := by
    unfold addStaircase staircaseExponents
    rw [show ∑ i : Fin N, (lam.parts i + (N - 1 - ↑i)) =
        ∑ i : Fin N, lam.parts i + ∑ i : Fin N, (N - 1 - (↑i : ℕ))
      from Finset.sum_add_distrib]
    rw [lam.sum_parts]
  have hsum_perm : ∑ i : Fin N, permutedStaircaseExponent N π i =
      ∑ i : Fin N, staircaseExponents N i :=
    Fintype.sum_equiv π⁻¹ _ _ (fun _ => rfl)
  omega

/-- A sum of products of auxiliary values equals a factorial times a double alternating
coefficient sum over bounded permutations. -/
theorem sum_auxiliary_values_mul_eq_factorial_mul_double_alternating_sum
    (N : ℕ) {n : ℕ} (lam lam' : FinPartition N n) :
    (∑ σ : Equiv.Perm (Fin n),
      partitionExpansionCoeff N lam (cycleType σ) *
      partitionExpansionCoeff N lam' (cycleType σ) : ℚ) =
    (n.factorial : ℚ) *
    ∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) * (↑(Equiv.Perm.sign τ : ℤ) : ℚ) *
      (if (∀ i, permutedStaircaseExponent N π i ≤ addStaircase N lam.parts i) ∧
          (∀ i, permutedStaircaseExponent N τ i ≤ addStaircase N lam'.parts i)
       then MvPowerSeries.coeff
          (auxiliaryFinsupp N
            (fun i => addStaircase N lam.parts i - permutedStaircaseExponent N π i)
            (fun i => addStaircase N lam'.parts i - permutedStaircaseExponent N τ i))
          (auxiliaryPowerSeries N ℚ)
       else 0) := by
  simp_rw [auxiliary_value_eq_alternating_coeff_sum]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Equiv.Perm (Fin n)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  set hcondπ := ∀ i, permutedStaircaseExponent N π i ≤ addStaircase N lam.parts i
  set hcondτ := ∀ i, permutedStaircaseExponent N τ i ≤ addStaircase N lam'.parts i
  set sπ := (↑(Equiv.Perm.sign π : ℤ) : ℚ)
  set sτ := (↑(Equiv.Perm.sign τ : ℤ) : ℚ)
  set α' := Finsupp.equivFunOnFinite.symm (addStaircase N lam.parts) -
    Finsupp.equivFunOnFinite.symm (permutedStaircaseExponent N π)
  set β' := Finsupp.equivFunOnFinite.symm (addStaircase N lam'.parts) -
    Finsupp.equivFunOnFinite.symm (permutedStaircaseExponent N τ)
  have aux : ∀ (a b c d : ℚ) (P Q : Prop) [Decidable P] [Decidable Q],
      (a * if P then c else 0) * (b * if Q then d else 0) =
      a * b * if P ∧ Q then c * d else 0 := by
    intros; split_ifs <;> simp_all; ring
  simp_rw [aux]
  rw [← Finset.mul_sum]
  split_ifs with h
  · obtain ⟨hπ, hτ⟩ := h
    simp_rw [← permutationPowerSum_eq_cycleType]
    have hα_sum : ∑ i, α' i = n :=
      sum_addStaircase_sub_permutedStaircaseExponent N lam π hπ
    have hβ_sum : ∑ i, β' i = n :=
      sum_addStaircase_sub_permutedStaircaseExponent N lam' τ hτ
    rw [sum_coeff_mul_coeff_eq_factorial_mul_auxiliaryPowerSeriesCoeff
      N α' β' hα_sum hβ_sum]
    have haux : auxiliaryFinsupp N (⇑α') (⇑β') =
        auxiliaryFinsupp N
          (fun i => addStaircase N lam.parts i - permutedStaircaseExponent N π i)
          (fun i =>
            addStaircase N lam'.parts i - permutedStaircaseExponent N τ i) := by
      ext v
      cases v <;>
        simp [auxiliaryFinsupp, α', β', Finsupp.equivFunOnFinite]
    rw [haux]
    ring
  · simp

/-- Multiplication by the reversing permutation produces the permuted staircase exponent. -/
private lemma inv_mul_revPerm_val (N : ℕ) (π : Equiv.Perm (Fin N)) (i : Fin N) :
    Fin.val ((π * @Fin.revPerm N)⁻¹ i) = permutedStaircaseExponent N π i := by
  change ((π * @Fin.revPerm N).symm i).val = permutedStaircaseExponent N π i
  unfold permutedStaircaseExponent staircaseExponents
  have hrev : ((π * @Fin.revPerm N).symm i) = Fin.rev (π.symm i) := by
    change (@Fin.revPerm N).symm (π.symm i) = Fin.rev (π.symm i)
    rw [Fin.revPerm_symm, Fin.revPerm_apply]
  rw [hrev]
  simp [Fin.rev, Equiv.Perm.inv_def]
  omega

/-- Adding the staircase exponents is injective on finite partition tuples. -/
private lemma addStaircase_injective (N : ℕ) {n : ℕ}
    (lam lam' : FinPartition N n) :
    addStaircase N lam.parts = addStaircase N lam'.parts ↔ lam = lam' := by
  constructor
  · intro h
    have hparts : lam.parts = lam'.parts := by
      funext i
      have hi := congr_fun h i
      simp [addStaircase] at hi
      omega
    cases lam
    cases lam'
    simp only [FinPartition.mk.injEq] at hparts ⊢
    exact hparts
  · rintro rfl
    rfl

/-- Reindexing by the reversing permutation expresses the double signed sum using permuted
staircase exponents. -/
private lemma double_signed_sum_permutedStaircaseExponent
    (N : ℕ) (α β : Fin N → ℕ) (hα : StrictAnti α) (hβ : StrictAnti β) :
    (∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, permutedStaircaseExponent N π i ≤ α i) ∧
          (∀ i, permutedStaircaseExponent N τ i ≤ β i)
       then MvPowerSeries.coeff
          (auxiliaryFinsupp N
            (fun i => α i - permutedStaircaseExponent N π i)
            (fun i => β i - permutedStaircaseExponent N τ i))
          (auxiliaryPowerSeries N ℂ)
       else 0)) =
    if α = β then 1 else 0 := by
  set ρ := @Fin.revPerm N
  have hsρ : ((Equiv.Perm.sign ρ : ℤ) : ℂ) *
      ((Equiv.Perm.sign ρ : ℤ) : ℂ) = 1 := by
    have h := Int.units_sq (Equiv.Perm.sign ρ)
    have hsquare : ((Equiv.Perm.sign ρ : ℤ) : ℂ) *
        ((Equiv.Perm.sign ρ : ℤ) : ℂ) =
        (↑(↑(Equiv.Perm.sign ρ ^ 2) : ℤ) : ℂ) := by
      push_cast
      ring
    rw [hsquare, h]
    simp
  have h_eq : ∀ (π τ : Equiv.Perm (Fin N)),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, permutedStaircaseExponent N π i ≤ α i) ∧
          (∀ i, permutedStaircaseExponent N τ i ≤ β i)
       then MvPowerSeries.coeff
          (auxiliaryFinsupp N
            (fun i => α i - permutedStaircaseExponent N π i)
            (fun i => β i - permutedStaircaseExponent N τ i))
          (auxiliaryPowerSeries N ℂ)
       else 0) =
      ((Equiv.Perm.sign (π * ρ) : ℤ) : ℂ) *
        ((Equiv.Perm.sign (τ * ρ) : ℤ) : ℂ) *
      (if (∀ i, ((π * ρ)⁻¹ i : Fin N).val ≤ α i) ∧
          (∀ i, ((τ * ρ)⁻¹ i : Fin N).val ≤ β i)
       then MvPowerSeries.coeff
          (auxiliaryFinsupp N
            (fun i => α i - ((π * ρ)⁻¹ i : Fin N).val)
            (fun i => β i - ((τ * ρ)⁻¹ i : Fin N).val))
          (auxiliaryPowerSeries N ℂ)
       else 0) := by
    intro π τ
    simp only [ρ]
    simp_rw [inv_mul_revPerm_val, Equiv.Perm.sign_mul]
    push_cast
    split_ifs
    · congr 1
      have hsign :
          (↑↑(Equiv.Perm.sign π) * ↑↑(Equiv.Perm.sign (@Fin.revPerm N))) *
              (↑↑(Equiv.Perm.sign τ) * ↑↑(Equiv.Perm.sign (@Fin.revPerm N))) =
            ↑↑(Equiv.Perm.sign π) * ↑↑(Equiv.Perm.sign τ) *
              ((↑↑(Equiv.Perm.sign (@Fin.revPerm N)) : ℂ) *
                ↑↑(Equiv.Perm.sign (@Fin.revPerm N))) := by
        ring
      rw [hsign, hsρ, mul_one]
    · simp
  exact (Fintype.sum_equiv (Equiv.mulRight ρ) _ _
    (fun π => Fintype.sum_equiv (Equiv.mulRight ρ) _ _ (fun τ => h_eq π τ))).trans
    (double_signed_permutation_sum_eq_indicator_of_strictAnti N α β hα hβ)

/-- The sum of products of two auxiliary value families is the factorial when their indices agree
and zero otherwise. -/
theorem sum_auxiliary_values_mul_eq_factorial_ite
    (N : ℕ) {n : ℕ} (lam lam' : FinPartition N n) :
    ∑ σ : Equiv.Perm (Fin n),
      partitionExpansionCoeff N lam (cycleType σ) *
      partitionExpansionCoeff N lam' (cycleType σ) =
    if lam = lam' then (n.factorial : ℚ) else 0 := by
  rw [sum_auxiliary_values_mul_eq_factorial_mul_double_alternating_sum]
  set α := addStaircase N lam.parts
  set β := addStaircase N lam'.parts
  have hα_strict : StrictAnti α := by
    intro i j hij
    simp only [α, addStaircase]
    have hparts := lam.parts_antitone hij.le
    omega
  have hβ_strict : StrictAnti β := by
    intro i j hij
    simp only [β, addStaircase]
    have hparts := lam'.parts_antitone hij.le
    omega
  suffices hsum :
      ∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (↑(Equiv.Perm.sign π : ℤ) : ℚ) * (↑(Equiv.Perm.sign τ : ℤ) : ℚ) *
        (if (∀ i, permutedStaircaseExponent N π i ≤ α i) ∧
            (∀ i, permutedStaircaseExponent N τ i ≤ β i)
         then MvPowerSeries.coeff
            (auxiliaryFinsupp N
              (fun i => α i - permutedStaircaseExponent N π i)
              (fun i => β i - permutedStaircaseExponent N τ i))
            (auxiliaryPowerSeries N ℚ)
         else 0) = if lam = lam' then 1 else 0 by
    rw [hsum]
    split_ifs <;> ring
  have h_inj : Function.Injective (algebraMap ℚ ℂ) := Rat.cast_injective
  apply h_inj
  rw [map_sum]
  simp_rw [map_sum, map_mul, map_intCast]
  have hcoeff_cast : ∀ (P : Prop) [Decidable P]
      (e : AuxiliaryIndex N →₀ ℕ),
      (algebraMap ℚ ℂ)
          (if P then MvPowerSeries.coeff e (auxiliaryPowerSeries N ℚ) else 0) =
        (if P then MvPowerSeries.coeff e (auxiliaryPowerSeries N ℂ) else 0) := by
    intro P _ e
    split_ifs
    · rw [← MvPowerSeries.coeff_map, map_auxiliaryPowerSeries]
    · exact map_zero _
  simp_rw [hcoeff_cast]
  have hrhs : (algebraMap ℚ ℂ) (if lam = lam' then 1 else 0) =
      if α = β then (1 : ℂ) else 0 := by
    simp only [apply_ite (algebraMap ℚ ℂ), map_one, map_zero]
    exact if_congr (addStaircase_injective N lam lam').symm rfl rfl
  rw [hrhs]
  exact double_signed_sum_permutedStaircaseExponent N α β hα_strict hβ_strict

end RepresentationTheory.MvPolynomial.AlternatingDeterminantCoefficients

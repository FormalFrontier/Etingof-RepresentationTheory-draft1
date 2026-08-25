/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.MvPolynomial.AlternatingDeterminantCoefficients
import RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary

open MvPolynomial Finset

namespace RepresentationTheory.Combinatorics.AuxiliaryPolynomialSums

open Auxiliary.PermutationPolynomials
open FinsuppPermutationAuxiliary
open GeneralLinearGroup.WeightCharacter
open MvPolynomial.AlternatingDeterminantCoefficients
open SymmetricPolynomials.Alternant

variable {N d : ℕ}

/-- A factorial times the pointwise product sum equals the sum of products of the two displayed
auxiliary weighted sums. -/
theorem factorial_mul_sum_mul_eq_sum_auxiliaryWeightedSums
    (F G : FinPartition N d → ℚ) :
    (d.factorial : ℚ) * ∑ ν : FinPartition N d, F ν * G ν =
    ∑ σ : Equiv.Perm (Fin d),
      (∑ ν : FinPartition N d, partitionExpansionCoeff N ν (cycleType σ) * F ν) *
      (∑ ν : FinPartition N d, partitionExpansionCoeff N ν (cycleType σ) * G ν) := by
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_comm)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  have hinner : ∀ ρ : FinPartition N d,
      (∑ σ : Equiv.Perm (Fin d),
        partitionExpansionCoeff N ν (cycleType σ) * F ν *
          (partitionExpansionCoeff N ρ (cycleType σ) * G ρ)) =
      (if ν = ρ then (d.factorial : ℚ) else 0) * (F ν * G ρ) := by
    intro ρ
    have : ∀ σ : Equiv.Perm (Fin d),
        partitionExpansionCoeff N ν (cycleType σ) * F ν *
          (partitionExpansionCoeff N ρ (cycleType σ) * G ρ) =
        (partitionExpansionCoeff N ν (cycleType σ) *
          partitionExpansionCoeff N ρ (cycleType σ)) * (F ν * G ρ) := by
      intro σ
      ring
    simp_rw [this, ← Finset.sum_mul,
      sum_auxiliary_values_mul_eq_factorial_ite N ν ρ]
  simp_rw [hinner, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ ν
    (fun ρ => (d.factorial : ℚ) * (F ν * G ρ))]
  simp

/-- Evaluation at one of the auxiliary permutation polynomial is a weighted sum of evaluations at
one of the displayed auxiliary polynomials. -/
theorem auxiliaryPermutationPolynomial_evalOne_eq_auxiliaryPolynomialSum
    (σ : Equiv.Perm (Fin d)) :
    eval (fun _ => (1 : ℚ)) (auxiliaryPermutationPolynomial' N σ) =
    ∑ ν : FinPartition N d,
      partitionExpansionCoeff N ν (cycleType σ) *
        eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts) := by
  rw [permutationPowerSum_eq_cycleType, psumPart_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]

/-- A coefficient of the auxiliary permutation polynomial is a finite sum of products of the
displayed auxiliary scalars and auxiliary polynomial coefficients. -/
theorem auxiliaryPermutationPolynomial_coeff_eq_auxiliarySum
    (σ : Equiv.Perm (Fin d)) (μ : Fin N →₀ ℕ) :
    coeff μ (auxiliaryPermutationPolynomial' N σ) =
    ∑ ν : FinPartition N d,
      partitionExpansionCoeff N ν (cycleType σ) *
        coeff μ (partitionPolynomial N ν.parts) := by
  rw [permutationPowerSum_eq_cycleType, psumPart_expansion, coeff_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [coeff_smul, smul_eq_mul]

/-- Evaluation at one of the auxiliary permutation polynomial is the sum of its coefficients over
the finitely supported antidiagonal. -/
theorem auxiliaryPermutationPolynomial_evalOne_eq_antidiag_coeff_sum
    (σ : Equiv.Perm (Fin d)) :
    eval (fun _ => (1 : ℚ)) (auxiliaryPermutationPolynomial' N σ) =
    ∑ β ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d,
      coeff β (auxiliaryPermutationPolynomial' N σ) := by
  rw [eval_eq']
  simp only [one_pow, Finset.prod_const_one, mul_one]
  have hhom : (auxiliaryPermutationPolynomial' N σ).IsHomogeneous d := by
    rw [permutationPowerSum_eq_cycleType]
    exact psumPart_isHomogeneous N (cycleType σ)
  apply Finset.sum_subset
  · intro β hβ
    rw [mem_finsuppAntidiag]
    have hdeg : β.degree = ∑ i, β i := Finsupp.degree_eq_sum β
    refine ⟨?_, Finset.subset_univ _⟩
    by_contra hne
    exact (mem_support_iff.1 hβ) (hhom.coeff_eq_zero (by rw [hdeg]; exact hne))
  · intro β _ hβ
    exact Finsupp.notMem_support_iff.1 hβ

/-- The number of bounded natural-valued functions with prescribed sum is a binomial
coefficient. -/
private theorem card_boundedFun_sum_eq_choose (m : ℕ) (hm : m ≤ d) (hN : 1 ≤ N) :
    Fintype.card {c : Fin N → Fin (d + 1) // ∑ i, (c i : ℕ) = m} =
    (m + N - 1).choose (N - 1) := by
  rw [← Nat.card_eq_fintype_card]
  have ebound : {c : Fin N → Fin (d + 1) // ∑ i, (c i : ℕ) = m} ≃
      {c : Fin N → ℕ // ∑ i, c i = m} :=
    { toFun := fun c => ⟨fun i => (c.val i : ℕ), c.prop⟩
      invFun := fun c => ⟨fun i => ⟨c.val i, by
          have hle := Finset.single_le_sum (f := c.val)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          rw [c.prop] at hle
          omega⟩, by simpa using c.prop⟩
      left_inv := fun c => by ext i; simp
      right_inv := fun c => by ext i; simp }
  have esym : {c : Fin N → ℕ // ∑ i, c i = m} ≃ Sym (Fin N) m :=
    Equiv.subtypeEquiv
      (Finsupp.equivFunOnFinite.symm.trans Multiset.toFinsupp.toEquiv.symm)
      (fun c => by
        change (∑ i, c i = m) ↔
          Multiset.card (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm c)) = m
        rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
        simp [Finsupp.equivFunOnFinite])
  rw [Nat.card_congr ebound, Nat.card_congr esym, Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin, Nat.add_comm N m,
    ← Nat.choose_symm (show m ≤ m + N - 1 by omega)]
  congr 1
  omega

/-- For a multi-index of fixed total degree, the sum of the displayed auxiliary finite-type
cardinalities is a product of binomial coefficients. -/
theorem sum_card_auxiliaryType_eq_prod_choose
    (μ : Fin N →₀ ℕ) (hμ : ∑ i, μ i = d) :
    ∑ β ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d,
      Fintype.card (FinNatFunctionPairAuxiliary N (n := d) (⇑β) (⇑μ)) =
    ∏ j, (μ j + N - 1).choose (N - 1) := by
  classical
  let M := {K : Fin N → Fin N → Fin (d + 1) //
    ∀ j, ∑ i, (K i j : ℕ) = μ j}
  let rowF : M → (Fin N →₀ ℕ) :=
    fun K => Finsupp.equivFunOnFinite.symm (fun i => ∑ j, (K.val i j : ℕ))
  have hrowF_apply : ∀ (K : M) (i : Fin N),
      rowF K i = ∑ j, (K.val i j : ℕ) := by
    intro K i
    simp [rowF]
  have hmem : ∀ K : M,
      rowF K ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d := by
    intro K
    rw [mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    simp_rw [hrowF_apply]
    rw [Finset.sum_comm]
    simp_rw [K.prop]
    exact hμ
  have hfib : Fintype.card M =
      ∑ β ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d,
        Fintype.card (FinNatFunctionPairAuxiliary N (n := d) (⇑β) (⇑μ)) := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (fun K _ => hmem K)]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun K => ⟨K.val.val, ⟨fun i => ?_, K.val.prop⟩⟩
        invFun := fun K => ⟨⟨K.val, K.prop.2⟩, ?_⟩
        left_inv := fun K => rfl
        right_inv := fun K => rfl }
    · have h := K.prop
      rw [← hrowF_apply K.val i, h]
    · change Finsupp.equivFunOnFinite.symm
        (fun i => ∑ j, (K.val i j : ℕ)) = β
      rw [show (fun i => ∑ j, (K.val i j : ℕ)) = (⇑β : Fin N → ℕ)
        from funext K.prop.1]
      exact Finsupp.equivFunOnFinite_symm_coe β
  have hfactor : Fintype.card M =
      ∏ j, (μ j + N - 1).choose (N - 1) := by
    have e : M ≃ ∀ j, {c : Fin N → Fin (d + 1) // ∑ i, (c i : ℕ) = μ j} :=
      { toFun := fun K j => ⟨fun i => K.val i j, K.prop j⟩
        invFun := fun g => ⟨fun i j => (g j).val i, fun j => (g j).prop⟩
        left_inv := fun K => rfl
        right_inv := fun g => rfl }
    rw [Fintype.card_congr e, Fintype.card_pi]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    refine card_boundedFun_sum_eq_choose (μ j) ?_ (Fin.pos j)
    rw [← hμ]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [← hfib, hfactor]

/-- For a multi-index of the prescribed total degree, the weighted coefficient sum over the
auxiliary polynomials equals a product of binomial coefficients. -/
theorem sum_auxiliaryPolynomial_coeff_mul_evalOne_eq_prod_choose
    (μ : Fin N →₀ ℕ) (hμ : ∑ i, μ i = d) :
    ∑ ν : FinPartition N d,
      eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts) *
        coeff μ (partitionPolynomial N ν.parts) =
    ∏ j, ((μ j + N - 1).choose (N - 1) : ℚ) := by
  refine mul_left_cancel₀ (a := (d.factorial : ℚ)) (by positivity) ?_
  rw [factorial_mul_sum_mul_eq_sum_auxiliaryWeightedSums
    (fun ν => eval (fun _ => (1 : ℚ)) (partitionPolynomial N ν.parts))
    (fun ν => coeff μ (partitionPolynomial N ν.parts))]
  simp_rw [← auxiliaryPermutationPolynomial_evalOne_eq_auxiliaryPolynomialSum,
    ← auxiliaryPermutationPolynomial_coeff_eq_auxiliarySum,
    auxiliaryPermutationPolynomial_evalOne_eq_antidiag_coeff_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have step : ∀ β ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d,
      (∑ σ : Equiv.Perm (Fin d),
        coeff β (auxiliaryPermutationPolynomial' N σ) *
          coeff μ (auxiliaryPermutationPolynomial' N σ)) =
      (d.factorial : ℚ) *
        (Fintype.card
          (FinNatFunctionPairAuxiliary N (n := d) (⇑β) (⇑μ)) : ℚ) := by
    intro β hβ
    rw [mem_finsuppAntidiag] at hβ
    have hβsum : ∑ i, β i = d := hβ.1
    rw [sum_coeff_mul_coeff_eq_factorial_mul_auxiliaryPowerSeriesCoeff
        N β μ hβsum hμ,
      auxiliaryPowerSeriesCoeff_eq_card_FinNatFunctionPairAuxiliary
        (N := N) (n := d) (⇑β) (⇑μ) (fun i => by
          have := Finset.single_le_sum (f := (⇑β : Fin N → ℕ))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega)]
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum, ← Nat.cast_sum,
    sum_card_auxiliaryType_eq_prod_choose μ hμ, Nat.cast_prod]

end RepresentationTheory.Combinatorics.AuxiliaryPolynomialSums

/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.MvPowerSeries.AuxiliaryExponentCoefficients
import RepresentationTheory.PermutationPolynomialAuxiliary
import RepresentationTheory.SymmetricPolynomials.Alternant

open Finset Equiv.Perm MvPowerSeries
open RepresentationTheory.LinearAlgebra.AuxiliaryPowerSeriesMatrix
open RepresentationTheory.MvPowerSeries.AuxiliaryExponentCoefficients
open RepresentationTheory.PermutationPolynomialAuxiliary
open RepresentationTheory.SymmetricPolynomials.Alternant

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.emptyLine false

set_option linter.flexible false in
section
namespace RepresentationTheory.Combinatorics.PermutationPowerSeries

variable (N : ℕ)

/-- An auxiliary finitely supported Nat-valued function on the displayed index type associated to two Nat-valued functions. -/
def auxiliaryFinsupp (α β : Fin N → ℕ) : AuxiliaryIndex N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim α β)

/-- The auxiliary finitely supported function evaluated at `Sum.inl i` equals the value of the first Nat-valued function at `i`. -/
@[simp]
theorem auxiliaryFinsupp_apply_inl (α β : Fin N → ℕ) (i : Fin N) :
    auxiliaryFinsupp N α β (Sum.inl i) = α i := by
  simp [auxiliaryFinsupp, Finsupp.equivFunOnFinite]

/-- The auxiliary finitely supported function evaluated at `Sum.inr j` equals the value of the second Nat-valued function at `j`. -/
@[simp]
theorem auxiliaryFinsupp_apply_inr (α β : Fin N → ℕ) (j : Fin N) :
    auxiliaryFinsupp N α β (Sum.inr j) = β j := by
  simp [auxiliaryFinsupp, Finsupp.equivFunOnFinite]

/-- The displayed auxiliary term equals the auxiliary finitely supported function formed from the same Nat-valued function in both arguments. -/
theorem auxiliary_eq_auxiliaryFinsupp_self (α : Fin N → ℕ) :
    auxiliaryExponentIndex N α = auxiliaryFinsupp N α α := by
  ext v; cases v <;> simp [auxiliaryExponentIndex, auxiliaryFinsupp, Finsupp.equivFunOnFinite]

/-- The coefficient of the auxiliary series at the auxiliary finitely supported function equals the signed sum over permutations satisfying the displayed pointwise equality. -/
theorem auxiliarySeries_coeff_auxiliaryFinsupp_eq_signed_permutation_sum (k : Type*) [Field k] [CharZero k]
    (α β : Fin N → ℕ) :
    MvPowerSeries.coeff (R := k) (auxiliaryFinsupp N α β) (auxiliaryDeterminantPowerSeries N k) =
    ∑ σ : Equiv.Perm (Fin N),
      (Int.cast (Equiv.Perm.sign σ : ℤ) : k) *
        if (∀ j : Fin N, α j = β (σ j)) then 1 else 0 := by
  simp only [auxiliaryDeterminantPowerSeries, map_sum]
  congr 1; ext σ
  rw [MvPowerSeries.coeff_C_mul, coeff_prod_invOfUnit_one_sub_X_mul_X_eq_ite N k σ (auxiliaryFinsupp N α β)]
  simp only [auxiliaryFinsupp_apply_inl, auxiliaryFinsupp_apply_inr]

/-- For injective Nat-valued functions that are pointwise equal, the coefficient of the auxiliary series at the auxiliary finitely supported function is one. -/
theorem auxiliarySeries_coeff_auxiliaryFinsupp_eq_one_of_injective_eq (k : Type*) [Field k] [CharZero k]
    (α β : Fin N → ℕ) (_hα : Function.Injective α) (hβ : Function.Injective β)
    (hαβ : ∀ j, α j = β j) :
    MvPowerSeries.coeff (R := k) (auxiliaryFinsupp N α β) (auxiliaryDeterminantPowerSeries N k) = 1 := by
  rw [auxiliarySeries_coeff_auxiliaryFinsupp_eq_signed_permutation_sum]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (if ∀ j, α j = β (σ j) then (1 : k) else 0) =
      if σ = 1 then 1 else 0 := by
    intro σ
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2; ext j
      simp only [Equiv.Perm.coe_one, id_eq]
      exact congr_arg Fin.val (hβ ((hαβ j).symm.trans (h1 j))).symm
    · exfalso; apply h1; intro j; subst h2
      simp only [Equiv.Perm.coe_one, id_eq]; exact hαβ j
    · rfl
  simp_rw [key]
  simp [Finset.sum_ite_eq']

/-- A multivariate power series over a commutative ring on the displayed index type. -/
def auxiliaryPowerSeries (n : ℕ) (k : Type*) [CommRing k] : MvPowerSeries (AuxiliaryIndex n) k :=
  ∏ i : Fin n, ∏ j : Fin n,
    MvPowerSeries.invOfUnit
      (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex n) *
           MvPowerSeries.X (Sum.inr j : AuxiliaryIndex n))
      1

private abbrev xyPairMon (n : ℕ) (i j : Fin n) : AuxiliaryIndex n →₀ ℕ :=
  Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1

@[simp]
private theorem xyPairMon_inl (n : ℕ) (i j : Fin n) (i' : Fin n) :
    xyPairMon n i j (Sum.inl i') = if i = i' then 1 else 0 := by
  simp [xyPairMon, Finsupp.single_apply]

@[simp]
private theorem xyPairMon_inr (n : ℕ) (i j : Fin n) (j' : Fin n) :
    xyPairMon n i j (Sum.inr j') = if j = j' then 1 else 0 := by
  simp [xyPairMon, Finsupp.single_apply]

private def geomTarget (n : ℕ) (i j : Fin n) : MvPowerSeries (AuxiliaryIndex n) ℂ :=
  fun e => if e = e (Sum.inl i) • xyPairMon n i j then 1 else 0

@[simp]
private theorem coeff_geomTarget (n : ℕ) (i j : Fin n) (e : AuxiliaryIndex n →₀ ℕ) :
    MvPowerSeries.coeff e (geomTarget n i j) =
    if e = e (Sum.inl i) • xyPairMon n i j then 1 else 0 := rfl

private theorem xyPairMon_ne_zero (n : ℕ) (i j : Fin n) : xyPairMon n i j ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h (Sum.inl i)
  simp at this

private theorem nsmul_xyPairMon_apply (n : ℕ) (i j : Fin n) (k : ℕ) (v : AuxiliaryIndex n) :
    (k • xyPairMon n i j) v = k * (xyPairMon n i j v) :=
  Finsupp.smul_apply k _ v

private theorem one_sub_xy_mul_geomTarget (n : ℕ) (i j : Fin n) :
    (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex n) *
         MvPowerSeries.X (Sum.inr j : AuxiliaryIndex n) :
      MvPowerSeries (AuxiliaryIndex n) ℂ) * geomTarget n i j = 1 := by
  have hXX : (MvPowerSeries.X (Sum.inl i : AuxiliaryIndex n) *
    MvPowerSeries.X (Sum.inr j : AuxiliaryIndex n) :
      MvPowerSeries (AuxiliaryIndex n) ℂ) =
    MvPowerSeries.monomial (xyPairMon n i j) 1 := by
    simp [xyPairMon, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial]
  ext e
  rw [sub_mul, one_mul, map_sub, hXX, MvPowerSeries.coeff_monomial_mul, one_mul]
  simp only [coeff_geomTarget, MvPowerSeries.coeff_one]
  set m := xyPairMon n i j with hm_def
  have hm_inl : m (Sum.inl i) = 1 := by simp [m]
  have hm_ne_zero : m ≠ 0 := hm_def ▸ xyPairMon_ne_zero n i j

  by_cases h0 : e = 0
  · subst h0

    have hle : ¬(m ≤ 0) := fun h => hm_ne_zero (le_antisymm h zero_le)
    simp only [Finsupp.coe_zero, Pi.zero_apply, zero_smul, ite_true, if_neg hle, sub_zero]

  · rw [if_neg h0]
    by_cases hm : e = e (Sum.inl i) • m
    ·
      have hk : 0 < e (Sum.inl i) := by
        by_contra hle; push Not at hle
        rw [Nat.le_zero.mp hle, zero_smul] at hm; exact h0 hm
      rw [if_pos hm]
      have hle : m ≤ e := by
        rw [hm]; intro v
        simp only [Finsupp.smul_apply, smul_eq_mul]
        exact le_mul_of_one_le_left (Nat.zero_le _) hk
      rw [if_pos hle]
      have hsub : e - m = (e (Sum.inl i) - 1) • m := by
        rw [hm]; ext v
        simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.tsub_apply, hm_inl,
          mul_one, Nat.sub_mul, one_mul]
      have hsub_val : (e - m) (Sum.inl i) = e (Sum.inl i) - 1 := by
        rw [hsub, Finsupp.smul_apply, smul_eq_mul, hm_inl, mul_one]
      rw [hsub_val, if_pos hsub]; ring
    ·
      rw [if_neg hm]
      by_cases hle : m ≤ e
      · rw [if_pos hle]
        have hsub_ne : ¬(e - m = (e - m) (Sum.inl i) • m) := by
          intro hsub; apply hm

          have h1 : e = (e - m) + m := (tsub_add_cancel_of_le hle).symm
          rw [hsub, show (e - m) (Sum.inl i) • m + m =
            ((e - m) (Sum.inl i) + 1) • m from by rw [add_smul, one_smul]] at h1
          have h3 : e (Sum.inl i) = (e - m) (Sum.inl i) + 1 := by
            have := DFunLike.congr_fun h1 (Sum.inl i)
            simp only [Finsupp.smul_apply, smul_eq_mul, hm_inl, mul_one] at this
            exact this
          exact h3.symm ▸ h1
        rw [if_neg hsub_ne]; ring
      · rw [if_neg hle]; ring

private theorem invOfUnit_eq_geomTarget (n : ℕ) (i j : Fin n) :
    MvPowerSeries.invOfUnit
      (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex n) *
           MvPowerSeries.X (Sum.inr j : AuxiliaryIndex n))
      (1 : ℂˣ) =
    geomTarget n i j := by
  have h1 := one_sub_xy_mul_geomTarget n i j
  have hconst : (MvPowerSeries.constantCoeff :
      MvPowerSeries (AuxiliaryIndex n) ℂ →+* ℂ)
      (1 - MvPowerSeries.X (Sum.inl i) * MvPowerSeries.X (Sum.inr j)) = ↑(1 : ℂˣ) := by
    simp [map_sub, map_one, map_mul, MvPowerSeries.constantCoeff_X, Units.val_one]
  have h2 := MvPowerSeries.mul_invOfUnit
    (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex n) *
         MvPowerSeries.X (Sum.inr j : AuxiliaryIndex n)) 1 hconst
  have hU : IsUnit (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex n) *
      MvPowerSeries.X (Sum.inr j : AuxiliaryIndex n) :
        MvPowerSeries (AuxiliaryIndex n) ℂ) :=
    ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  exact hU.mul_left_cancel (h2.trans h1.symm)

/-- The indicated coefficient of the inverse of one minus a product of variables is an equality indicator. -/
theorem coeff_invOfUnit_one_sub_variable_product_eq_indicator (n : ℕ) (i j : Fin n) (e : AuxiliaryIndex n →₀ ℕ) :
    MvPowerSeries.coeff e
      (MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl i : AuxiliaryIndex n) *
             MvPowerSeries.X (Sum.inr j : AuxiliaryIndex n))
        (1 : ℂˣ)) =
    if e = e (Sum.inl i) • xyPairMon n i j then 1 else 0 := by
  rw [invOfUnit_eq_geomTarget]; rfl

/-- An auxiliary type indexed by a natural number and two Nat-valued functions on the corresponding finite type. -/
def FunctionPairIndexedAuxiliary (n : ℕ) (α β : Fin n → ℕ) : Type :=
  { K : Fin n → Fin n → Fin (n + 1) //
    (∀ i, ∑ j, (K i j : ℕ) = α i) ∧ (∀ j, ∑ i, (K i j : ℕ) = β j) }

/-- Provides a `Fintype` structure on each function-pair-indexed auxiliary type. -/
instance functionPairIndexedAuxiliaryFintype (n : ℕ) (α β : Fin n → ℕ) : Fintype (FunctionPairIndexedAuxiliary n α β) :=
  Subtype.fintype _

private theorem fullCauchyProd_eq_prod_pairs (n : ℕ) :
    auxiliaryPowerSeries n ℂ = ∏ p : Fin n × Fin n,
      MvPowerSeries.invOfUnit
        (1 - MvPowerSeries.X (Sum.inl p.1 : AuxiliaryIndex n) *
             MvPowerSeries.X (Sum.inr p.2 : AuxiliaryIndex n))
        (1 : ℂˣ) := by
  change (∏ i : Fin n, ∏ j : Fin n, _) = _
  rw [← Fintype.prod_prod_type']

private def matrixToAntidiag (n : ℕ) (α β : Fin n → ℕ)
    (K : FunctionPairIndexedAuxiliary n α β) :
    (Fin n × Fin n) →₀ (AuxiliaryIndex n →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm (fun p => (K.1 p.1 p.2 : ℕ) • xyPairMon n p.1 p.2)

private lemma matrixToAntidiag_mem (n : ℕ) (α β : Fin n → ℕ)
    (K : FunctionPairIndexedAuxiliary n α β) :
    matrixToAntidiag n α β K ∈
      Finset.univ.finsuppAntidiag (auxiliaryFinsupp n α β) := by
  rw [Finset.mem_finsuppAntidiag]
  refine ⟨?_, Finset.subset_univ _⟩
  have key : ∀ p, (matrixToAntidiag n α β K) p =
      (K.1 p.1 p.2 : ℕ) • xyPairMon n p.1 p.2 := fun p => by
    simp [matrixToAntidiag]
  ext v; cases v with
  | inl i =>
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, key,
      Finsupp.smul_apply, smul_eq_mul, xyPairMon_inl, mul_ite, mul_one, mul_zero,
      auxiliaryFinsupp_apply_inl]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i
      (fun i' _ hi' => by simp [hi']) (fun h => absurd (Finset.mem_univ i) h)]
    simp [K.2.1 i]
  | inr j =>
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, key,
      Finsupp.smul_apply, smul_eq_mul, xyPairMon_inr, mul_ite, mul_one, mul_zero,
      auxiliaryFinsupp_apply_inr]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j
      (fun j' _ hj' => by simp [hj']) (fun h => absurd (Finset.mem_univ j) h)]
    simp [K.2.2 j]

private lemma matrixToAntidiag_valid (n : ℕ) (α β : Fin n → ℕ)
    (K : FunctionPairIndexedAuxiliary n α β) (p : Fin n × Fin n) :
    (matrixToAntidiag n α β K) p =
    ((matrixToAntidiag n α β K) p) (Sum.inl p.1) •
      xyPairMon n p.1 p.2 := by
  simp only [matrixToAntidiag, Finsupp.coe_equivFunOnFinite_symm,
    Finsupp.smul_apply, smul_eq_mul, xyPairMon_inl, ite_true, mul_one]

private lemma extract_row_sum (n : ℕ) (α β : Fin n → ℕ)
    (x : (Fin n × Fin n) →₀ (AuxiliaryIndex n →₀ ℕ))
    (hx_mem : x ∈ Finset.univ.finsuppAntidiag (auxiliaryFinsupp n α β))
    (hx_valid : ∀ p : Fin n × Fin n, x p = (x p) (Sum.inl p.1) • xyPairMon n p.1 p.2)
    (i : Fin n) : ∑ j : Fin n, (x (i, j)) (Sum.inl i) = α i := by
  have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx_mem).1 (Sum.inl i)
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, auxiliaryFinsupp_apply_inl] at h
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i _ _] at h
  · exact h
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun j _ => by
      have := DFunLike.congr_fun (hx_valid (i', j)) (Sum.inl i)
      simp [hi'] at this; exact this
  · exact fun h' => absurd (Finset.mem_univ i) h'

private lemma extract_col_sum (n : ℕ) (α β : Fin n → ℕ)
    (x : (Fin n × Fin n) →₀ (AuxiliaryIndex n →₀ ℕ))
    (hx_mem : x ∈ Finset.univ.finsuppAntidiag (auxiliaryFinsupp n α β))
    (hx_valid : ∀ p : Fin n × Fin n, x p = (x p) (Sum.inl p.1) • xyPairMon n p.1 p.2)
    (j : Fin n) : ∑ i : Fin n, (x (i, j)) (Sum.inl i) = β j := by
  have h := DFunLike.congr_fun (Finset.mem_finsuppAntidiag.mp hx_mem).1 (Sum.inr j)
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, auxiliaryFinsupp_apply_inr] at h
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j _ _] at h
  · rwa [show (∑ i : Fin n, (x (i, j)) (Sum.inr j)) =
        ∑ i : Fin n, (x (i, j)) (Sum.inl i) from
      Finset.sum_congr rfl fun i _ => by
        have := DFunLike.congr_fun (hx_valid (i, j)) (Sum.inr j)
        simp at this; exact this] at h
  · intro j' _ hj'
    exact Finset.sum_eq_zero fun i _ => by
      have := DFunLike.congr_fun (hx_valid (i, j')) (Sum.inr j)
      simp [hj'] at this; exact this
  · exact fun h' => absurd (Finset.mem_univ j) h'

private def antidiagToMatrix (n : ℕ) (α β : Fin n → ℕ) (hα : ∀ i, α i ≤ n)
    (x : (Fin n × Fin n) →₀ (AuxiliaryIndex n →₀ ℕ))
    (hrow : ∀ i, ∑ j : Fin n, (x (i, j)) (Sum.inl i) = α i)
    (hcol : ∀ j, ∑ i : Fin n, (x (i, j)) (Sum.inl i) = β j) :
    FunctionPairIndexedAuxiliary n α β :=
  ⟨fun i j => ⟨(x (i, j)) (Sum.inl i),
    Nat.lt_succ_of_le ((hrow i ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans (hα i))⟩,
   hrow, hcol⟩

/-- When every value of the first Nat-valued function is at most `n`, the coefficient indexed by the auxiliary finitely supported function in the auxiliary power series equals the cardinality of the function-pair-indexed auxiliary type. -/
theorem auxiliaryPowerSeries_coeff_auxiliaryFinsupp_eq_card_functionPairIndexedAuxiliary_of_le (n : ℕ) (α β : Fin n → ℕ)
    (hα : ∀ i, α i ≤ n) :
    MvPowerSeries.coeff (auxiliaryFinsupp n α β) (auxiliaryPowerSeries n ℂ) =
    ↑(Fintype.card (FunctionPairIndexedAuxiliary n α β)) := by
  rw [fullCauchyProd_eq_prod_pairs]
  simp_rw [invOfUnit_eq_geomTarget]
  rw [MvPowerSeries.coeff_prod]
  simp_rw [coeff_geomTarget, Finset.prod_boole, Finset.mem_univ, forall_true_left,
    Finset.sum_boole]
  norm_cast

  change #_ = #(Finset.univ : Finset (FunctionPairIndexedAuxiliary n α β))
  apply Finset.card_bij'
    (fun x hx =>
      antidiagToMatrix n α β hα x
        (extract_row_sum n α β x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
        (extract_col_sum n α β x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2))
    (fun K _ => matrixToAntidiag n α β K)
    (fun _ _ => Finset.mem_univ _)
    (fun K _ => Finset.mem_filter.mpr
      ⟨matrixToAntidiag_mem n α β K, matrixToAntidiag_valid n α β K⟩)
    (fun x hx => by
      apply DFunLike.ext; intro ⟨i, j⟩
      simp only [matrixToAntidiag, antidiagToMatrix, Finsupp.coe_equivFunOnFinite_symm]
      exact ((Finset.mem_filter.mp hx).2 (i, j)).symm)
    (fun K _ => by
      refine Subtype.ext (funext fun i => funext fun j => Fin.ext ?_)
      simp [antidiagToMatrix, matrixToAntidiag])

/-- An auxiliary type indexed by a natural number, a finitely supported Nat-valued function on the corresponding finite type, and a permutation of that finite type. -/
def PermutationIndexedAuxiliary (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  { f : Fin (permutationNatMultiset n σ).toList.length → Fin n //
    ∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => ((permutationNatMultiset n σ).toList[↑i])) = α j }

/-- Provides a `Fintype` structure on each permutation-indexed auxiliary type. -/
instance permutationIndexedAuxiliaryFintype (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (PermutationIndexedAuxiliary n α σ) := by
  unfold PermutationIndexedAuxiliary
  exact Subtype.fintype _

private lemma finsupp_sum_single_iff' (n : ℕ) (α : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin (permutationNatMultiset n σ).toList.length → Fin n) :
    (∑ i, Finsupp.single (f i) ((permutationNatMultiset n σ).toList[(↑i : ℕ)]) = α) ↔
    (∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => (permutationNatMultiset n σ).toList[(↑i : ℕ)]) = α j) := by
  constructor
  · intro heq j
    have hj := DFunLike.congr_fun heq j
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply] at hj
    rw [← hj, Finset.sum_filter]
  · intro hall
    ext j
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [← Finset.sum_filter]
    exact hall j

/-- The coefficient of the displayed auxiliary polynomial is the cardinality of the corresponding permutation-indexed auxiliary type. -/
theorem auxiliaryPolynomial_coeff_eq_card_permutationIndexedAuxiliary (n : ℕ) (α : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff α (permutationPolynomialAuxiliary n σ) =
    ↑(Fintype.card (PermutationIndexedAuxiliary n α σ)) := by
  rw [permutationPolynomialAuxiliary_eq_prod_psum]
  rw [← Multiset.prod_map_toList, ← List.ofFn_getElem_eq_map, List.prod_ofFn]
  simp_rw [psum_eq_sum_monomial_single]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_one]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial, Finset.sum_boole, Fintype.piFinset_univ]
  norm_cast



  have equiv : PermutationIndexedAuxiliary n α σ ≃
      { f : Fin (permutationNatMultiset n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((permutationNatMultiset n σ).toList[(↑i : ℕ)])) = α } := by
    unfold PermutationIndexedAuxiliary
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun f => (finsupp_sum_single_iff' n α σ f).symm)
  rw [show Fintype.card (PermutationIndexedAuxiliary n α σ) = Fintype.card
      { f : Fin (permutationNatMultiset n σ).toList.length → Fin n //
        (∑ i, Finsupp.single (f i) ((permutationNatMultiset n σ).toList[(↑i : ℕ)])) = α }
    from Fintype.card_congr equiv]
  simp only [Fintype.card_subtype, Finset.card_filter]

private def ElemBicol (n : ℕ) (α β : Fin n →₀ ℕ) : Type :=
  { h : Fin n → Fin n × Fin n //
    (∀ i : Fin n, (Finset.univ.filter fun x => (h x).1 = i).card = α i) ∧
    (∀ j : Fin n, (Finset.univ.filter fun x => (h x).2 = j).card = β j) }

private instance (n : ℕ) (α β : Fin n →₀ ℕ) : Fintype (ElemBicol n α β) :=
  Subtype.fintype _

private def FiberPerm {n : ℕ} (h : Fin n → Fin n × Fin n) : Type :=
  { σ : Equiv.Perm (Fin n) // ∀ x, h (σ x) = h x }

private instance {n : ℕ} (h : Fin n → Fin n × Fin n) : Fintype (FiberPerm h) :=
  Subtype.fintype _

private def cycleColToBicol (n : ℕ) (α β : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : PermutationIndexedAuxiliary n α σ × PermutationIndexedAuxiliary n β σ) :
    ElemBicol n α β :=
  let π := (exists_sameCycle_class_indexing σ).choose
  have hπ := (exists_sameCycle_class_indexing σ).choose_spec
  ⟨fun x => (fg.1.val (π x), fg.2.val (π x)),
   ⟨fun i => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.1.val (π x) = i) =
          (Finset.univ.filter fun j => fg.1.val j = i).biUnion
            (fun j => Finset.univ.filter fun x => π x = j) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨j, hj, hjx⟩ => hjx ▸ hj⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext j; rw [hπ.2 j]
      exact fg.1.prop i,
    fun j => by
      rw [show (Finset.univ.filter fun x : Fin n => fg.2.val (π x) = j) =
          (Finset.univ.filter fun k => fg.2.val k = j).biUnion
            (fun k => Finset.univ.filter fun x => π x = k) from by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        exact ⟨fun h => ⟨π x, h, rfl⟩, fun ⟨k, hk, hkx⟩ => hkx ▸ hk⟩]
      rw [Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
        Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hij (h₁ ▸ h₂)))]
      conv_lhs => arg 2; ext k; rw [hπ.2 k]
      exact fg.2.prop j⟩⟩

private lemma cycleColToBicol_compat (n : ℕ) (α β : Fin n →₀ ℕ)
    (σ : Equiv.Perm (Fin n)) (fg : PermutationIndexedAuxiliary n α σ × PermutationIndexedAuxiliary n β σ) :
    ∀ x, (cycleColToBicol n α β σ fg).val (σ x) = (cycleColToBicol n α β σ fg).val x := by
  intro x
  simp only [cycleColToBicol]
  let π := (exists_sameCycle_class_indexing σ).choose
  have hπ := (exists_sameCycle_class_indexing σ).choose_spec
  change (fg.1.val (π (σ x)), fg.2.val (π (σ x))) = (fg.1.val (π x), fg.2.val (π x))
  have hkey : π (σ x) = π x := (hπ.1 (σ x) x).mpr ⟨-1, by simp⟩
  rw [hkey]

private lemma card_sigma_CycleCol_eq_card_sigma_fiberPerm (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ σ : Equiv.Perm (Fin n), PermutationIndexedAuxiliary n α σ × PermutationIndexedAuxiliary n β σ) =
    Fintype.card (Σ hb : ElemBicol n α β, FiberPerm hb.val) := by
  classical



  apply Fintype.card_congr
  exact {
    toFun := fun ⟨σ, fg⟩ =>
      ⟨cycleColToBicol n α β σ fg,
       ⟨σ, cycleColToBicol_compat n α β σ fg⟩⟩
    invFun := fun p =>

      let h := p.1.val
      let hrow := p.1.property.1
      let hcol := p.1.property.2
      let σ := p.2.val
      let hcompat : ∀ x, h (σ x) = h x := p.2.property
      let π := (exists_sameCycle_class_indexing σ).choose
      have hπ := (exists_sameCycle_class_indexing σ).choose_spec
      have hne : ∀ i : Fin (permutationNatMultiset n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := permutationNatMultiset_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      let rep := fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)
      have hrep : ∀ i, π (rep i) = i := fun i =>
        (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hc : ∀ x, h (σ x) = h x := hcompat
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih => intro y; rw [pow_succ, Equiv.Perm.mul_apply, ih, hc]
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)
      ⟨σ,
        ⟨fun i => (h (rep i)).1, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).1 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).1 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).1 = j) by rw [heq]; exact hrow j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩,
        ⟨fun i => (h (rep i)).2, fun j => by
          dsimp only
          trans (Finset.univ.filter (fun i => (h (rep i)).2 = j)).sum
            (fun i => (Finset.univ.filter (fun k : Fin n => π k = i)).card)
          · exact Finset.sum_congr rfl (fun i _ => (hπ.2 i).symm)
          rw [← Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hij =>
            Finset.disjoint_filter.mpr (fun k _ h₁ h₂ => hij (h₁ ▸ h₂)))]
          suffices heq : (Finset.univ.filter (fun i => (h (rep i)).2 = j)).biUnion
              (fun i => Finset.univ.filter (fun k : Fin n => π k = i)) =
              Finset.univ.filter (fun x => (h x).2 = j) by rw [heq]; exact hcol j
          ext k; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, hk⟩
            rw [← hk] at hi; rwa [hconst _ _ (hrep (π k))] at hi
          · intro hk; exact ⟨π k, by rwa [← hconst k (rep (π k)) (hrep (π k)).symm], rfl⟩⟩⟩
    left_inv := fun ⟨σ, fg⟩ => by

      let π := (exists_sameCycle_class_indexing σ).choose
      have hπ := (exists_sameCycle_class_indexing σ).choose_spec
      have hne : ∀ i : Fin (permutationNatMultiset n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := permutationNatMultiset_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2


      refine Sigma.ext rfl (heq_of_eq ?_)
      simp only [cycleColToBicol]
      apply Prod.ext
      · apply Subtype.ext; funext i; exact congrArg fg.1.val (hrep i)
      · apply Subtype.ext; funext i; exact congrArg fg.2.val (hrep i)
    right_inv := fun ⟨⟨h, hrow, hcol⟩, ⟨σ, hcompat⟩⟩ => by
      simp only [cycleColToBicol]
      let π := (exists_sameCycle_class_indexing σ).choose
      have hπ := (exists_sameCycle_class_indexing σ).choose_spec
      have hne : ∀ i : Fin (permutationNatMultiset n σ).toList.length,
          (Finset.univ.filter (fun k : Fin n => π k = i)).Nonempty := by
        intro i; by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have h1 := hπ.2 i; rw [hemp, Finset.card_empty] at h1
        have h2 := permutationNatMultiset_pos σ _ (Multiset.mem_toList.mp (List.getElem_mem i.isLt))
        omega
      have hrep : ∀ i, π ((Finset.univ.filter (fun k : Fin n => π k = i)).min' (hne i)) = i :=
        fun i => (Finset.mem_filter.mp (Finset.min'_mem _ (hne i))).2
      have hc : ∀ x, h (σ x) = h x := hcompat
      have hiter : ∀ (m : ℕ) (y : Fin n), h ((σ ^ m) y) = h y := by
        intro m; induction m with
        | zero => intro y; simp
        | succ m ih =>
          intro y; rw [pow_succ, Equiv.Perm.mul_apply, ih, hc]
      have hconst : ∀ k₁ k₂, π k₁ = π k₂ → h k₁ = h k₂ := by
        intro k₁ k₂ hk
        obtain ⟨m, -, hm⟩ := ((hπ.1 k₁ k₂).mp hk).exists_pow_eq'
        exact (hiter m k₁).symm.trans (congrArg h hm)

      ext1
      ·
        apply Subtype.ext; funext x
        have key := hconst _ x (hrep (π x))
        simp only [Prod.mk.eta]; exact key
      ·
        rfl
  }

private lemma filter_card_comp_perm {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun x => P (σ x))).card = (Finset.univ.filter P).card := by
  apply Finset.card_bij' (fun x _ => σ x) (fun x _ => σ⁻¹ x)
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    convert hx using 1; simp
  · intro x _; simp
  · intro x _; simp

private noncomputable def permSmulElemBicol {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) : ElemBicol n α β :=
  ⟨hb.val ∘ ⇑σ⁻¹, by
    constructor
    · intro i
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).1 = i)).card =
          (Finset.univ.filter (fun x => (hb.val x).1 = i)).card :=
        filter_card_comp_perm (fun x => (hb.val x).1 = i) σ⁻¹
      rw [h1]; exact hb.2.1 i
    · intro j
      have h1 : (Finset.univ.filter (fun x => ((hb.val ∘ ⇑σ⁻¹) x).2 = j)).card =
          (Finset.univ.filter (fun x => (hb.val x).2 = j)).card :=
        filter_card_comp_perm (fun x => (hb.val x).2 = j) σ⁻¹
      rw [h1]; exact hb.2.2 j⟩

@[simp]
private lemma permSmulElemBicol_val {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) :
    (permSmulElemBicol σ hb).val = hb.val ∘ ⇑σ⁻¹ := rfl

private noncomputable instance permMulActionElemBicol {n : ℕ} {α β : Fin n →₀ ℕ} :
    MulAction (Equiv.Perm (Fin n)) (ElemBicol n α β) where
  smul := permSmulElemBicol
  one_smul hb := Subtype.ext (funext fun _ => by
    change (permSmulElemBicol 1 hb).val _ = hb.val _
    simp [permSmulElemBicol_val, Function.comp])
  mul_smul σ τ hb := Subtype.ext (funext fun x => by
    change (permSmulElemBicol (σ * τ) hb).val x = (permSmulElemBicol σ (permSmulElemBicol τ hb)).val x
    simp [permSmulElemBicol_val, Function.comp, mul_inv_rev, Equiv.Perm.mul_apply])

private lemma mem_stabilizer_iff_fiberPerm {n : ℕ} {α β : Fin n →₀ ℕ}
    (hb : ElemBicol n α β) (σ : Equiv.Perm (Fin n)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) hb ↔ ∀ x, hb.val (σ x) = hb.val x := by
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    have h1 := congr_arg Subtype.val h
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicol_val σ hb] at h1
    have := congr_fun h1 (σ x)
    simp at this; exact this.symm
  · intro h
    apply Subtype.ext
    rw [show (σ • hb).val = hb.val ∘ ⇑σ⁻¹ from permSmulElemBicol_val σ hb]
    funext x
    have := h (σ⁻¹ x)
    simp at this; exact this.symm

private noncomputable def fiberSizes {n : ℕ} {α β : Fin n →₀ ℕ}
    (hb : ElemBicol n α β) : FunctionPairIndexedAuxiliary n (⇑α) (⇑β) :=
  ⟨fun i j => ⟨(Finset.univ.filter fun x => hb.val x = (i, j)).card,
    Nat.lt_succ_of_le <| (Finset.card_filter_le _ _).trans <| by simp [Fintype.card_fin]⟩,
   fun i => by
     simp only [Fin.val_natCast]
     rw [← hb.2.1 i]
     rw [← Finset.card_biUnion (fun j₁ _ j₂ _ hj =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hj (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.2)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨j, ⟨h1, h2⟩⟩ => h1, fun h => ⟨(hb.val x).2, ⟨h, rfl⟩⟩⟩,
   fun j => by
     simp only [Fin.val_natCast]
     rw [← hb.2.2 j]
     rw [← Finset.card_biUnion (fun i₁ _ i₂ _ hi =>
       Finset.disjoint_filter.mpr (fun x _ h₁ h₂ => hi (by
         have := h₁.symm.trans h₂; exact Prod.ext_iff.mp this |>.1)))]
     congr 1; ext x
     simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
     exact ⟨fun ⟨i, ⟨h1, h2⟩⟩ => h2, fun h => ⟨(hb.val x).1, ⟨rfl, h⟩⟩⟩⟩

@[simp]
private lemma smul_val {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) :
    (σ • hb).val = hb.val ∘ ⇑σ⁻¹ :=
  permSmulElemBicol_val σ hb

private lemma filter_card_comp_equiv {α' β' : Type*} [Fintype α'] [Fintype β']
    (e : α' ≃ β') (P : β' → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x => P (e x))).card = (Finset.univ.filter P).card := by
  apply Finset.card_bij' (fun x _ => e x) (fun y _ => e.symm y)
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx
  · intro y hy; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    convert hy using 1; simp
  · intro x _; simp
  · intro y _; simp

private lemma fiberSizes_smul_eq {n : ℕ} {α β : Fin n →₀ ℕ}
    (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) :
    fiberSizes (σ • hb) = fiberSizes hb := by
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizes, smul_val]
  exact filter_card_comp_perm (fun x => hb.val x = (i, j)) σ⁻¹

private lemma same_fiberSizes_same_orbit {n : ℕ} {α β : Fin n →₀ ℕ}
    (h₁ h₂ : ElemBicol n α β) (heq : fiberSizes h₁ = fiberSizes h₂) :
    h₁ ∈ MulAction.orbit (Equiv.Perm (Fin n)) h₂ := by
  classical

  have hcard : ∀ p : Fin n × Fin n,
      Fintype.card { x // h₁.val x = p } = Fintype.card { x // h₂.val x = p } := by
    intro ⟨i, j⟩
    simp only [Fintype.card_subtype, Finset.card_filter]
    have := congr_arg (fun K => (K.1 i j : ℕ)) heq
    simpa [fiberSizes] using this

  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofFiberEquiv (f := h₁.val) (g := h₂.val)
      (fun p => Fintype.equivOfCardEq (hcard p))

  have hσ : ∀ x, h₂.val (σ x) = h₁.val x := Equiv.ofFiberEquiv_map _

  refine ⟨σ⁻¹, Subtype.ext (funext fun x => ?_)⟩
  simp only [smul_val, Function.comp, inv_inv]
  exact hσ x

private lemma sigma_filter_fst_card {n : ℕ} (K : Fin n → Fin n → ℕ) (i : Fin n) :
    (Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1.1 = i)).card = ∑ j, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ j, K i j = Fintype.card (Σ j : Fin n, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i', j⟩, k⟩, (hi : i' = i)⟩ => ⟨j, hi ▸ k⟩
    invFun := fun ⟨j, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i', j⟩, k⟩, hi⟩ => by subst hi; rfl
    right_inv := fun ⟨j, k⟩ => rfl }

private lemma sigma_filter_snd_card {n : ℕ} (K : Fin n → Fin n → ℕ) (j : Fin n) :
    (Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1.2 = j)).card = ∑ i, K i j := by
  rw [← Fintype.card_subtype,
      show ∑ i, K i j = Fintype.card (Σ i : Fin n, Fin (K i j)) from
        by simp [Fintype.card_sigma, Fintype.card_fin]]
  exact Fintype.card_congr {
    toFun := fun ⟨⟨⟨i, j'⟩, k⟩, (hj : j' = j)⟩ => ⟨i, hj ▸ k⟩
    invFun := fun ⟨i, k⟩ => ⟨⟨(i, j), k⟩, rfl⟩
    left_inv := fun ⟨⟨⟨i, j'⟩, k⟩, hj⟩ => by subst hj; rfl
    right_inv := fun ⟨i, k⟩ => rfl }

private lemma sigma_filter_pair_card {n : ℕ} (K : Fin n → Fin n → ℕ) (i j : Fin n) :
    (Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j))).card = K i j := by
  have : Finset.univ.filter (fun (s : Σ ij : Fin n × Fin n, Fin (K ij.1 ij.2)) =>
      s.1 = (i, j)) =
    (Finset.univ : Finset (Fin (K i j))).map
      ⟨fun k => ⟨(i, j), k⟩, fun k₁ k₂ h => by simpa using h⟩ := by
    ext ⟨⟨i', j'⟩, k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨k, rfl⟩
    · rintro ⟨k', hk'⟩; exact (congr_arg Sigma.fst hk').symm
  rw [this, Finset.card_map, Finset.card_fin]

private noncomputable def elemBicolOfMatrix_equiv {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : FunctionPairIndexedAuxiliary n (⇑α) (⇑β)) :
    Fin n ≃ (Σ ij : Fin n × Fin n, Fin (K.1 ij.1 ij.2 : ℕ)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.sum_prod_type]
    simp_rw [K.2.1]; rw [hα])

private noncomputable def elemBicolOfMatrix {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : FunctionPairIndexedAuxiliary n (⇑α) (⇑β)) :
    ElemBicol n α β :=
  ⟨fun x => (elemBicolOfMatrix_equiv hα K x).1,
   ⟨fun i => by
      classical
      rw [filter_card_comp_equiv (elemBicolOfMatrix_equiv hα K) (fun s => s.1.1 = i)]
      rw [sigma_filter_fst_card (fun i j => (K.1 i j : ℕ)) i]
      exact K.2.1 i,
    fun j => by
      classical
      rw [filter_card_comp_equiv (elemBicolOfMatrix_equiv hα K) (fun s => s.1.2 = j)]
      rw [sigma_filter_snd_card (fun i j => (K.1 i j : ℕ)) j]
      exact K.2.2 j⟩⟩

@[simp]
private lemma elemBicolOfMatrix_val {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : FunctionPairIndexedAuxiliary n (⇑α) (⇑β)) :
    (elemBicolOfMatrix hα K).val = fun x => (elemBicolOfMatrix_equiv hα K x).1 := rfl

private lemma fiberSizes_elemBicolOfMatrix {n : ℕ} {α β : Fin n →₀ ℕ}
    (hα : ∑ i, α i = n) (K : FunctionPairIndexedAuxiliary n (⇑α) (⇑β)) :
    fiberSizes (elemBicolOfMatrix hα K) = K := by
  classical
  apply Subtype.ext; funext i; funext j; apply Fin.ext
  simp only [fiberSizes, elemBicolOfMatrix_val]
  rw [filter_card_comp_equiv (elemBicolOfMatrix_equiv hα K) (fun s => s.1 = (i, j))]
  exact sigma_filter_pair_card (fun i j => (K.1 i j : ℕ)) i j

private lemma card_sigma_fiberPerm_eq_factorial_mul (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Σ hb : ElemBicol n α β, FiberPerm hb.val) =
    n.factorial * Fintype.card (FunctionPairIndexedAuxiliary n (⇑α) (⇑β)) := by
  classical

  have step1 : Fintype.card (Σ hb : ElemBicol n α β, FiberPerm hb.val) =
      Fintype.card (Σ hb : ElemBicol n α β,
        MulAction.stabilizer (Equiv.Perm (Fin n)) hb) := by
    apply Fintype.card_congr
    exact Equiv.sigmaCongrRight (fun hb =>
      Equiv.subtypeEquiv (Equiv.refl _) (fun σ =>
        (mem_stabilizer_iff_fiberPerm hb σ).symm))
  rw [step1]

  have step2 : Fintype.card (Σ hb : ElemBicol n α β,
      MulAction.stabilizer (Equiv.Perm (Fin n)) hb) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n),
      MulAction.fixedBy (ElemBicol n α β) σ) := by
    apply Fintype.card_congr
    calc (Σ hb : ElemBicol n α β, MulAction.stabilizer (Equiv.Perm (Fin n)) hb)
      ≃ { p : ElemBicol n α β × Equiv.Perm (Fin n) // p.2 ∈ MulAction.stabilizer _ p.1 } :=
        (Equiv.subtypeProdEquivSigmaSubtype
          (fun (hb : ElemBicol n α β) (σ : Equiv.Perm (Fin n)) =>
            σ ∈ MulAction.stabilizer _ hb)).symm
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicol n α β // p.1 ∈ MulAction.stabilizer _ p.2 } :=
        (Equiv.prodComm _ _).subtypeEquiv (fun ⟨hb, σ⟩ => Iff.rfl)
      _ ≃ { p : Equiv.Perm (Fin n) × ElemBicol n α β // p.2 ∈ MulAction.fixedBy _ p.1 } :=
        Equiv.subtypeEquivRight (fun ⟨σ, hb⟩ => by
          simp [MulAction.mem_stabilizer_iff, MulAction.mem_fixedBy])
      _ ≃ (Σ σ : Equiv.Perm (Fin n), MulAction.fixedBy (ElemBicol n α β) σ) :=
        Equiv.subtypeProdEquivSigmaSubtype
          (fun (σ : Equiv.Perm (Fin n)) (hb : ElemBicol n α β) =>
            hb ∈ MulAction.fixedBy _ σ)
  rw [step2]

  rw [show Fintype.card (Σ σ : Equiv.Perm (Fin n), MulAction.fixedBy (ElemBicol n α β) σ) =
    ∑ σ : Equiv.Perm (Fin n), Fintype.card (MulAction.fixedBy (ElemBicol n α β) σ) from
    Fintype.card_sigma]
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  rw [Fintype.card_perm, Fintype.card_fin]

  rw [mul_comm]
  congr 1

  apply Fintype.card_congr
  letI := MulAction.orbitRel (Equiv.Perm (Fin n)) (ElemBicol n α β)
  exact Equiv.ofBijective
    (Quotient.lift fiberSizes (fun a b (hab : a ∈ MulAction.orbit _ b) => by
      obtain ⟨g, rfl⟩ := hab; exact fiberSizes_smul_eq g b))
    ⟨fun q₁ q₂ => Quotient.inductionOn₂ q₁ q₂ (fun a b heq =>
        Quotient.sound (same_fiberSizes_same_orbit a b heq)),
     fun K => ⟨Quotient.mk' (elemBicolOfMatrix hα K),
              fiberSizes_elemBicolOfMatrix hα K⟩⟩

/-- If each of two finitely supported Nat-valued functions has total sum equal to `n`, the sum of products of cardinalities of their permutation-indexed auxiliary types equals `n!` times the cardinality of their function-pair-indexed auxiliary type. -/
theorem sum_card_permutationIndexedAuxiliary_mul_eq_factorial_mul_card_functionPairIndexedAuxiliary (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (PermutationIndexedAuxiliary n α σ) * Fintype.card (PermutationIndexedAuxiliary n β σ) =
    n.factorial * Fintype.card (FunctionPairIndexedAuxiliary n (⇑α) (⇑β)) := by

  have h1 : ∑ σ : Equiv.Perm (Fin n),
      Fintype.card (PermutationIndexedAuxiliary n α σ) * Fintype.card (PermutationIndexedAuxiliary n β σ) =
    Fintype.card (Σ σ : Equiv.Perm (Fin n), PermutationIndexedAuxiliary n α σ × PermutationIndexedAuxiliary n β σ) := by
    simp_rw [← Fintype.card_prod]; exact Fintype.card_sigma.symm
  rw [h1]

  rw [card_sigma_CycleCol_eq_card_sigma_fiberPerm n α β hα hβ]
  exact card_sigma_fiberPerm_eq_factorial_mul n α β hα hβ

/-- If each of two finitely supported Nat-valued functions has total sum equal to `n`, the sum of products of the indicated auxiliary-polynomial coefficients equals `n!` times the auxiliary-Finsupp-indexed coefficient in the auxiliary power series. -/
theorem sum_auxiliaryPolynomial_coeff_mul_eq_factorial_mul_auxiliaryPowerSeries_coeff_auxiliaryFinsupp (n : ℕ) (α β : Fin n →₀ ℕ)
    (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (MvPolynomial.coeff α (permutationPolynomialAuxiliary n σ) : ℂ) *
      (MvPolynomial.coeff β (permutationPolynomialAuxiliary n σ) : ℂ)) =
    (Nat.factorial n : ℂ) * MvPowerSeries.coeff (auxiliaryFinsupp n α β)
      (auxiliaryPowerSeries n ℂ) := by

  simp_rw [auxiliaryPolynomial_coeff_eq_card_permutationIndexedAuxiliary]

  have hα' : ∀ i, (α : Fin n → ℕ) i ≤ n := by
    intro i
    have := Finset.single_le_sum (f := (⇑α : Fin n → ℕ)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega
  rw [auxiliaryPowerSeries_coeff_auxiliaryFinsupp_eq_card_functionPairIndexedAuxiliary_of_le n (⇑α) (⇑β) hα']

  simp only [← Nat.cast_mul, ← Nat.cast_sum]
  congr 1
  exact sum_card_permutationIndexedAuxiliary_mul_eq_factorial_mul_card_functionPairIndexedAuxiliary n α β hα hβ

private def permExponentX (N : ℕ) (π : Equiv.Perm (Fin N)) : AuxiliaryIndex N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => (π⁻¹ i).val) (fun _ => 0))

private def permExponentY (N : ℕ) (τ : Equiv.Perm (Fin N)) : AuxiliaryIndex N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun _ => 0) (fun j => (τ⁻¹ j).val))

@[simp]
private theorem permExponentX_inl (N : ℕ) (π : Equiv.Perm (Fin N)) (i : Fin N) :
    permExponentX N π (Sum.inl i) = (π⁻¹ i).val := by
  simp [permExponentX, Finsupp.equivFunOnFinite]

@[simp]
private theorem permExponentX_inr (N : ℕ) (π : Equiv.Perm (Fin N)) (j : Fin N) :
    permExponentX N π (Sum.inr j) = 0 := by
  simp [permExponentX, Finsupp.equivFunOnFinite]

@[simp]
private theorem permExponentY_inl (N : ℕ) (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    permExponentY N τ (Sum.inl i) = 0 := by
  simp [permExponentY, Finsupp.equivFunOnFinite]

@[simp]
private theorem permExponentY_inr (N : ℕ) (τ : Equiv.Perm (Fin N)) (j : Fin N) :
    permExponentY N τ (Sum.inr j) = (τ⁻¹ j).val := by
  simp [permExponentY, Finsupp.equivFunOnFinite]

private noncomputable def vandermondeFPS_x (N : ℕ) : MvPowerSeries (AuxiliaryIndex N) ℂ :=
  ∑ π : Equiv.Perm (Fin N),
    ((Equiv.Perm.sign π : ℤ) : ℂ) • MvPowerSeries.monomial (permExponentX N π) 1

private noncomputable def vandermondeFPS_y (N : ℕ) : MvPowerSeries (AuxiliaryIndex N) ℂ :=
  ∑ τ : Equiv.Perm (Fin N),
    ((Equiv.Perm.sign τ : ℤ) : ℂ) • MvPowerSeries.monomial (permExponentY N τ) 1

private theorem permExponentXY_add (N : ℕ) (π τ : Equiv.Perm (Fin N)) :
    permExponentX N π + permExponentY N τ =
    auxiliaryFinsupp N (fun i => (π⁻¹ i).val) (fun j => (τ⁻¹ j).val) := by
  ext v; cases v <;> simp [auxiliaryFinsupp, Finsupp.equivFunOnFinite]

private theorem bilinExponent_sub_permExponentX (N : ℕ) (α β : Fin N → ℕ)
    (π : Equiv.Perm (Fin N)) (h : ∀ i, (π⁻¹ i : Fin N).val ≤ α i) :
    auxiliaryFinsupp N α β - permExponentX N π =
    auxiliaryFinsupp N (fun i => α i - (π⁻¹ i).val) β := by
  ext v; cases v with
  | inl i => simp [auxiliaryFinsupp, permExponentX, Finsupp.equivFunOnFinite]
  | inr j => simp [auxiliaryFinsupp, permExponentX, Finsupp.equivFunOnFinite]

private theorem permExponentX_le_bilinExponent_iff (N : ℕ) (α β : Fin N → ℕ)
    (π : Equiv.Perm (Fin N)) :
    permExponentX N π ≤ auxiliaryFinsupp N α β ↔ ∀ i, (π⁻¹ i : Fin N).val ≤ α i := by
  constructor
  · intro h i
    have := h (Sum.inl i)
    simp at this
    exact this
  · intro h v; cases v with
    | inl i => exact h i
    | inr j => simp

private theorem permExponentY_le_bilinExponent_iff (N : ℕ) (α' β : Fin N → ℕ)
    (τ : Equiv.Perm (Fin N)) :
    permExponentY N τ ≤ auxiliaryFinsupp N α' β ↔ ∀ j, (τ⁻¹ j : Fin N).val ≤ β j := by
  constructor
  · intro h j
    have := h (Sum.inr j)
    simp at this
    exact this
  · intro h v; cases v with
    | inl i => simp
    | inr j => exact h j

private theorem bilinExponent_sub_permExponentY (N : ℕ) (α' β : Fin N → ℕ)
    (τ : Equiv.Perm (Fin N)) (_h : ∀ j, (τ⁻¹ j : Fin N).val ≤ β j) :
    auxiliaryFinsupp N α' β - permExponentY N τ =
    auxiliaryFinsupp N α' (fun j => β j - (τ⁻¹ j).val) := by
  ext v; cases v with
  | inl i => simp [auxiliaryFinsupp, permExponentY, Finsupp.equivFunOnFinite]
  | inr j =>
    simp only [auxiliaryFinsupp, permExponentY, Finsupp.equivFunOnFinite, Finsupp.tsub_apply]
    simp

private abbrev xVar (N : ℕ) (i : Fin N) : MvPowerSeries (AuxiliaryIndex N) ℂ :=
  MvPowerSeries.X (Sum.inl i)

private abbrev yVar (N : ℕ) (j : Fin N) : MvPowerSeries (AuxiliaryIndex N) ℂ :=
  MvPowerSeries.X (Sum.inr j)

private noncomputable def denomProd (N : ℕ) : MvPowerSeries (AuxiliaryIndex N) ℂ :=
  ∏ i : Fin N, ∏ j : Fin N, (1 - xVar N i * yVar N j)

private theorem one_sub_xy_mul_invOfUnit (N : ℕ) (i j : Fin N) :
    (1 - xVar N i * yVar N j) *
      MvPowerSeries.invOfUnit (1 - xVar N i * yVar N j) (1 : ℂˣ) = 1 := by
  have hconst : (MvPowerSeries.constantCoeff :
      MvPowerSeries (AuxiliaryIndex N) ℂ →+* ℂ)
      (1 - xVar N i * yVar N j) = ↑(1 : ℂˣ) := by
    simp [xVar, yVar, map_sub, map_one, map_mul, MvPowerSeries.constantCoeff_X, Units.val_one]
  exact MvPowerSeries.mul_invOfUnit _ _ hconst

private theorem denomProd_mul_fullCauchyProd (N : ℕ) :
    denomProd N * auxiliaryPowerSeries N ℂ = 1 := by
  simp only [denomProd, auxiliaryPowerSeries, Finset.prod_mul_distrib.symm]
  rw [show (∏ i : Fin N, ∏ j : Fin N,
      ((1 - xVar N i * yVar N j) *
        MvPowerSeries.invOfUnit (1 - xVar N i * yVar N j) (1 : ℂˣ))) =
    ∏ i : Fin N, ∏ j : Fin N, (1 : MvPowerSeries (AuxiliaryIndex N) ℂ) from
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ =>
      one_sub_xy_mul_invOfUnit N i j]
  simp

private noncomputable def clearedDenomMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPowerSeries (AuxiliaryIndex N) ℂ) :=
  Matrix.of fun i j => ∏ k ∈ Finset.univ.erase j, (1 - xVar N i * yVar N k)

private noncomputable def rowProd (N : ℕ) (i : Fin N) : MvPowerSeries (AuxiliaryIndex N) ℂ :=
  ∏ j : Fin N, (1 - xVar N i * yVar N j)

private theorem clearedDenomMatrix_eq_rowProd_mul_cauchyEntry (N : ℕ) (i j : Fin N) :
    clearedDenomMatrix N i j =
      rowProd N i * auxiliaryPowerSeriesArray N ℂ i j := by

  have h_key : rowProd N i =
      (1 - xVar N i * yVar N j) * clearedDenomMatrix N i j := by
    simp only [rowProd, clearedDenomMatrix, Matrix.of_apply, xVar, yVar]
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have h_cancel := one_sub_xy_mul_invOfUnit N i j

  simp only [auxiliaryPowerSeriesArray]
  rw [h_key, mul_assoc, mul_comm (clearedDenomMatrix N i j) _, ← mul_assoc, h_cancel, one_mul]

private theorem det_clearedDenomMatrix_eq (N : ℕ) :
    (clearedDenomMatrix N).det = denomProd N * (auxiliaryPowerSeriesMatrix N ℂ).det := by

  have h_factor : clearedDenomMatrix N =
      Matrix.diagonal (rowProd N) * auxiliaryPowerSeriesMatrix N ℂ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, auxiliaryPowerSeriesMatrix, Matrix.of_apply]
    rw [Finset.sum_eq_single i
      (fun b _ hbi => by simp only [if_neg (Ne.symm hbi), zero_mul])
      (by simp)]
    simp only [ite_true]
    congr 1
    exact clearedDenomMatrix_eq_rowProd_mul_cauchyEntry N i j
  rw [h_factor, Matrix.det_mul, Matrix.det_diagonal]
  simp [denomProd, rowProd]

private theorem vandermondeFPS_x_eq_det (N : ℕ) :
    vandermondeFPS_x N = (Matrix.vandermonde (fun i => xVar N i)).det := by
  simp only [vandermondeFPS_x, Matrix.det_apply', Matrix.vandermonde, Matrix.of_apply]
  congr 1; ext σ
  simp only [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.monomial_one_eq,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sum_type,
    permExponentX_inr, pow_zero, Finset.prod_const_one, mul_one, permExponentX_inl,
    map_intCast]
  rw [show ∏ x : Fin N, MvPowerSeries.X (Sum.inl x) ^ ((σ⁻¹ x : Fin N) : ℕ) =
    ∏ x : Fin N, xVar N (σ x) ^ (x : ℕ) from
    Fintype.prod_equiv σ⁻¹ _ _ (fun i => by simp [xVar, Equiv.apply_symm_apply])]

private theorem vandermondeFPS_y_eq_det (N : ℕ) :
    vandermondeFPS_y N = (Matrix.vandermonde (fun j => yVar N j)).det := by
  simp only [vandermondeFPS_y, Matrix.det_apply', Matrix.vandermonde, Matrix.of_apply]
  congr 1; ext τ
  simp only [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.monomial_one_eq,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sum_type,
    permExponentY_inl, pow_zero, Finset.prod_const_one, one_mul, permExponentY_inr,
    map_intCast]
  rw [show ∏ x : Fin N, MvPowerSeries.X (Sum.inr x) ^ ((τ⁻¹ x : Fin N) : ℕ) =
    ∏ x : Fin N, yVar N (τ x) ^ (x : ℕ) from
    Fintype.prod_equiv τ⁻¹ _ _ (fun j => by simp [yVar, Equiv.apply_symm_apply])]

private noncomputable def espMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPowerSeries (AuxiliaryIndex N) ℂ) :=
  Matrix.of fun s j =>
    ∑ T ∈ (Finset.univ.erase j).powersetCard s.val, ∏ k ∈ T, (-(yVar N k))

private theorem prod_one_sub_eq_sum_powersetCard
    (S : Finset (Fin N)) (x : MvPowerSeries (AuxiliaryIndex N) ℂ) :
    ∏ k ∈ S, (1 - x * yVar N k) =
    ∑ s ∈ Finset.range (#S + 1),
      x ^ s * ∑ T ∈ S.powersetCard s, ∏ k ∈ T, (-yVar N k) := by

  simp_rw [show ∀ k, (1 : MvPowerSeries _ ℂ) - x * yVar N k =
    1 + (x * (-yVar N k)) from fun k => by ring]
  rw [Finset.prod_one_add]

  simp_rw [show ∀ T : Finset (Fin N), ∏ k ∈ T, (x * (-yVar N k)) =
    x ^ #T * ∏ k ∈ T, (-yVar N k) from fun T => by
    rw [Finset.prod_mul_distrib, Finset.prod_const]]

  rw [S.powerset_card_disjiUnion, Finset.sum_disjiUnion]

  refine Finset.sum_congr rfl fun s _ => ?_
  trans (∑ T ∈ S.powersetCard s, x ^ s * ∏ k ∈ T, (-yVar N k))
  · exact Finset.sum_congr rfl fun T hT => by
      rw [(Finset.mem_powersetCard.mp hT).2]
  · exact (Finset.mul_sum ..).symm

private theorem clearedDenom_eq_vanderm_mul_esp (N : ℕ) :
    clearedDenomMatrix N =
      Matrix.vandermonde (fun i => xVar N i) * espMatrix N := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vandermonde, Matrix.of_apply, espMatrix,
    clearedDenomMatrix]
  rw [prod_one_sub_eq_sum_powersetCard]



  have hN : 0 < N := Fin.pos j
  rw [show #(Finset.univ.erase j) + 1 = N from by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    omega]
  rw [← Fin.sum_univ_eq_sum_range]

private noncomputable def signedEsp (N : ℕ) (s : ℕ) : MvPowerSeries (AuxiliaryIndex N) ℂ :=
  ∑ T ∈ Finset.univ.powersetCard s, ∏ k ∈ T, (-(yVar N k))

private noncomputable def triA (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPowerSeries (AuxiliaryIndex N) ℂ) :=
  Matrix.of fun s n =>
    if (n : ℕ) ≤ s then signedEsp N (s.val - n.val) else 0

private theorem signedEsp_split (N : ℕ) (j : Fin N) (m : ℕ) :
    signedEsp N (m + 1) =
      ∑ T ∈ (Finset.univ.erase j).powersetCard (m + 1), ∏ k ∈ T, (-(yVar N k)) +
      (-(yVar N j)) * ∑ T ∈ (Finset.univ.erase j).powersetCard m, ∏ k ∈ T, (-(yVar N k)) := by
  simp only [signedEsp]
  set S := Finset.univ.erase j
  have hj : j ∉ S := Finset.notMem_erase j Finset.univ
  have h_univ : (Finset.univ : Finset (Fin N)) = insert j S :=
    (Finset.insert_erase (Finset.mem_univ j)).symm
  rw [h_univ, Finset.powersetCard_succ_insert hj]

  have h_disj : Disjoint (S.powersetCard (m + 1))
      ((S.powersetCard m).image (insert j)) := by
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    exact absurd (by rw [Finset.mem_image] at hT2; obtain ⟨_, _, rfl⟩ := hT2
                     exact Finset.mem_insert_self j _)
      (fun h => hj ((Finset.mem_powersetCard.mp hT1).1 h))
  rw [Finset.sum_union h_disj]
  congr 1

  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T hT => by
      rw [Finset.prod_insert (fun hm => hj ((Finset.mem_powersetCard.1 hT).1 hm))]
  ·
    intro T₁ hT₁ T₂ hT₂ h
    have h1 : j ∉ T₁ := fun hm => hj ((Finset.mem_powersetCard.1 (Finset.mem_coe.mp hT₁)).1 hm)
    have h2 : j ∉ T₂ := fun hm => hj ((Finset.mem_powersetCard.1 (Finset.mem_coe.mp hT₂)).1 hm)
    have := congr_arg (·.erase j) h

    beta_reduce at this
    rwa [Finset.erase_insert h1, Finset.erase_insert h2] at this

private theorem esp_eq_sum_signedEsp (N : ℕ) (j : Fin N) :
    ∀ s : ℕ,
    ∑ T ∈ (Finset.univ.erase j).powersetCard s, ∏ k ∈ T, (-(yVar N k)) =
    ∑ n ∈ Finset.range (s + 1), signedEsp N (s - n) * (yVar N j) ^ n := by
  intro s; induction s with
  | zero => simp [signedEsp, Finset.powersetCard_zero]
  | succ s ih =>

    have h_rec := signedEsp_split N j s
    have h_esp : ∑ T ∈ (Finset.univ.erase j).powersetCard (s + 1),
        ∏ k ∈ T, (-(yVar N k)) =
      signedEsp N (s + 1) - (-(yVar N j)) *
        ∑ T ∈ (Finset.univ.erase j).powersetCard s, ∏ k ∈ T, (-(yVar N k)) := by
      linear_combination -h_rec
    rw [h_esp, ih, neg_mul, sub_neg_eq_add, Finset.mul_sum,
        Finset.sum_range_succ' (fun n => signedEsp N (s + 1 - n) * yVar N j ^ n)]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    rw [add_comm (∑ _ ∈ _, _)]
    congr 1
    exact Finset.sum_congr rfl fun n hn => by
      rw [show s + 1 - (n + 1) = s - n from by omega]; ring

private theorem espMatrix_eq_triA_mul_vanderm (N : ℕ) :
    espMatrix N = triA N * (Matrix.vandermonde (fun j => yVar N j)).transpose := by
  funext ⟨s, hs⟩ j
  simp only [espMatrix, triA, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vandermonde, Matrix.of_apply]
  rw [esp_eq_sum_signedEsp N j s]
  symm

  rw [Fin.sum_univ_eq_sum_range (fun n =>
    (if n ≤ s then signedEsp N (s - n) else 0) * yVar N j ^ n)]


  trans ∑ n ∈ Finset.range (s + 1),
    (if n ≤ s then signedEsp N (s - n) else 0) * yVar N j ^ n
  · symm
    exact Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp only [if_neg (by omega : ¬(n ≤ s)), zero_mul]
  · exact Finset.sum_congr rfl fun n hn => by
      simp only [Finset.mem_range] at hn
      simp only [if_pos (by omega : n ≤ s)]

private theorem triA_blockTriangular (N : ℕ) :
    (triA N).BlockTriangular OrderDual.toDual := by
  intro s n hsn
  simp only [triA, Matrix.of_apply]
  exact if_neg (not_le.mpr (by exact hsn))

private theorem triA_diag (N : ℕ) (s : Fin N) :
    triA N s s = 1 := by
  simp only [triA, Matrix.of_apply, le_refl, ite_true, Nat.sub_self, signedEsp]
  simp [Finset.powersetCard_zero]

private theorem det_triA_eq_one (N : ℕ) : (triA N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (triA_blockTriangular N)]
  simp [triA_diag]

private theorem det_clearedDenomMatrix_eq_vandermonde_prod (N : ℕ) :
    (clearedDenomMatrix N).det = vandermondeFPS_x N * vandermondeFPS_y N := by
  rw [vandermondeFPS_x_eq_det, vandermondeFPS_y_eq_det]

  rw [clearedDenom_eq_vanderm_mul_esp, Matrix.det_mul]

  rw [espMatrix_eq_triA_mul_vanderm, Matrix.det_mul, det_triA_eq_one, one_mul,
      Matrix.det_transpose]

private theorem vandermonde_mul_fullCauchyProd_eq_cauchyRHS (N : ℕ) :
    vandermondeFPS_x N * vandermondeFPS_y N * auxiliaryPowerSeries N ℂ = auxiliaryDeterminantPowerSeries N ℂ := by


  have h1 := det_clearedDenomMatrix_eq_vandermonde_prod N
  have h2 := det_clearedDenomMatrix_eq N
  have h3 := denomProd_mul_fullCauchyProd N
  have h4 := det_auxiliaryPowerSeriesMatrix (k := ℂ) N





  calc vandermondeFPS_x N * vandermondeFPS_y N * auxiliaryPowerSeries N ℂ
      = (clearedDenomMatrix N).det * auxiliaryPowerSeries N ℂ := by rw [h1]
    _ = denomProd N * (auxiliaryPowerSeriesMatrix N ℂ).det * auxiliaryPowerSeries N ℂ := by rw [h2]
    _ = (auxiliaryPowerSeriesMatrix N ℂ).det * (denomProd N * auxiliaryPowerSeries N ℂ) := by ring
    _ = (auxiliaryPowerSeriesMatrix N ℂ).det * 1 := by rw [h3]
    _ = (auxiliaryPowerSeriesMatrix N ℂ).det := by ring
    _ = auxiliaryDeterminantPowerSeries N ℂ := h4

private theorem coeff_vandermondeFPS_x_mul (N : ℕ) (d : AuxiliaryIndex N →₀ ℕ)
    (F : MvPowerSeries (AuxiliaryIndex N) ℂ) :
    MvPowerSeries.coeff d (vandermondeFPS_x N * F) =
    ∑ π : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign π : ℤ) : ℂ) *
        (if permExponentX N π ≤ d
         then MvPowerSeries.coeff (d - permExponentX N π) F
         else 0) := by
  simp only [vandermondeFPS_x, Finset.sum_mul, smul_mul_assoc, map_sum,
    MvPowerSeries.coeff_smul]
  congr 1; ext π
  congr 1
  rw [MvPowerSeries.coeff_monomial_mul, one_mul]

private theorem alternating_coeff_eq_cauchyRHS_coeff (N : ℕ) (α β : Fin N → ℕ) :
    (∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, (π⁻¹ i : Fin N).val ≤ α i) ∧ (∀ i, (τ⁻¹ i : Fin N).val ≤ β i)
       then MvPowerSeries.coeff
              (auxiliaryFinsupp N (fun i => α i - (π⁻¹ i : Fin N).val)
                               (fun i => β i - (τ⁻¹ i : Fin N).val))
              (auxiliaryPowerSeries N ℂ)
       else 0)) =
    MvPowerSeries.coeff (auxiliaryFinsupp N α β) (auxiliaryDeterminantPowerSeries N ℂ) := by

  rw [← vandermonde_mul_fullCauchyProd_eq_cauchyRHS N, mul_assoc]

  rw [coeff_vandermondeFPS_x_mul]

  apply Finset.sum_congr rfl; intro π _
  by_cases hπ : ∀ i, (π⁻¹ i : Fin N).val ≤ α i
  ·
    have hle : permExponentX N π ≤ auxiliaryFinsupp N α β :=
      (permExponentX_le_bilinExponent_iff N α β π).mpr hπ
    rw [if_pos hle, bilinExponent_sub_permExponentX N α β π hπ]

    simp only [vandermondeFPS_y, Finset.sum_mul, smul_mul_assoc, map_sum,
      MvPowerSeries.coeff_smul]


    rw [Finset.mul_sum]; congr 1; ext τ
    rw [MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hτ : ∀ j, (τ⁻¹ j : Fin N).val ≤ β j
    · have hle' : permExponentY N τ ≤ auxiliaryFinsupp N (fun i => α i - (π⁻¹ i).val) β :=
        (permExponentY_le_bilinExponent_iff N _ β τ).mpr hτ
      rw [if_pos hle', bilinExponent_sub_permExponentY N _ β τ hτ,
        if_pos ⟨hπ, hτ⟩]
      ring
    · have hle' : ¬(permExponentY N τ ≤ auxiliaryFinsupp N (fun i => α i - (π⁻¹ i).val) β) :=
        by rwa [permExponentY_le_bilinExponent_iff]
      rw [if_neg hle', if_neg (show ¬(_ ∧ _) from fun h => hτ h.2)]
      ring
  ·
    have hle : ¬(permExponentX N π ≤ auxiliaryFinsupp N α β) :=
      by rwa [permExponentX_le_bilinExponent_iff]
    rw [if_neg hle]
    simp only [show ¬((∀ i, (π⁻¹ i : Fin N).val ≤ α i) ∧ _) from fun h => hπ h.1,
      if_false, mul_zero, Finset.sum_const_zero, mul_zero]

/-- For an injective Nat-valued function, the displayed double signed permutation sum is one. -/
theorem double_signed_permutation_sum_eq_one_of_injective (N : ℕ) (α : Fin N → ℕ)
    (hα_inj : Function.Injective α) :
    (∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, (π⁻¹ i : Fin N).val ≤ α i) ∧ (∀ i, (τ⁻¹ i : Fin N).val ≤ α i)
       then MvPowerSeries.coeff
              (auxiliaryFinsupp N (fun i => α i - (π⁻¹ i : Fin N).val)
                               (fun i => α i - (τ⁻¹ i : Fin N).val))
              (auxiliaryPowerSeries N ℂ)
       else 0)) = 1 := by
  have h1 := alternating_coeff_eq_cauchyRHS_coeff N α α
  have h2 := auxiliarySeries_coeff_auxiliaryFinsupp_eq_one_of_injective_eq ℂ (N := N) α α hα_inj hα_inj (fun _ => rfl)
  rw [h1, h2]

/-- For strictly antitone Nat-valued functions, the displayed double signed permutation sum equals their equality indicator. -/
theorem double_signed_permutation_sum_eq_indicator_of_strictAnti (N : ℕ) (α β : Fin N → ℕ)
    (hα : StrictAnti α) (hβ : StrictAnti β) :
    (∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
      (if (∀ i, (π⁻¹ i : Fin N).val ≤ α i) ∧ (∀ i, (τ⁻¹ i : Fin N).val ≤ β i)
       then MvPowerSeries.coeff
              (auxiliaryFinsupp N (fun i => α i - (π⁻¹ i : Fin N).val)
                               (fun i => β i - (τ⁻¹ i : Fin N).val))
              (auxiliaryPowerSeries N ℂ)
       else 0)) =
    if α = β then 1 else 0 := by

  have hcauchy : MvPowerSeries.coeff (auxiliaryFinsupp N α β) (auxiliaryDeterminantPowerSeries N ℂ) =
      if α = β then 1 else 0 := by
    by_cases heq : α = β
    · subst heq; rw [if_pos rfl]
      exact auxiliarySeries_coeff_auxiliaryFinsupp_eq_one_of_injective_eq ℂ (N := N) α α hα.injective hα.injective
        (fun _ => rfl)
    · rw [if_neg heq, @auxiliarySeries_coeff_auxiliaryFinsupp_eq_signed_permutation_sum N ℂ _ _ α β]
      apply Finset.sum_eq_zero; intro σ _
      suffices h : ¬(∀ j, α j = β (σ j)) by rw [if_neg h, mul_zero]
      intro hall; apply heq; funext j

      have hσ_mono : StrictMono (⇑σ : Fin N → Fin N) := by
        intro i k hik
        by_contra hle; push Not at hle
        rcases hle.eq_or_lt with heq' | hlt
        · exact absurd (σ.injective heq'.symm) (ne_of_lt hik)
        · exact absurd (hα hik) (not_lt.mpr (le_of_lt (by rw [hall i, hall k]; exact hβ hlt)))
      rw [show σ = 1 from perm_eq_one_of_strictMono hσ_mono] at hall; exact hall j
  rw [alternating_coeff_eq_cauchyRHS_coeff N α β, hcauchy]

end RepresentationTheory.Combinatorics.PermutationPowerSeries

end

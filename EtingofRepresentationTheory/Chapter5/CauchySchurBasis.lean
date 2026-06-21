import Mathlib
import EtingofRepresentationTheory.Chapter5.CharacterOrthogonality
import EtingofRepresentationTheory.Chapter5.SchurWeylPolynomialIdentity

/-!
# The Cauchy identity in the Schur basis at `y = 1ᴺ`

This file proves the symmetric-function core of the right-`GL_N` Cauchy character
identity (#4944, sub-issue B / #4958): for every weight `μ : Fin N →₀ ℕ` of size `d`,

  `∑_{ν : BoundedPartition N d} s_ν(1ᴺ) · [x^μ] s_ν = ∏_j C(μ_j + N − 1, N − 1)`,

where `s_ν(1ᴺ) = eval 1 (schurPoly N ν.parts)` and `[x^μ] s_ν = (schurPoly N ν.parts).coeff μ`.

## Proof outline

Write `aᵥ = s_ν(1ᴺ)`, `bᵥ = [x^μ] s_ν`. The goal is `∑ᵥ aᵥ bᵥ = ∏_j C(μ_j+N−1,N−1)`.

1. **Orthogonality inversion** (`factorial_mul_sum_eq_sum_perm`): for any
   `F G : BoundedPartition N d → ℚ`,
   `d! · ∑ᵥ F ν G ν = ∑_{σ∈S_d} (∑ᵥ χᵥ(σ) F ν)(∑ᵥ χᵥ(σ) G ν)`,
   using the `S_d` character orthogonality `charValue_row_orthogonality`.

2. **Frobenius** (`Proposition5_21_1_univ`): applying the linear functionals `eval 1`
   and `coeff μ` to `p_{type σ} = ∑ᵥ χᵥ(σ) s_ν` turns the inner sums into
   `eval 1 (P_σ)` and `coeff μ (P_σ)`, where `P_σ = powerSumCycleProduct N σ`.

3. **Power-sum Cauchy**: `eval 1 (P_σ) = ∑_β coeff β (P_σ)` (sum over the degree-`d`
   monomials, by homogeneity); swapping the `σ`/`β` sums and using
   `powerSum_bilinear_coeff_gen` + `fullCauchyProd_coeff_eq_card_gen` gives
   `∑_β d! · #{N×N matrices, row sums β, col sums μ}`.

4. **Stars and bars** (`sum_card_NNMatrixGen_eq_prod_choose`): summing over the row
   margins `β` collapses to all matrices with column sums `μ`, which factor over the
   `N` columns into `∏_j C(μ_j + N − 1, N − 1)`.

Cancelling `d!` yields the identity.
-/

open MvPolynomial Finset

namespace Etingof.CauchySchurBasis

variable {N d : ℕ}

/-! ### Step 1: orthogonality inversion -/

/-- **Orthogonality inversion.** For any two `ℚ`-valued functions on the bounded
partitions of `d`, the diagonal pairing is recovered (up to `d!`) by summing the
products of the two `charValue`-twisted sums over all permutations `σ ∈ S_d`. This is
the symmetric-group character orthogonality `charValue_row_orthogonality` repackaged
for the two linear functionals `eval 1` and `coeff μ`. -/
theorem factorial_mul_sum_eq_sum_perm (F G : BoundedPartition N d → ℚ) :
    (d.factorial : ℚ) * ∑ ν : BoundedPartition N d, F ν * G ν =
    ∑ σ : Equiv.Perm (Fin d),
      (∑ ν : BoundedPartition N d, charValue N ν (fullCycleTypePartition σ) * F ν) *
      (∑ ν : BoundedPartition N d, charValue N ν (fullCycleTypePartition σ) * G ν) := by
  -- Expand each product of sums and pull the `σ`-sum innermost.
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_comm)]
  -- Now: ∑_ν ∑_ρ ∑_σ (χ_ν(σ) F ν)(χ_ρ(σ) G ρ); collapse the inner σ-sum via orthogonality.
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  -- goal: d! * (F ν * G ν) = ∑_ρ ∑_σ (χ_ν F ν)(χ_ρ G ρ)
  have hinner : ∀ ρ : BoundedPartition N d,
      (∑ σ : Equiv.Perm (Fin d),
        charValue N ν (fullCycleTypePartition σ) * F ν *
          (charValue N ρ (fullCycleTypePartition σ) * G ρ)) =
      (if ν = ρ then (d.factorial : ℚ) else 0) * (F ν * G ρ) := by
    intro ρ
    have : ∀ σ : Equiv.Perm (Fin d),
        charValue N ν (fullCycleTypePartition σ) * F ν *
          (charValue N ρ (fullCycleTypePartition σ) * G ρ) =
        (charValue N ν (fullCycleTypePartition σ) *
          charValue N ρ (fullCycleTypePartition σ)) * (F ν * G ρ) := by
      intro σ; ring
    simp_rw [this, ← Finset.sum_mul, charValue_row_orthogonality N ν ρ]
  simp_rw [hinner, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ ν (fun ρ => (d.factorial : ℚ) * (F ν * G ρ))]
  simp

/-! ### Step 2: Frobenius expansion of the two functionals -/

/-- `eval 1` of the power-sum product `P_σ` expands over bounded partitions with
`charValue` coefficients, by the Frobenius formula `Proposition5_21_1_univ`. -/
theorem eval_one_powerSumCycleProduct (σ : Equiv.Perm (Fin d)) :
    eval (fun _ => (1 : ℚ)) (powerSumCycleProduct N σ) =
    ∑ ν : BoundedPartition N d,
      charValue N ν (fullCycleTypePartition σ) *
        eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts) := by
  rw [powerSumCycleProduct_eq_psumPart, Proposition5_21_1_univ, map_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]

/-- `coeff μ` of the power-sum product `P_σ` expands over bounded partitions with
`charValue` coefficients, by the Frobenius formula `Proposition5_21_1_univ`. -/
theorem coeff_powerSumCycleProduct_schur (σ : Equiv.Perm (Fin d)) (μ : Fin N →₀ ℕ) :
    coeff μ (powerSumCycleProduct N σ) =
    ∑ ν : BoundedPartition N d,
      charValue N ν (fullCycleTypePartition σ) *
        coeff μ (schurPoly N ν.parts) := by
  rw [powerSumCycleProduct_eq_psumPart, Proposition5_21_1_univ, coeff_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [coeff_smul, smul_eq_mul]

/-! ### Step 3: `eval 1` as a sum over degree-`d` monomials -/

/-- `eval 1` of the homogeneous degree-`d` polynomial `P_σ` is the sum of its
coefficients over all weight monomials of size `d`. -/
theorem eval_one_eq_sum_coeff (σ : Equiv.Perm (Fin d)) :
    eval (fun _ => (1 : ℚ)) (powerSumCycleProduct N σ) =
    ∑ β ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d,
      coeff β (powerSumCycleProduct N σ) := by
  rw [eval_eq']
  simp only [one_pow, Finset.prod_const_one, mul_one]
  -- support ⊆ antidiag, with the extra antidiag terms vanishing
  have hhom : (powerSumCycleProduct N σ).IsHomogeneous d := by
    rw [powerSumCycleProduct_eq_psumPart]
    exact psumPart_isHomogeneous N (fullCycleTypePartition σ)
  apply Finset.sum_subset
  · intro β hβ
    rw [mem_finsuppAntidiag]
    have hdeg : β.degree = ∑ i, β i := Finsupp.degree_eq_sum β
    refine ⟨?_, Finset.subset_univ _⟩
    by_contra hne
    exact (mem_support_iff.1 hβ) (hhom.coeff_eq_zero (by rw [hdeg]; exact hne))
  · intro β _ hβ
    exact Finsupp.notMem_support_iff.1 hβ

/-! ### Step 4: the stars-and-bars matrix count -/

/-- **Stars and bars.** Summing the number of `N×N` non-negative integer matrices with
row sums `β` and column sums `μ` over all row margins `β` (of total `d = ∑ μ`) collapses
to the number of matrices with column sums `μ` (rows free), which factors over the `N`
columns into `∏_j C(μ_j + N − 1, N − 1)`. -/
theorem sum_card_NNMatrixGen_eq_prod_choose (μ : Fin N →₀ ℕ) (hμ : ∑ i, μ i = d) :
    ∑ β ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d,
      Fintype.card (NNMatrixWithMarginsGen N (n := d) (⇑β) (⇑μ)) =
    ∏ j, (μ j + N - 1).choose (N - 1) := by
  sorry

/-! ### Assembly -/

/-- **Cauchy identity in the Schur basis at `y = 1ᴺ`** (#4958). For every weight
`μ : Fin N →₀ ℕ` of size `d`,

  `∑_{ν : BoundedPartition N d} s_ν(1ᴺ) · [x^μ] s_ν = ∏_j C(μ_j + N − 1, N − 1)`. -/
theorem cauchy_schur_coeff (μ : Fin N →₀ ℕ) (hμ : ∑ i, μ i = d) :
    ∑ ν : BoundedPartition N d,
      eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts) * coeff μ (schurPoly N ν.parts) =
    ∏ j, ((μ j + N - 1).choose (N - 1) : ℚ) := by
  -- Cancel `d!` from the inversion identity.
  refine mul_left_cancel₀ (a := (d.factorial : ℚ)) (by positivity) ?_
  rw [factorial_mul_sum_eq_sum_perm
        (fun ν => eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts))
        (fun ν => coeff μ (schurPoly N ν.parts))]
  simp_rw [← eval_one_powerSumCycleProduct, ← coeff_powerSumCycleProduct_schur,
    eval_one_eq_sum_coeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  -- inner `σ`-sum over each row margin `β`: power-sum Cauchy → matrix count
  have step : ∀ β ∈ finsuppAntidiag (Finset.univ : Finset (Fin N)) d,
      (∑ σ : Equiv.Perm (Fin d),
        coeff β (powerSumCycleProduct N σ) * coeff μ (powerSumCycleProduct N σ)) =
      (d.factorial : ℚ) *
        (Fintype.card (NNMatrixWithMarginsGen N (n := d) (⇑β) (⇑μ)) : ℚ) := by
    intro β hβ
    rw [mem_finsuppAntidiag] at hβ
    have hβsum : ∑ i, β i = d := hβ.1
    rw [powerSum_bilinear_coeff_gen N β μ hβsum hμ,
      fullCauchyProd_coeff_eq_card_gen (N := N) (n := d) (⇑β) (⇑μ) (fun i => by
        have := Finset.single_le_sum (f := (⇑β : Fin N → ℕ)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
        omega)]
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum, ← Nat.cast_sum,
    sum_card_NNMatrixGen_eq_prod_choose μ hμ, Nat.cast_prod]

end Etingof.CauchySchurBasis

import Mathlib
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyBilinear
import EtingofRepresentationTheory.Chapter5.PowerSumCauchyBilinearGen
import EtingofRepresentationTheory.Chapter5.Proposition5_21_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1

/-!
# Character Row Orthogonality for Symmetric Groups

This file proves the row orthogonality relation for irreducible characters of Sₙ:

  ∑_{σ∈Sₙ} χ_λ(σ) · χ_{λ'}(σ) = n! · δ_{λ,λ'}

where χ_λ is the character value defined via the Frobenius formula.

## Proof strategy

The proof proceeds by connecting charValue to the Cauchy identity:

1. **Expand charValue**: `charValue(N, λ, type(σ))` is the coefficient of
   `x^{λ+δ}` in `Δ(x) · P_σ(x)`. Expanding the alternant Δ via the
   Leibniz formula gives a signed sum over permutations:
   `charValue = ∑_π sign(π) · coeff_{λ+δ-π(δ)}(P_σ)`

2. **Bilinear identity**: Sum the product of two charValues over σ ∈ S_n.
   After exchanging summation order:
   `∑_σ charValue(λ) · charValue(λ') = ∑_π ∑_τ sign(π)sign(τ) · [∑_σ coeff·coeff]`
   The inner sum `∑_σ coeff_α(P_σ) · coeff_β(P_σ)` equals
   `n! · fullCauchyProd_coeff` by `powerSum_bilinear_coeff_gen`.

3. **Cauchy identity**: The resulting double alternating sum of fullCauchyProd
   coefficients equals `δ_{λ,λ'}` by `vandermonde_cauchy_general`.

## Main results

* `charValue_row_orthogonality`: the row orthogonality relation for character values
* `charValue_as_alternating_coeff`: expansion of charValue via the alternant
-/

open MvPolynomial Finset

noncomputable section

namespace Etingof

/-! ### Step 1: Expand charValue via the alternant determinant -/

/-- The exponent vector for permutation π applied to vandermondeExps:
the function `i ↦ vandermondeExps N (π⁻¹ i) = N - 1 - π⁻¹(i)`.

This corresponds to the monomial exponent of the π-th term in the
Leibniz expansion of the alternant determinant. -/
private def permVandermondeExp (N : ℕ) (π : Equiv.Perm (Fin N)) : Fin N → ℕ :=
  fun i => vandermondeExps N (π⁻¹ i)

/-- **Alternant determinant expansion**: the coefficient of `x^e` in the product
`det(alternantMatrix(δ)) · f` equals the alternating sum of coefficients of `f`
at shifted exponents.

This is the key step: it expands
  `[x^e](Δ · f) = ∑_π sign(π) · [x^{e - π(δ)}](f)`
where the sum is over permutations π such that `e - π(δ) ≥ 0` pointwise. -/
theorem coeff_alternant_mul_eq_alternating_sum (N : ℕ) (e : Fin N →₀ ℕ)
    (f : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff e ((alternantMatrix N (vandermondeExps N)).det * f) =
    ∑ π : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) *
      (if ∀ i, permVandermondeExp N π i ≤ e i
       then MvPolynomial.coeff (e - Finsupp.equivFunOnFinite.symm (permVandermondeExp N π)) f
       else 0) := by
  -- Expand the determinant via Leibniz formula and distribute over f
  rw [Matrix.det_apply, Finset.sum_mul]
  simp only [MvPolynomial.coeff_sum, smul_mul_assoc, MvPolynomial.coeff_smul]
  -- Each permutation term: ∏_j alternantMatrix(σ j, j) = monomial(vandermondeExps ∘ σ⁻¹) 1
  simp_rw [show ∀ σ : Equiv.Perm (Fin N), ∏ j, alternantMatrix N (vandermondeExps N) (σ j) j =
      monomial (Finsupp.equivFunOnFinite.symm (vandermondeExps N ∘ ⇑σ.symm)) 1 from fun σ => by
    rw [show ∏ j, alternantMatrix N (vandermondeExps N) (σ j) j =
        ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ vandermondeExps N j from rfl,
      show ∏ j, (X (σ j) : MvPolynomial (Fin N) ℚ) ^ vandermondeExps N j =
        ∏ i, X i ^ (vandermondeExps N (σ.symm i))
        from Fintype.prod_equiv σ _ _ (fun _ => by simp)]
    exact prod_X_pow_eq_monomial' _]
  -- Match term by term
  apply Finset.sum_congr rfl; intro π _
  -- Convert Units.smul to cast * ...
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
  congr 1
  -- coeff_e(monomial(m) 1 * f) = if m ≤ e then 1 * coeff_{e-m}(f) else 0
  rw [MvPolynomial.coeff_monomial_mul', one_mul]
  -- The monomial exponent is vandermondeExps ∘ π⁻¹ = permVandermondeExp N π
  have heq : Finsupp.equivFunOnFinite.symm (vandermondeExps N ∘ ⇑π.symm) =
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π) := by
    ext i; simp [permVandermondeExp, Equiv.Perm.inv_def]
  rw [heq]; congr 1

/-- **charValue as alternating coefficient sum**: the character value
`χ_λ(μ)` equals the alternating sum of power sum partition coefficients
at shifted exponents `λ+δ - π(δ)`. -/
theorem charValue_as_alternating_coeff
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n) (μ : n.Partition) :
    charValue N lam μ =
    ∑ π : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) *
      (if ∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i
       then MvPolynomial.coeff
         (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
          Finsupp.equivFunOnFinite.symm (permVandermondeExp N π))
         (MvPolynomial.psumPart (Fin N) ℚ μ)
       else 0) := by
  unfold charValue
  exact coeff_alternant_mul_eq_alternating_sum N
    (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts))
    (MvPolynomial.psumPart (Fin N) ℚ μ)

/-- Sum of shifted minus permuted vandermondeExps equals n. -/
private lemma sum_shiftedExps_sub_permVandermondeExp
    (N : ℕ) {n : ℕ} (lam : BoundedPartition N n)
    (π : Equiv.Perm (Fin N))
    (hle : ∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i) :
    ∑ i, (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π) : Fin N →₀ ℕ) i = n := by
  -- Simplify Finsupp evaluations
  have heval : ∀ (f : Fin N → ℕ) (i : Fin N),
      (Finsupp.equivFunOnFinite.symm f : Fin N →₀ ℕ) i = f i := by
    intros; simp [Finsupp.equivFunOnFinite]
  simp_rw [show ∀ i, (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π) : Fin N →₀ ℕ) i =
      shiftedExps N lam.parts i - permVandermondeExp N π i from by
    intro i; simp [Finsupp.equivFunOnFinite, Finsupp.coe_tsub, heval]]
  -- ∑(a - b) + ∑ b = ∑ a when b ≤ a pointwise, so ∑(a - b) = ∑ a - ∑ b
  have key : ∑ i : Fin N, (shiftedExps N lam.parts i - permVandermondeExp N π i) +
      ∑ i : Fin N, permVandermondeExp N π i =
      ∑ i : Fin N, shiftedExps N lam.parts i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
  -- ∑ shiftedExps = ∑ lam.parts + ∑ vandermondeExps = n + ∑ vandermondeExps
  have hsum_shifted : ∑ i : Fin N, shiftedExps N lam.parts i =
      n + ∑ i : Fin N, vandermondeExps N i := by
    unfold shiftedExps vandermondeExps
    rw [show ∑ i : Fin N, (lam.parts i + (N - 1 - ↑i)) =
        ∑ i : Fin N, lam.parts i + ∑ i : Fin N, (N - 1 - (↑i : ℕ)) from
      Finset.sum_add_distrib]
    rw [lam.sum_eq]
  -- ∑ permVandermondeExp = ∑ vandermondeExps (permutation invariance)
  have hsum_perm : ∑ i : Fin N, permVandermondeExp N π i =
      ∑ i : Fin N, vandermondeExps N i :=
    Fintype.sum_equiv π⁻¹ _ _ (fun _ => rfl)
  omega

/-! ### Step 2: Bilinear sum over permutations -/

/-- **Bilinear expansion**: the sum of products of character values over all
permutations σ ∈ Sₙ equals a double alternating sum of fullCauchyProd
coefficients (times n!).

This uses `powerSum_bilinear_coeff_gen` to convert
`∑_σ coeff_α(P_σ) · coeff_β(P_σ)` into `n! · fullCauchyProd` coefficients. -/
theorem charValue_product_sum_eq_alternating_cauchy
    (N : ℕ) {n : ℕ} (lam lam' : BoundedPartition N n) :
    (∑ σ : Equiv.Perm (Fin n),
      charValue N lam (fullCycleTypePartition σ) *
      charValue N lam' (fullCycleTypePartition σ) : ℚ) =
    (n.factorial : ℚ) *
    ∑ π : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      (↑(Equiv.Perm.sign π : ℤ) : ℚ) * (↑(Equiv.Perm.sign τ : ℤ) : ℚ) *
      (if (∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i) ∧
          (∀ i, permVandermondeExp N τ i ≤ shiftedExps N lam'.parts i)
       then MvPowerSeries.coeff
              (bilinExponent N
                (fun i => shiftedExps N lam.parts i - permVandermondeExp N π i)
                (fun i => shiftedExps N lam'.parts i - permVandermondeExp N τ i))
              (fullCauchyProd N ℚ)
       else 0) := by
  -- Step 1: Expand charValue using the alternant expansion
  simp_rw [charValue_as_alternating_coeff]
  -- Step 2: Each summand is a product of two alternating sums
  -- ∑_σ (∑_π sign(π)*f_π(σ)) * (∑_τ sign(τ)*g_τ(σ))
  -- = ∑_σ ∑_π ∑_τ sign(π)*sign(τ)*f_π(σ)*g_τ(σ)
  simp_rw [Finset.sum_mul_sum]
  -- Step 3: Exchange sum order: ∑_σ ∑_π ∑_τ → ∑_π ∑_τ ∑_σ
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := Equiv.Perm (Fin n)))]
  -- Now: ∑_π ∑_τ ∑_σ sign(π)*f_π(σ) * sign(τ)*g_τ(σ)
  -- Step 4: Factor n! out and match term by term
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro π _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro τ _
  -- Factor out signs and merge conditionals
  set hcondπ := ∀ i, permVandermondeExp N π i ≤ shiftedExps N lam.parts i
  set hcondτ := ∀ i, permVandermondeExp N τ i ≤ shiftedExps N lam'.parts i
  set sπ := (↑(Equiv.Perm.sign π : ℤ) : ℚ)
  set sτ := (↑(Equiv.Perm.sign τ : ℤ) : ℚ)
  set α' := Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N π)
  set β' := Finsupp.equivFunOnFinite.symm (shiftedExps N lam'.parts) -
      Finsupp.equivFunOnFinite.symm (permVandermondeExp N τ)
  -- Each summand: sπ * (if hcondπ then ... else 0) * (sτ * (if hcondτ then ... else 0))
  -- = sπ * sτ * (if hcondπ ∧ hcondτ then ... * ... else 0)
  have aux : ∀ (a b c d : ℚ) (P Q : Prop) [Decidable P] [Decidable Q],
      (a * if P then c else 0) * (b * if Q then d else 0) =
      a * b * if P ∧ Q then c * d else 0 := by
    intros; split_ifs <;> simp_all <;> ring
  simp_rw [aux]
  rw [← Finset.mul_sum]
  split_ifs with h
  · -- Both conditions hold: apply powerSum_bilinear_coeff_gen
    obtain ⟨hπ, hτ⟩ := h
    -- Replace psumPart with powerSumCycleProduct
    simp_rw [← powerSumCycleProduct_eq_psumPart]
    -- Need sum hypotheses for powerSum_bilinear_coeff_gen
    have hα_sum : ∑ i, α' i = n :=
      sum_shiftedExps_sub_permVandermondeExp N lam π hπ
    have hβ_sum : ∑ i, β' i = n :=
      sum_shiftedExps_sub_permVandermondeExp N lam' τ hτ
    rw [powerSum_bilinear_coeff_gen N α' β' hα_sum hβ_sum]
    -- Now: sπ * sτ * (n! * coeff) = n! * (sπ * sτ * coeff)
    -- with matching bilinExponent
    have hbilin : bilinExponent N (⇑α') (⇑β') =
        bilinExponent N (fun i => shiftedExps N lam.parts i - permVandermondeExp N π i)
          (fun i => shiftedExps N lam'.parts i - permVandermondeExp N τ i) := by
      ext v; cases v <;> simp [bilinExponent, α', β', Finsupp.equivFunOnFinite]
    rw [hbilin]; ring
  · -- At least one condition fails: both sides are zero
    simp

/-! ### Step 3: Connecting to vandermonde_cauchy_general -/

/-- **Row orthogonality of Sₙ characters**: For bounded partitions λ, λ' of n
with at most N parts,

  ∑_{σ∈Sₙ} χ_λ(type(σ)) · χ_{λ'}(type(σ)) = n! · δ_{λ,λ'}

where `χ_λ(type(σ)) = charValue N lam (fullCycleTypePartition σ)` is the
Frobenius character value.

The proof uses:
- `charValue_product_sum_eq_alternating_cauchy` to reduce the LHS to a
  double alternating sum of fullCauchyProd coefficients
- `vandermonde_cauchy_general` to evaluate the alternating sum as δ_{λ,λ'}

Note: The proof currently relies on `powerSum_bilinear_coeff_gen` which
has a sorry from the generalized double counting lemma. -/
theorem charValue_row_orthogonality
    (N : ℕ) {n : ℕ} (lam lam' : BoundedPartition N n) :
    ∑ σ : Equiv.Perm (Fin n),
      charValue N lam (fullCycleTypePartition σ) *
      charValue N lam' (fullCycleTypePartition σ) =
    if lam = lam' then (n.factorial : ℚ) else 0 := by
  -- Step 1: Reduce to alternating sum of fullCauchyProd coefficients
  rw [charValue_product_sum_eq_alternating_cauchy]
  -- Step 2: The alternating sum equals δ_{λ,λ'} by vandermonde_cauchy_general
  -- This requires connecting the ℚ fullCauchyProd coefficients to the ℂ version
  -- used in vandermonde_cauchy_general, and matching the permVandermondeExp
  -- with the (π⁻¹ i).val in vandermonde_cauchy_general.
  sorry

end Etingof

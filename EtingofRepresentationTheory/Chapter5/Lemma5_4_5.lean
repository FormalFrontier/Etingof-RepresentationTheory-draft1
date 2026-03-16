import Mathlib

/-!
# Lemma 5.4.5: Roots of Unity Average

If ε₁, ..., εₙ are roots of unity in ℂ and their average (ε₁ + ... + εₙ)/n is
an algebraic integer, then either:
- all εᵢ are equal, or
- ε₁ + ... + εₙ = 0.

The proof uses the fact that |εᵢ| = 1 for roots of unity, so
|(ε₁ + ... + εₙ)/n| ≤ 1, with equality iff all εᵢ are equal.
If the average is a nonzero algebraic integer, its norm must be ≥ 1, forcing equality.

## Mathlib correspondence

Uses `IsPrimitiveRoot`, `rootsOfUnity`, `IsIntegral`, `Algebra.norm`.
-/

open Finset Complex in
/-- Key algebraic number theory lemma: a nonzero algebraic integer that is the average
of roots of unity has norm ≥ 1 by the product formula, contradicting the strict
triangle inequality when not all roots are equal.

The proof considers L = ℚ(ε₁,...,εₙ), a number field. Every ℚ-algebra
homomorphism σ : L → ℂ sends each εᵢ to a root of unity of the same order
(since σ preserves εᵢ^mᵢ = 1). Therefore |σ((∑εᵢ)/n)| ≤ 1 for all σ.
By the product formula, |Norm(α)| = ∏ |σ(α)| < 1 (one factor is < 1).
But Norm(α) is a nonzero integer, giving a contradiction. -/
private lemma roots_of_unity_avg_norm_bound
    (n : ℕ) (hn : 0 < n)
    (ε : Fin n → ℂ)
    (hε : ∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1)
    (hint : IsIntegral ℤ ((∑ i, ε i) / n))
    (hsum : (∑ i, ε i) ≠ 0)
    (hlt : ‖(∑ i, ε i) / (n : ℂ)‖ < 1) :
    False := by
  -- Set up intermediate field L = ℚ(ε₁,...,εₙ) inside ℂ
  set L := IntermediateField.adjoin ℚ (Set.range ε) with hL_def
  -- Each εᵢ is integral over ℤ (root of X^mᵢ - 1)
  have hε_int : ∀ i, IsIntegral ℤ (ε i) := by
    intro i
    obtain ⟨m, hm, hpow⟩ := hε i
    exact ⟨Polynomial.X ^ m - 1,
      Polynomial.monic_X_pow_sub_C 1 (Nat.pos_iff_ne_zero.mp hm),
      by simp [hpow]⟩
  -- Each εᵢ is integral over ℚ
  have hε_intQ : ∀ x ∈ Set.range ε, IsIntegral ℚ x := by
    intro x ⟨i, hi⟩; rw [← hi]; exact (hε_int i).tower_top
  -- L is finite-dimensional over ℚ
  haveI hL_fd : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin hε_intQ
  -- L has characteristic zero (subfield of ℂ, with ℚ ↪ L injective)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  -- L is a number field
  haveI : NumberField L := ⟨⟩
  -- Each εᵢ is in L
  have hε_mem : ∀ i, ε i ∈ L :=
    fun i => IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)
  -- Lift εᵢ to elements of L
  set ε' : Fin n → L := fun i => ⟨ε i, hε_mem i⟩ with hε'_def
  -- α = (∑ εᵢ)/n as an element of L
  have hα_mem : (∑ i, ε i) / (n : ℂ) ∈ L :=
    L.div_mem (L.sum_mem (fun i _ => hε_mem i)) (L.natCast_mem n)
  set α : L := ⟨(∑ i, ε i) / (n : ℂ), hα_mem⟩ with hα_def
  -- α ≠ 0
  have hα_ne : α ≠ 0 := by
    intro h
    apply hsum
    have h0 : (α : ℂ) = 0 := congr_arg Subtype.val h
    change (∑ i, ε i) / (n : ℂ) = 0 at h0
    have hnn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    rwa [div_eq_zero_iff, or_iff_left hnn'] at h0
  -- For any embedding σ : L →ₐ[ℚ] ℂ, each σ(εᵢ) is a root of unity with ‖σ(εᵢ)‖ = 1
  have hσε_norm : ∀ (σ : L →ₐ[ℚ] ℂ) (i : Fin n), ‖σ (ε' i)‖ = 1 := by
    intro σ i
    obtain ⟨m, hm, hpow⟩ := hε i
    apply Complex.norm_eq_one_of_pow_eq_one _ (Nat.pos_iff_ne_zero.mp hm)
    calc (σ (ε' i)) ^ m = σ ((ε' i) ^ m) := (map_pow σ _ m).symm
      _ = σ ⟨1, L.one_mem⟩ := by
          congr 1; ext; simp [hε'_def, hpow]
      _ = 1 := map_one σ
  -- For any embedding σ, ‖σ(α)‖ ≤ 1
  have hσ_bound : ∀ (σ : L →ₐ[ℚ] ℂ), ‖σ α‖ ≤ 1 := by
    intro σ
    have hnn : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
    -- σ(α) = (∑ σ(εᵢ))/n
    have hσα : σ α = (∑ i, σ (ε' i)) / (n : ℂ) := by
      have key : α = (∑ i, ε' i) / (n : L) := by
        apply_fun (algebraMap L ℂ) using (algebraMap L ℂ).injective
        simp only [map_div₀, map_sum, map_natCast]
        rfl
      rw [key, map_div₀, map_sum, map_natCast]
    rw [hσα, norm_div, Complex.norm_natCast, div_le_one hnn]
    calc ‖∑ i, σ (ε' i)‖ ≤ ∑ i, ‖σ (ε' i)‖ := norm_sum_le _ _
      _ = ∑ _i : Fin n, (1 : ℝ) := by congr 1; ext i; exact hσε_norm σ i
      _ = n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- The inclusion L ↪ ℂ is an embedding with ‖ι(α)‖ < 1
  set ι₀ : L →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ L ℂ with hι₀_def
  have hι_val : ι₀ α = (α : ℂ) := rfl
  -- By norm_eq_prod_embeddings: algebraMap ℚ ℂ (Norm α) = ∏ σ(α)
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ (α : L)
  -- ∏ ‖σ(α)‖ < 1 (each ≤ 1, one < 1)
  have hprod_lt : ∏ σ : L →ₐ[ℚ] ℂ, ‖σ α‖ < 1 := by
    rw [← Finset.prod_const_one]
    have hσ_pos : ∀ σ : L →ₐ[ℚ] ℂ, 0 < ‖σ α‖ := by
      intro σ; rw [norm_pos_iff, ne_eq, ← map_zero σ]; exact σ.injective.ne hα_ne
    exact Finset.prod_lt_prod (fun σ _ => hσ_pos σ) (fun σ _ => hσ_bound σ)
      ⟨ι₀, Finset.mem_univ _, by rw [hι_val]; exact hlt⟩
  -- Norm(α) is integral over ℤ (hence an integer)
  have hα_int_L : IsIntegral ℤ (α : L) := by
    have : IsIntegral ℤ (algebraMap L ℂ α) := hint
    rwa [isIntegral_algebraMap_iff (algebraMap L ℂ).injective] at this
  have hnorm_int : IsIntegral ℤ (Algebra.norm ℚ (α : L)) :=
    Algebra.isIntegral_norm ℚ hα_int_L
  -- Norm(α) ≠ 0
  have hnorm_ne : Algebra.norm ℚ (α : L) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hα_ne
  -- |Norm(α)| ≥ 1 (nonzero integer)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm_int
  have hm_ne : m ≠ 0 := by
    intro h; exact hnorm_ne (by rw [← hm]; simp [h])
  -- ‖algebraMap ℚ ℂ (Norm α)‖ = ‖∏ σ(α)‖ = ∏ ‖σ(α)‖ < 1
  have h1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ (α : L))‖ < 1 := by
    rw [hprod]
    rw [show ‖∏ σ : L →ₐ[ℚ] ℂ, σ α‖ = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ α‖ from
      norm_prod (Finset.univ : Finset (L →ₐ[ℚ] ℂ)) (fun σ => σ α)]
    exact hprod_lt
  -- But ‖algebraMap ℚ ℂ (Norm α)‖ ≥ 1
  have h2 : 1 ≤ ‖algebraMap ℚ ℂ (Algebra.norm ℚ (α : L))‖ := by
    rw [← hm, ← IsScalarTower.algebraMap_apply ℤ ℚ ℂ m]
    rw [show (algebraMap ℤ ℂ) m = (m : ℂ) from map_intCast (algebraMap ℤ ℂ) m,
        Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm_ne
  linarith

open Finset in
/-- If ε₁, ..., εₙ are roots of unity and their average is an algebraic integer,
then either all εᵢ are equal or their sum is 0. (Etingof Lemma 5.4.5) -/
theorem Etingof.Lemma5_4_5
    (n : ℕ) (hn : 0 < n)
    (ε : Fin n → ℂ)
    (hε : ∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1)
    (hint : IsIntegral ℤ ((∑ i, ε i) / n)) :
    (∀ i j, ε i = ε j) ∨ (∑ i, ε i) = 0 := by
  by_cases hsum : (∑ i, ε i) = 0
  · exact Or.inr hsum
  · left
    have hnorm_one : ∀ i, ‖ε i‖ = 1 := by
      intro i
      obtain ⟨m, hm, hpow⟩ := hε i
      exact Complex.norm_eq_one_of_pow_eq_one hpow (Nat.pos_iff_ne_zero.mp hm)
    by_contra h
    push_neg at h
    obtain ⟨i, j, hij⟩ := h
    have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    have hlt : ‖(∑ i, ε i) / (n : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_natCast, div_lt_one (Nat.cast_pos.mpr hn)]
      have : ‖∑ k : Fin n, ((1 : ℝ) / n) • ε k‖ < 1 := by
        apply norm_sum_lt_of_strictConvexSpace (t := Finset.univ) (w := fun _ => (1 : ℝ) / n)
          (r := 1) (z := ε)
        · intro k _; positivity
        · simp [hnn]
        · exact Finset.mem_univ i
        · exact Finset.mem_univ j
        · exact hij
        · positivity
        · positivity
        · intro k _; rw [hnorm_one k]
      rw [← Finset.smul_sum] at this
      simp only [one_div, norm_smul, norm_inv, Real.norm_natCast] at this
      rwa [inv_mul_lt_iff₀ (Nat.cast_pos.mpr hn), mul_one] at this
    exact roots_of_unity_avg_norm_bound n hn ε hε hint hsum hlt

import Mathlib

/-!
# Lemma 5.2.6: Conjugates of Sums of Algebraic Numbers

If α₁, ..., αₘ are algebraic numbers, then every algebraic conjugate of
α = α₁ + ... + αₘ is of the form α₁' + ... + αₘ', where each αᵢ'
is an algebraic conjugate of αᵢ.

Etingof proves this via eigenvalues of tensor products of rational matrices
(`A₁ ⊗ I + I ⊗ A₂`). We instead use the equivalent Galois-theoretic formulation:
an algebraic conjugate `β` of `∑ αᵢ` is, by definition, a root of its minimal
polynomial, hence the image of `∑ αᵢ` under some `ℚ`-algebra homomorphism
`φ : ℚ⟮α₁, …, αₘ⟯ →ₐ[ℚ] ℂ` (such a `φ` exists because `ℂ` is algebraically
closed, so every minimal polynomial splits over it). Then `αᵢ' := φ(αᵢ)` are the
required conjugates: `∑ αᵢ' = φ(∑ αᵢ) = β`, and `αᵢ'` is a root of `minpoly ℚ αᵢ`
because `φ` is a `ℚ`-algebra homomorphism.

## Mathlib correspondence

Uses `IsConjRoot` (equality of minimal polynomials), `minpoly`, and
`IntermediateField.exists_algHom_adjoin_of_splits_of_aeval`.
-/

open Polynomial

/-- **Lemma 5.2.6.** Every algebraic conjugate `β` of a sum `α₁ + ⋯ + αₘ` of
algebraic numbers decomposes as `β = α₁' + ⋯ + αₘ'`, where each `αᵢ'` is an
algebraic conjugate of `αᵢ` (i.e. a root of `minpoly ℚ αᵢ`). (Etingof Lemma 5.2.6) -/
theorem Etingof.Lemma5_2_6
    (m : ℕ) (α : Fin m → ℂ) (hα : ∀ i, IsAlgebraic ℚ (α i))
    (β : ℂ) (hβ : IsConjRoot ℚ (∑ i, α i) β) :
    ∃ α' : Fin m → ℂ, (∀ i, IsConjRoot ℚ (α i) (α' i)) ∧ β = ∑ i, α' i := by
  classical
  -- The field generated over `ℚ` by all the `αᵢ`.
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α) with hK
  -- Each `αᵢ` lies in `K`.
  have mem : ∀ i, α i ∈ K :=
    fun i => IntermediateField.subset_adjoin ℚ (Set.range α) (Set.mem_range_self i)
  -- So does the sum `∑ αᵢ`.
  have hsum : (∑ i, α i) ∈ K := sum_mem (fun i _ => mem i)
  -- The minimal polynomial of each `αᵢ` (over `ℚ`) splits over `ℂ`, since `ℂ` is
  -- algebraically closed; and every `αᵢ` is integral over `ℚ`.
  have hsplits : ∀ s ∈ Set.range α, IsIntegral ℚ s ∧
      ((minpoly ℚ s).map (algebraMap ℚ ℂ)).Splits := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(hα i).isIntegral, IsAlgClosed.splits _⟩
  -- `β` is a root of `minpoly ℚ (∑ αᵢ)`.
  have hroot : (aeval β) (minpoly ℚ (∑ i, α i)) = 0 := hβ.aeval_eq_zero
  -- Extend the assignment `(∑ αᵢ) ↦ β` to a `ℚ`-algebra homomorphism out of `K`.
  obtain ⟨φ, hφ⟩ :=
    IntermediateField.exists_algHom_adjoin_of_splits_of_aeval hsplits hsum hroot
  -- The conjugates: `αᵢ' := φ(αᵢ)`.
  refine ⟨fun i => φ ⟨α i, mem i⟩, fun i => ?_, ?_⟩
  · -- `αᵢ'` is a conjugate of `αᵢ`: it is a root of `minpoly ℚ αᵢ`.
    apply isConjRoot_of_aeval_eq_zero (hα i).isIntegral
    rw [Polynomial.aeval_algHom_apply]
    have hz : (aeval (⟨α i, mem i⟩ : K)) (minpoly ℚ (α i)) = 0 := by
      rw [← map_eq_zero_iff K.val Subtype.val_injective, ← Polynomial.aeval_algHom_apply]
      simp
    rw [hz, map_zero]
  · -- `β = ∑ αᵢ'`.
    have hsum' : (∑ i, (⟨α i, mem i⟩ : K)) = ⟨∑ i, α i, hsum⟩ := by
      apply Subtype.ext
      push_cast
      rfl
    calc β = φ ⟨∑ i, α i, hsum⟩ := hφ.symm
      _ = φ (∑ i, (⟨α i, mem i⟩ : K)) := by rw [hsum']
      _ = ∑ i, φ ⟨α i, mem i⟩ := by rw [map_sum]

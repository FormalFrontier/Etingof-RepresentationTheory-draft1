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

/-- If ε₁, ..., εₙ are roots of unity and their average is an algebraic integer,
then either all εᵢ are equal or their sum is 0. (Etingof Lemma 5.4.5) -/
theorem Etingof.Lemma5_4_5
    (n : ℕ) (hn : 0 < n)
    (ε : Fin n → ℂ)
    (hε : ∀ i, ∃ m : ℕ, 0 < m ∧ (ε i) ^ m = 1)
    (hint : IsIntegral ℤ ((∑ i, ε i) / n)) :
    (∀ i j, ε i = ε j) ∨ (∑ i, ε i) = 0 := by
  sorry

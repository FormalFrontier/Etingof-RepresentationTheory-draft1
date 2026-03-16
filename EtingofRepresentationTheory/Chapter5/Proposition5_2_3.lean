import Mathlib

/-!
# Proposition 5.2.3: Equivalence of Algebraic Number Definitions

Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic numbers
and algebraic integers. The proof uses:
- (5.2.1 → 5.2.2): The companion matrix of a polynomial has the roots as eigenvalues.
- (5.2.2 → 5.2.1): An eigenvalue of a matrix is a root of its characteristic polynomial.

## Mathlib correspondence

The equivalence follows from `Matrix.charpoly` and companion matrix theory.
-/

/-- Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic numbers:
z is a root of a rational polynomial iff z is an eigenvalue of a rational matrix.
(Etingof Proposition 5.2.3) -/
theorem Etingof.Proposition5_2_3_algebraic (z : ℂ) :
    (∃ p : Polynomial ℚ, p ≠ 0 ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      (Matrix.charpoly (M.map (algebraMap ℚ ℂ))).IsRoot z) := by
  sorry

/-- Definitions 5.2.1 and 5.2.2 give equivalent characterizations of algebraic integers:
z is a root of a monic integer polynomial iff z is an eigenvalue of an integer matrix.
(Etingof Proposition 5.2.3) -/
theorem Etingof.Proposition5_2_3_integer (z : ℂ) :
    (∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval z p = 0) ↔
    (∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      (Matrix.charpoly (M.map (algebraMap ℤ ℂ))).IsRoot z) := by
  sorry

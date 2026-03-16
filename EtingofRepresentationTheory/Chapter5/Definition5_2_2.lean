import Mathlib

/-!
# Definition 5.2.2: Algebraic Numbers (Eigenvalue Characterization)

An equivalent characterization: z ∈ ℂ is an algebraic number (resp. integer) if and only
if z is an eigenvalue of a matrix with entries in ℚ (resp. ℤ).

## Mathlib correspondence

This is a theorem proving equivalence with Definition 5.2.1. Uses `Matrix.IsHermitian`,
eigenvalue theory, and companion matrices.
-/

/-- A complex number is algebraic if and only if it is an eigenvalue of a matrix
with rational entries. (Etingof Definition 5.2.2) -/
theorem Etingof.Definition5_2_2_algebraic
    (z : ℂ) :
    IsAlgebraic ℚ z ↔
    ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      (Matrix.charpoly (M.map (algebraMap ℚ ℂ))).IsRoot z := by
  sorry

/-- A complex number is an algebraic integer if and only if it is an eigenvalue of a matrix
with integer entries. (Etingof Definition 5.2.2) -/
theorem Etingof.Definition5_2_2_integer
    (z : ℂ) :
    IsIntegral ℤ z ↔
    ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
      (Matrix.charpoly (M.map (algebraMap ℤ ℂ))).IsRoot z := by
  sorry

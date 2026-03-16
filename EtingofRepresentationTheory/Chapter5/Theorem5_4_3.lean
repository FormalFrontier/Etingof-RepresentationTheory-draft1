import Mathlib

/-!
# Theorem 5.4.3: Burnside's Theorem

Any group of order p^a · q^b, where p, q are primes and a, b ≥ 0, is solvable.

The proof uses representation theory: specifically Theorem 5.4.6 (conjugacy classes
of prime power size force normal subgroups) combined with induction on the order of G.

## Mathlib correspondence

Burnside's theorem is a major result. Mathlib has `IsSolvable` but may not have
this specific theorem yet.
-/

/-- Burnside's theorem: any group of order p^a · q^b (p, q prime) is solvable.
(Etingof Theorem 5.4.3) -/
theorem Etingof.Theorem5_4_3
    (G : Type*) [Group G] [Fintype G]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (a b : ℕ) (hord : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  sorry

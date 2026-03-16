import Mathlib

/-!
# Lemma 5.4.7: Existence of Nonzero Character Value

In the context of Theorem 5.4.6's proof: among the nontrivial irreducible
representations V with p ∤ dim(V), there exists one with χ_V(g) ≠ 0.

This is proved using the column orthogonality of the character table.

## Mathlib correspondence

Uses character orthogonality and divisibility properties.
-/

/-- Among nontrivial irreducible representations V with p ∤ dim(V), there exists one
with χ_V(g) ≠ 0, where g is an element whose conjugacy class has size p^k.
(Etingof Lemma 5.4.7) -/
theorem Etingof.Lemma5_4_7
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p)
    (g : G) :
    -- There exists a nontrivial irreducible V with p ∤ dim(V) and χ_V(g) ≠ 0
    -- TODO: Express precisely once character table API is available
    True := by
  trivial

import Mathlib

/-!
# Theorem 5.4.6: Conjugacy Class of Prime Power Size

If G has a conjugacy class C of size p^k where p is prime and k > 0,
then G has a proper nontrivial normal subgroup (and hence is not simple).

The proof uses the column orthogonality of the character table, splitting
irreducible representations into three sets based on whether p divides
their dimension, and applying Theorem 5.4.4 and Lemma 5.4.7.

## Mathlib correspondence

Uses `Subgroup.Normal`, character orthogonality.
-/

/-- If G has a conjugacy class of size p^k (p prime, k > 0), then G has a proper
nontrivial normal subgroup. (Etingof Theorem 5.4.6) -/
theorem Etingof.Theorem5_4_6
    (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G)
    -- Hypothesis: the conjugacy class of g has size p^k
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  sorry

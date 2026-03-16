import Mathlib

/-!
# Corollary 4.2.2: Number of Irreducible Representations

The number of isomorphism classes of irreducible representations of G equals
the number of conjugacy classes of G (assuming k is algebraically closed and
char(k) does not divide |G|).

This follows from Theorem 4.2.1: irreducible characters form a basis of class functions,
and the dimension of the class function space equals the number of conjugacy classes.

## Mathlib correspondence

Mathlib has conjugacy classes via `ConjClasses G` and `Fintype (ConjClasses G)`.
The counting result requires the basis theorem (4.2.1).
-/

open FDRep CategoryTheory

universe u

/-- The number of isomorphism classes of irreducible representations equals the number
of conjugacy classes: there exist exactly `Fintype.card (ConjClasses G)` pairwise
non-isomorphic simple representations, and every simple representation is isomorphic
to one of them. (Etingof Corollary 4.2.2) -/
theorem Etingof.Corollary4_2_2
    {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {k : Type u} [Field k] [IsAlgClosed k]
    [Invertible (Fintype.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      n = Fintype.card (ConjClasses G) := by
  sorry

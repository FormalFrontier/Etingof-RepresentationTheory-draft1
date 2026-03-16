import Mathlib

/-!
# Lemma 5.7.2: Virtual Representation to Irreducible Criterion

If V is a virtual representation with (χ_V, χ_V) = 1 and χ_V(1) > 0,
then V is (the class of) an irreducible representation.

The proof: if V = Σ nᵢVᵢ, then (χ_V, χ_V) = Σ nᵢ² = 1 by orthonormality,
so exactly one nᵢ = ±1 and the rest are 0. Since χ_V(1) = Σ nᵢ dim(Vᵢ) > 0,
the nonzero coefficient must be +1.

## Mathlib correspondence

Uses character inner products and orthonormality of irreducible characters.
-/

/-- A virtual representation with inner product 1 and positive dimension at the identity
is irreducible. (Etingof Lemma 5.7.2) -/
theorem Etingof.Lemma5_7_2
    (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    -- If (χ_V, χ_V) = 1 and χ_V(1) > 0 for virtual representation V,
    -- then V is an irreducible representation
    -- TODO: Express precisely once virtual representation and character inner product API exist
    True := by
  trivial

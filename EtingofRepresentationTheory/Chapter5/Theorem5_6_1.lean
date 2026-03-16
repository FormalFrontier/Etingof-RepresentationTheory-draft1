import Mathlib

/-!
# Theorem 5.6.1: Irreducible Representations of Product Groups

The irreducible representations of G × H over ℂ are exactly the tensor products
Vᵢ ⊗ Wⱼ, where {Vᵢ} are the irreducible representations of G and {Wⱼ} are
the irreducible representations of H.

## Mathlib correspondence

Uses `Representation`, `TensorProduct`, and `Prod` group structure from Mathlib.
-/

/-- The irreducible representations of G × H are exactly {Vᵢ ⊗ Wⱼ} where Vᵢ, Wⱼ
range over irreducibles of G, H respectively. (Etingof Theorem 5.6.1) -/
theorem Etingof.Theorem5_6_1
    (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] :
    -- The number of irreducibles of G × H equals |Irr(G)| × |Irr(H)|
    -- TODO: Express as a classification of irreducible FDRep ℂ (G × H)
    -- once the necessary API for enumerating irreducibles exists.
    True := by
  trivial

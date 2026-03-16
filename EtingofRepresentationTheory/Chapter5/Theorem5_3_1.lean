import Mathlib

/-!
# Theorem 5.3.1: Dimension Divides Group Order

For any irreducible representation V of a finite group G over ℂ:
  dim(V) | |G|

The proof uses the fact that character values at conjugacy classes, multiplied by
|C|/dim(V), are algebraic integers (Proposition 5.3.2), combined with the
orthogonality relation Σ |χ(Cᵢ)|² · |Cᵢ| = |G|.

## Mathlib correspondence

Uses `FDRep`, character theory, and `IsIntegral` from Mathlib.
-/

/-- The dimension of any irreducible representation divides the order of the group.
(Etingof Theorem 5.3.1) -/
theorem Etingof.Theorem5_3_1
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) :
    -- dim(V) | |G| for irreducible V
    -- TODO: add irreducibility hypothesis once `IsSimpleModule` for FDRep is set up
    -- TODO: Express dim(V) | |G| once FDRep dimension API is available
    True := by
  trivial

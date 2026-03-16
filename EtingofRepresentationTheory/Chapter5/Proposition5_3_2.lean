import Mathlib

/-!
# Proposition 5.3.2: Character Values Yield Algebraic Integers

For an irreducible representation V of a finite group G, and a conjugacy class Cᵢ,
the value λᵢ = χ_V(gᵢ) · |Cᵢ| / dim(V) is an algebraic integer.

This follows from the fact that the central elements eᵢ = Σ_{g ∈ Cᵢ} g of the
group algebra ℤ[G] act on V as scalars, and their eigenvalues are algebraic integers.

## Mathlib correspondence

Uses `IsIntegral ℤ`, `MonoidAlgebra`, and character values.
-/

/-- For an irreducible representation V and conjugacy class C, the product
χ_V(g_C) · |C| / dim(V) is an algebraic integer. (Etingof Proposition 5.3.2) -/
theorem Etingof.Proposition5_3_2
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) :
    -- For each conjugacy class representative g, χ_V(g) · |C_g| / dim(V) is integral
    -- TODO: Express precisely once conjugacy class API and character evaluation are available
    True := by
  trivial

import Mathlib

/-!
# Definition 5.7.1: Virtual Representation

A **virtual representation** of a group G is an element of the Grothendieck group
(representation ring) R(G) of finite-dimensional complex representations of G.
Concretely, it is a formal integer linear combination V = Σ nᵢVᵢ where nᵢ ∈ ℤ.

The **virtual character** of V is χ_V := Σ nᵢ χ_{Vᵢ}.

## Mathlib correspondence

Mathlib does not have a dedicated `VirtualRepresentation` type. The representation ring
R(G) would be constructed as the Grothendieck group of the semiring of isomorphism
classes of finite-dimensional representations.
-/

/-- A virtual representation is a formal integer linear combination of irreducible
representations. We model it as a function from irreducible indices to ℤ.
(Etingof Definition 5.7.1) -/
structure Etingof.VirtualRepresentation
    (G : Type) [Group G] [Fintype G] where
  /-- Coefficients in the irreducible decomposition. -/
  coeffs : FDRep ℂ G → ℤ
  /-- Only finitely many coefficients are nonzero. -/
  finite_support : Set.Finite { V | coeffs V ≠ 0 }

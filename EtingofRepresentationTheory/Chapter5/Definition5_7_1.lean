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

namespace Etingof.VirtualRepresentation

variable {G : Type} [Group G] [Fintype G]

/-- The (virtual) character of a virtual representation `V = Σ nᵢ Vᵢ` is the
function `χ_V := Σ nᵢ χ_{Vᵢ}`, the corresponding integer combination of the
characters of the constituents. The sum ranges over the (finite) support of the
coefficient function. (Etingof Definition 5.7.1) -/
noncomputable def character (V : VirtualRepresentation G) (g : G) : ℂ :=
  ∑ W ∈ V.finite_support.toFinset, (V.coeffs W : ℂ) * W.character g

/-- The character of the zero virtual representation (all coefficients zero) is zero. -/
@[simp]
theorem character_zero (g : G)
    (h : Set.Finite { V : FDRep ℂ G | (0 : FDRep ℂ G → ℤ) V ≠ 0 }) :
    character ⟨0, h⟩ g = 0 := by
  simp [character]

end Etingof.VirtualRepresentation

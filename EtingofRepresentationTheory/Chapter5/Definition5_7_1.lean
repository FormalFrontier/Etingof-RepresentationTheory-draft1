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

open CategoryTheory in
/-- A virtual representation is a formal integer linear combination of **irreducible**
representations `V = Σ nᵢ Vᵢ`, `nᵢ ∈ ℤ`. We model it as an integer-valued coefficient
function on objects of `FDRep ℂ G`, subject to two conditions: the support is finite,
and every representation carrying a nonzero coefficient is irreducible (a `Simple`
object of the category). The latter condition is what makes this a combination of
irreducibles rather than of arbitrary representations.
(Etingof Definition 5.7.1) -/
structure Etingof.VirtualRepresentation
    (G : Type) [Group G] [Fintype G] where
  /-- Coefficients in the irreducible decomposition. -/
  coeffs : FDRep ℂ G → ℤ
  /-- Only finitely many coefficients are nonzero. -/
  finite_support : Set.Finite { V | coeffs V ≠ 0 }
  /-- Coefficients are supported on irreducible representations: any `V` with a nonzero
  coefficient is a simple (irreducible) object. This restricts the combination to one of
  irreducibles, as required by the book. -/
  support_simple : ∀ V, coeffs V ≠ 0 → Simple V

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
    (h : Set.Finite { V : FDRep ℂ G | (0 : FDRep ℂ G → ℤ) V ≠ 0 })
    (hs : ∀ V, (0 : FDRep ℂ G → ℤ) V ≠ 0 → CategoryTheory.Simple V) :
    character ⟨0, h, hs⟩ g = 0 := by
  simp [character]

end Etingof.VirtualRepresentation

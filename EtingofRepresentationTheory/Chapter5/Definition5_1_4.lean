import Mathlib

/-!
# Definition 5.1.4: Frobenius-Schur Indicator

The **Frobenius-Schur indicator** of an irreducible representation V is defined as:
  FS(V) = 0  if V is of complex type
  FS(V) = 1  if V is of real type
  FS(V) = -1 if V is of quaternionic type

Equivalently, FS(V) = (1/|G|) Σ_{g∈G} χ_V(g²).

## Mathlib correspondence

The Frobenius-Schur indicator is not in Mathlib. It can be defined using the character
formula FS(V) = (1/|G|) Σ_{g∈G} χ_V(g²).
-/

/-- The Frobenius-Schur indicator of a representation, computed as
(1/|G|) Σ_{g∈G} χ_V(g²). Returns 0, 1, or -1 for irreducible representations.
(Etingof Definition 5.1.4) -/
noncomputable def Etingof.frobeniusSchurIndicator
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ V (ρ (g * g))

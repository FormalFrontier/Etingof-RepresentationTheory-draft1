import Mathlib

/-!
# Theorem 5.9.1: Frobenius Formula for Induced Characters

For H ⊂ G, a representation V of H, and g ∈ G, the character of the
induced representation is:
  χ_{Ind_H^G V}(g) = Σ_{σ ∈ H\G : x_σ g x_σ⁻¹ ∈ H} χ_V(x_σ g x_σ⁻¹)

where {x_σ} is a set of coset representatives for H\G.

## Mathlib correspondence

Uses coset representatives, character theory, and the induced representation.
Frobenius reciprocity (the adjunction between induction and restriction) is not
yet in Mathlib.
-/

/-- The Frobenius character formula for induced representations:
χ_{Ind_H^G V}(g) = Σ_{σ : x_σ g x_σ⁻¹ ∈ H} χ_V(x_σ g x_σ⁻¹).
(Etingof Theorem 5.9.1) -/
theorem Etingof.Theorem5_9_1
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H V)
    (g : G) :
    -- χ_{Ind V}(g) = Σ over coset reps σ with σgσ⁻¹ ∈ H of χ_V(σgσ⁻¹)
    -- TODO: Express precisely once induced representation and character API are available
    True := by
  trivial

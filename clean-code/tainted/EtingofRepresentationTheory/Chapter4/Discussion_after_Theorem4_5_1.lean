import Mathlib

/-!
# Discussion after Theorem 4.5.1: Irreducibility criterion

Theorem 4.5.1 (orthogonality of characters) gives a powerful method of checking
whether a complex representation `V` of a finite group `G` is irreducible: `V` is
irreducible if and only if `(χ_V, χ_V) = 1`, where

  `(χ_V, χ_V) = (1/|G|) Σ_{g∈G} χ_V(g) χ_V(g⁻¹)`.

The forward direction is part (ii) of Theorem 4.5.1 (the diagonal case `V ≅ V`); the
reverse direction is the content of this criterion. We package both as a single
biconditional, in the normalized form used throughout the project.

## Mathlib correspondence

This is `FDRep.simple_iff_char_is_norm_one` (which states it in the un-normalized
form `Σ_g χ_V(g) χ_V(g⁻¹) = |G|`), repackaged with the `(1/|G|)` normalization.
-/

open FDRep CategoryTheory

universe u

/-- Irreducibility criterion (discussion after Etingof Theorem 4.5.1): a
finite-dimensional representation `V` of a finite group `G` over an algebraically
closed field of characteristic zero is irreducible if and only if the normalized
inner product `⟨χ_V, χ_V⟩ = (1/|G|) Σ_g χ_V(g) χ_V(g⁻¹)` equals `1`. -/
theorem Etingof.Discussion_after_Theorem4_5_1
    {k G : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) :
    Simple V ↔
      ⅟(Fintype.card G : k) • ∑ g : G, V.character g * V.character g⁻¹ = 1 := by
  rw [simple_iff_char_is_norm_one V, smul_eq_mul]
  rw [show ((Nat.card G : k)) = (Fintype.card G : k) from by rw [Fintype.card_eq_nat_card]]
  constructor
  · intro h; rw [h]; exact invOf_mul_self _
  · intro h
    have h2 := congrArg (fun x => (Fintype.card G : k) * x) h
    simpa only [mul_one, ← mul_assoc, mul_invOf_self, one_mul] using h2

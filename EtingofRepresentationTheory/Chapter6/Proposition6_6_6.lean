import Mathlib

/-!
# Proposition 6.6.6: Inverse Relationship of Reflection Functors

(1) If φ : ⊕_{j→i} V_j → V_i is surjective, then F⁻ᵢ F⁺ᵢ V = V.
(2) If ψ : V_i → ⊕_{i→j} V_j is injective, then F⁺ᵢ F⁻ᵢ V = V.

The proof uses the homomorphism theorem: when φ is surjective, K = ker φ embeds
in ⊕V_j, and then (⊕V_j)/K ≅ Im φ = V_i.

## Mathlib correspondence

Requires reflection functor definitions (Definition 6.6.3 and 6.6.4) and
quiver representation isomorphism. Not in Mathlib.
-/

/-- If φ is surjective at a sink, then applying F⁻ᵢ after F⁺ᵢ recovers V.
(Etingof Proposition 6.6.6, part 1) -/
theorem Etingof.Proposition6_6_6_sink :
    (sorry : Prop) := -- TODO: needs reflection functor definitions
  sorry

/-- If ψ is injective at a source, then applying F⁺ᵢ after F⁻ᵢ recovers V.
(Etingof Proposition 6.6.6, part 2) -/
theorem Etingof.Proposition6_6_6_source :
    (sorry : Prop) := -- TODO: needs reflection functor definitions
  sorry

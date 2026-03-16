import Mathlib

/-!
# Proposition 6.6.7: Reflection Preserves Indecomposability

Let Q be a quiver and V an indecomposable representation. Then F⁺ᵢ(V) and F⁻ᵢ(V)
(whenever defined) are either indecomposable or 0.

The proof: if φ is not surjective, F⁺ᵢ(V) = 0. If φ is surjective and
F⁺ᵢ(V) = X ⊕ Y is decomposable, then X and Y are injective at i (since
F⁺ᵢ(V) is), so by Proposition 6.6.6, V = F⁻ᵢ(X) ⊕ F⁻ᵢ(Y), contradicting
indecomposability of V.

## Mathlib correspondence

Requires reflection functor definitions and indecomposable representation API.
Not in Mathlib.
-/

/-- Reflection functors preserve indecomposability: F⁺ᵢ(V) is indecomposable or zero.
(Etingof Proposition 6.6.7) -/
theorem Etingof.Proposition6_6_7 :
    (sorry : Prop) := -- TODO: needs reflection functor and indecomposable API
  sorry

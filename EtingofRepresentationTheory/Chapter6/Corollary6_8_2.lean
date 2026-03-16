import Mathlib

/-!
# Corollary 6.8.2: Dimension Vectors Are Positive Roots

For any indecomposable representation V of a Dynkin quiver Q, d(V) is a positive root,
i.e., B(d(V), d(V)) = 2.

The proof: by Theorem 6.8.1, s_{i₁} ⋯ s_{iₘ}(d(V)) = αₚ. Since the sᵢ preserve B,
B(d(V), d(V)) = B(αₚ, αₚ) = 2.

## Mathlib correspondence

Requires dimension vectors, simple reflections preserving the bilinear form,
and Theorem 6.8.1. This is part of Gabriel's theorem (classification of
quivers of finite representation type).
-/

/-- The dimension vector of any indecomposable representation of a Dynkin quiver
is a positive root. (Etingof Corollary 6.8.2) -/
theorem Etingof.Corollary6_8_2 :
    (sorry : Prop) := -- TODO: needs Theorem 6.8.1 and bilinear form on roots
  sorry

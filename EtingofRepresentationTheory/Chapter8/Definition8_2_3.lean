import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Definition 8.2.3: Tor functors

Let M be a right A-module, P• a projective resolution of M, and N a left A-module.
For i ≥ 0 we define Torᵢᴬ(M, N) to be the i-th homology of the complex
  ⋯ → P₂ ⊗_A N → P₁ ⊗_A N → P₀ ⊗_A N → 0
induced by the resolution P•.

## Mathlib correspondence

Mathlib has `Tor` defined as a derived functor of the tensor product. The API may be
limited for concrete computations.

## Formalization note

The definition uses derived category machinery. The sorry'd statement stands in for the
full construction pending further Mathlib API development for Tor.
-/

/-- The Tor functors, defined as derived functors of the tensor product.
(Etingof Definition 8.2.3) -/
theorem Etingof.Definition_8_2_3 : (sorry : Prop) := sorry

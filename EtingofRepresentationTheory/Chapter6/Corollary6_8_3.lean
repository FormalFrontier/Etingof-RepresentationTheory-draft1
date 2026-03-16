import Mathlib

/-!
# Corollary 6.8.3: Dimension Vector Determines Indecomposable Representation

If V, V' are indecomposable representations of a Dynkin quiver Q with d(V) = d(V'),
then V ≅ V'.

The proof: let i be minimal such that d(V⁽ⁱ⁾) = αₚ. Then d(V'⁽ⁱ⁾) = αₚ too,
so V⁽ⁱ⁾ = V'⁽ⁱ⁾. Both sequences satisfy surjectivity conditions, so applying
inverse functors gives V = V'.

Together with Corollary 6.8.2, this shows there are finitely many indecomposable
representations (one for each positive root).

## Mathlib correspondence

Requires Theorem 6.8.1, reflection functor invertibility (Proposition 6.6.6),
and quiver representation isomorphism. Not in Mathlib.
-/

/-- Indecomposable representations of a Dynkin quiver are determined (up to isomorphism)
by their dimension vectors. (Etingof Corollary 6.8.3) -/
theorem Etingof.Corollary6_8_3 :
    (sorry : Prop) := -- TODO: needs Theorem 6.8.1 and reflection functor invertibility
  sorry

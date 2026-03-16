import Mathlib

/-!
# Corollary 6.8.4: Every Positive Root Is Realized

For every positive root α of a Dynkin quiver Q, there exists an indecomposable
representation V with d(V) = α.

The proof constructs V explicitly: apply the sequence s_n, s_{n-1}s_n, … to α
until reaching a simple root αᵢ. Then build V = F⁻_n F⁻_{n-1} ⋯ F⁻_q k_{(i)}
where k_{(i)} is the simple representation at vertex i on the appropriately
reoriented quiver.

This completes Gabriel's theorem: indecomposable representations of Dynkin quivers
are in bijection with positive roots.

## Mathlib correspondence

Requires full reflection functor machinery and the construction of simple
representations. Not in Mathlib.
-/

/-- Every positive root of a Dynkin quiver is the dimension vector of some
indecomposable representation. (Etingof Corollary 6.8.4) -/
theorem Etingof.Corollary6_8_4 :
    (sorry : Prop) := -- TODO: needs reflection functor construction
  sorry

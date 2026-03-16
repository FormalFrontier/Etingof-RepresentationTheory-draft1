import Mathlib

/-!
# Proposition 6.6.8: Dimension Vector Under Reflection

(1) Let i be a sink and V surjective at i. Then d(F⁺ᵢ V) = sᵢ(d(V)).
(2) Let i be a source and V injective at i. Then d(F⁻ᵢ V) = sᵢ(d(V)).

where sᵢ is the simple reflection and d(V) is the dimension vector.

The proof computes dim(ker φ) = Σ_{j→i} dim V_j − dim V_i, showing that the
change in dimension vector at i equals −B(d(V), αᵢ), which is exactly sᵢ(d(V)).

## Mathlib correspondence

Requires reflection functors, dimension vectors, simple reflections, and the
bilinear form B on the root lattice. Mathlib has `CoxeterSystem` with simple
reflections, but the connection to quiver representations is not formalized.
-/

/-- At a sink with surjective map, the dimension vector transforms by the
simple reflection: d(F⁺ᵢ V) = sᵢ(d(V)). (Etingof Proposition 6.6.8, part 1) -/
theorem Etingof.Proposition6_6_8_sink :
    (sorry : Prop) := -- TODO: needs dimension vector and simple reflection API
  sorry

/-- At a source with injective map, the dimension vector transforms by the
simple reflection: d(F⁻ᵢ V) = sᵢ(d(V)). (Etingof Proposition 6.6.8, part 2) -/
theorem Etingof.Proposition6_6_8_source :
    (sorry : Prop) := -- TODO: needs dimension vector and simple reflection API
  sorry

import Mathlib

/-!
# Theorem 6.8.1: Reaching Simple Roots via Reflection Functors

There exists m ∈ ℕ such that d(V⁽ᵐ⁾) = αₚ for some vertex p, where V⁽ⁱ⁾ is the
sequence obtained by repeatedly applying reflection functors.

The proof: if V⁽ⁱ⁾ is surjective at the appropriate vertex k, then
d(V⁽ⁱ⁺¹⁾) = sₖ d(V⁽ⁱ⁾). By Lemma 6.7.2, this cannot continue indefinitely
(dimension vectors must remain non-negative). When it stops, by Proposition 6.6.5,
d(V⁽ⁱ⁾) = αₚ for some p.

This is the key technical step toward Gabriel's theorem.

## Mathlib correspondence

Requires the full infrastructure of reflection functors (Def 6.6.3-4),
dimension vectors, Propositions 6.6.5-6.6.8, and Lemma 6.7.2.
Not in Mathlib.
-/

/-- For any indecomposable representation V of a Dynkin quiver, repeated application
of reflection functors eventually produces a simple representation at some vertex.
(Etingof Theorem 6.8.1) -/
theorem Etingof.Theorem6_8_1 :
    (sorry : Prop) := -- TODO: needs full reflection functor infrastructure
  sorry

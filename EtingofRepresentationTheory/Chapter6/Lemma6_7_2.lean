import Mathlib

/-!
# Lemma 6.7.2: Coxeter Element Produces Negative Coefficients

Let β = Σᵢ kᵢ αᵢ with kᵢ ≥ 0 (not all zero). Then there exists N ∈ ℕ such that
cᴺβ has at least one strictly negative coefficient.

The proof shows that 1 is not an eigenvalue of the Coxeter element c. Since
c ∈ W (a finite group), cᴹ = 1 for some M, so 1 + c + c² + ⋯ + cᴹ⁻¹ = 0
as operators on ℝⁿ. If cv = v, then sᵢv = v for all i, implying B(v, αᵢ) = 0
for all i, contradicting nondegeneracy of B.

## Mathlib correspondence

Requires Coxeter groups, simple reflections, the bilinear form B, and its
nondegeneracy for Dynkin diagrams. Mathlib has Coxeter systems but the specific
eigenvalue argument needs custom development.
-/

/-- For a positive linear combination of simple roots (not all zero), some power of
the Coxeter element produces a vector with a negative coefficient.
(Etingof Lemma 6.7.2) -/
theorem Etingof.Lemma6_7_2 :
    (sorry : Prop) := -- TODO: needs Coxeter element, root system, bilinear form API
  sorry

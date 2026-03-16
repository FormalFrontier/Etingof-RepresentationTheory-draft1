import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Definition 9.4.1: Projective dimension

A module M has a **projective resolution** if there exists an exact sequence
… → P₁ → P₀ → M → 0 where each Pᵢ is projective.

The **projective dimension** pd(M) of M is the length of the shortest finite projective
resolution of M. If no finite projective resolution exists, pd(M) = ∞.

## Mathlib correspondence

Not directly in Mathlib. Could be formalized using `CategoryTheory.ProjectiveResolution`
and computing the length.
-/

/-- The projective dimension of a module, in the sense of Etingof Definition 9.4.1.
The length of the shortest finite projective resolution, or ∞ if none exists. -/
noncomputable def Etingof.projectiveDimension : (sorry : Prop) := sorry

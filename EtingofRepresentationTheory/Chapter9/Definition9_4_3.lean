import Mathlib.Algebra.Module.Projective

/-!
# Definition 9.4.3: Homological dimension of a ring

A ring A is said to have (left/right) **homological dimension** ≤ d if every (left/right)
A-module has projective dimension ≤ d. The smallest such d is the homological dimension
of A. If no such d exists, the homological dimension is infinite.

## Mathlib correspondence

Not directly in Mathlib. Could be formalized as the supremum of projective dimensions
over all modules.
-/

/-- The homological dimension of a ring, in the sense of Etingof Definition 9.4.3.
The supremum of projective dimensions of all modules. -/
noncomputable def Etingof.homologicalDimension : (sorry : Prop) := sorry

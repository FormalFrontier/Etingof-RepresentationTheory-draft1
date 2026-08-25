import Mathlib.Algebra.Lie.Basic

/-!
# Definition 2.9.1: Lie Algebra

(𝔤, [·, ·]) is a **Lie algebra** if [·, ·] satisfies the Jacobi identity:
[[a, b], c] + [[b, c], a] + [[c, a], b] = 0.

## Mathlib correspondence

This is `LieAlgebra R L` with `LieRing L`. The Jacobi identity is built into `LieRing`.
-/

/-- A Lie algebra, in the sense of Etingof Definition 2.9.1.
This is `LieAlgebra k L` with `LieRing L` in Mathlib. -/
abbrev Etingof.LieAlgebraDef (k : Type*) (L : Type*) [CommRing k] [LieRing L] :=
  LieAlgebra k L

namespace Etingof

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

/-- The Jacobi identity in the cyclic, left-nested form used in equation (2.9.1). -/
theorem jacobi_identity (a b c : L) :
    ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by
  rw [← neg_eq_zero]
  simpa only [neg_add_rev, neg_neg, lie_skew, add_comm, add_left_comm, add_assoc] using
    lie_jacobi c a b

end Etingof

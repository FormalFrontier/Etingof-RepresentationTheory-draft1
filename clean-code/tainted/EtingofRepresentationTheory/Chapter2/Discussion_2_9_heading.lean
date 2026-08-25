import Mathlib.Algebra.Lie.Basic

/-!
# §2.9 heading: skew-symmetric bilinear brackets

The section begins with a vector space `L` over a field `k` and a skew-symmetric bilinear map
`[·, ·] : L × L → L`.  In Mathlib this is the bracket underlying a `LieAlgebra k L`.
The declarations below expose the three properties stated in the text: bilinearity,
`[x, x] = 0`, and the resulting skew-symmetry `[x, y] = -[y, x]`.
-/

namespace Etingof.Discussion2_9

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

/-- The Lie bracket is additive in its first argument. -/
theorem bracket_add_left (x y z : L) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ :=
  LieRing.add_lie x y z

/-- The Lie bracket is additive in its second argument. -/
theorem bracket_add_right (x y z : L) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ :=
  LieRing.lie_add x y z

/-- The Lie bracket is homogeneous in its first argument. -/
theorem bracket_smul_left (a : k) (x y : L) : ⁅a • x, y⁆ = a • ⁅x, y⁆ := by
  calc
    ⁅a • x, y⁆ = -⁅y, a • x⁆ := (lie_skew _ _).symm
    _ = -(a • ⁅y, x⁆) := congrArg Neg.neg (LieAlgebra.lie_smul a y x)
    _ = a • ⁅x, y⁆ := by rw [← smul_neg, lie_skew]

/-- The Lie bracket is homogeneous in its second argument. -/
theorem bracket_smul_right (a : k) (x y : L) : ⁅x, a • y⁆ = a • ⁅x, y⁆ :=
  LieAlgebra.lie_smul a x y

/-- The alternating condition in the book: `[x, x] = 0`. -/
theorem bracket_self (x : L) : ⁅x, x⁆ = 0 := lie_self x

/-- The skew-symmetry deduced from the alternating condition: `[x, y] = -[y, x]`. -/
theorem bracket_skew (x y : L) : ⁅x, y⁆ = -⁅y, x⁆ := (lie_skew x y).symm

end Etingof.Discussion2_9

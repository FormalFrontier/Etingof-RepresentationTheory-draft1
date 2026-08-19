/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Lie bracket identities -/

namespace RepresentationTheory.LieAlgebra.BracketIdentities

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

/-- The bracket distributes over addition in its left argument. -/
@[source_ref "Chapter2/Discussion_2.9_heading" (role := supporting)]
theorem bracket_add_left (x y z : L) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ :=
  LieRing.add_lie x y z

/-- The bracket distributes over addition in its right argument. -/
@[source_ref "Chapter2/Discussion_2.9_heading" (role := supporting)]
theorem bracket_add_right (x y z : L) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ :=
  LieRing.lie_add x y z

/-- Scalar multiplication may be pulled out of the left argument of a Lie bracket. -/
@[source_ref "Chapter2/Discussion_2.9_heading" (role := supporting)]
theorem bracket_smul_left (a : k) (x y : L) : ⁅a • x, y⁆ = a • ⁅x, y⁆ := by
  calc
    ⁅a • x, y⁆ = -⁅y, a • x⁆ := (lie_skew _ _).symm
    _ = -(a • ⁅y, x⁆) := congrArg Neg.neg (LieAlgebra.lie_smul a y x)
    _ = a • ⁅x, y⁆ := by rw [← smul_neg, lie_skew]

/-- Scalar multiplication may be pulled out of the right argument of a Lie bracket. -/
@[source_ref "Chapter2/Discussion_2.9_heading" (role := supporting)]
theorem bracket_smul_right (a : k) (x y : L) : ⁅x, a • y⁆ = a • ⁅x, y⁆ :=
  LieAlgebra.lie_smul a x y

/-- The bracket of an element with itself is zero. -/
@[source_ref "Chapter2/Discussion_2.9_heading" (role := primary)]
theorem bracket_self (x : L) : ⁅x, x⁆ = 0 := lie_self x

/-- Interchanging the arguments of a bracket negates its value. -/
@[source_ref "Chapter2/Discussion_2.9_heading" (role := primary)]
theorem bracket_eq_neg_bracket_swap (x y : L) : ⁅x, y⁆ = -⁅y, x⁆ := (lie_skew x y).symm

end RepresentationTheory.LieAlgebra.BracketIdentities

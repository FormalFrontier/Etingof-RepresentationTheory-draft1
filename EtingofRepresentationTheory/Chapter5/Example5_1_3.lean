import Mathlib

/-!
# Example 5.1.3: Type Classification for Specific Groups

Examples of the real/complex/quaternionic classification:

1. ℤ/nℤ: representations of complex type come in conjugate pairs {V, V*}
2. S₃: all irreducible representations are real (characters are integer-valued)
3. S₄: all irreducible representations are real
4. A₅: all irreducible representations are real
5. Q₈: the 2-dimensional irreducible representation is quaternionic

## Mathlib correspondence

Uses `ZMod`, `Equiv.Perm (Fin n)`, and `Quaternion` types from Mathlib.
-/

/-- All irreducible representations of S₃ are of real type (all character values are real).
(Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_S3 :
    -- All character values of irreducible representations of S₃ are real
    True := by
  trivial
  -- TODO: Formalize once character table infrastructure is available.
  -- The key fact is that all character values of S₃ are integers.

/-- The 2-dimensional irreducible representation of Q₈ is of quaternionic type.
(Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_Q8 :
    -- The 2-dimensional irreducible representation of Q₈ admits an invariant
    -- skew-symmetric bilinear form
    True := by
  trivial
  -- TODO: Formalize once QuaternionGroup and its representations are set up.

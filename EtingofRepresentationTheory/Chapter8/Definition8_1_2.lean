import Mathlib.Algebra.Module.Projective

/-!
# Definition 8.1.2: Projective module

A module satisfying any of the conditions (i)–(iv) of Theorem 8.1.1 is said to be
**projective**.

## Mathlib correspondence

This is exactly `Module.Projective R M` in Mathlib, which asserts that M is a projective
R-module via the lifting property.
-/

/-- A projective module, in the sense of Etingof Definition 8.1.2.
This is `Module.Projective R M` in Mathlib. -/
abbrev Etingof.ProjectiveModule (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] :=
  Module.Projective R M

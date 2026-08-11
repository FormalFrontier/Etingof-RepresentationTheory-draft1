import Mathlib.Algebra.Module.Injective

/-!
# Definition 8.1.6: Injective module

A module satisfying any of the conditions (i)–(iii) of Theorem 8.1.5 is said to be
**injective**.

## Mathlib correspondence

This is exactly `Module.Injective R M` in Mathlib, which asserts that M is an injective
R-module via the extension property.
-/

/-- An injective module, in the sense of Etingof Definition 8.1.6.
This is `Module.Injective R M` in Mathlib. -/
abbrev Etingof.InjectiveModule (R : Type*) (M : Type*) [Ring R] [AddCommGroup M]
    [Module R M] :=
  Module.Injective R M

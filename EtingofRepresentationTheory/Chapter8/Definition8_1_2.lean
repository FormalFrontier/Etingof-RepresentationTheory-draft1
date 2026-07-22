import Mathlib.Algebra.Module.Projective

/-!
# Definition 8.1.2: Projective module

A module satisfying any of the conditions (i)–(iv) of Theorem 8.1.1 is said to be
**projective**.

## Mathlib correspondence

This is exactly `Module.Projective R M` in Mathlib, which asserts that M is a projective
R-module via the lifting property.

The book works over a general (possibly non-commutative) ring/algebra, so we require only
`[Ring R]` — matching Theorem 8.1.1's `[Ring R]` setting and the book's module theory over an
arbitrary algebra `A`. (Narrowing to `CommRing` would silently exclude the non-commutative rings
that are central to the chapter; `Module.Projective` itself needs only a semiring.)
-/

/-- A projective module, in the sense of Etingof Definition 8.1.2.
This is `Module.Projective R M` in Mathlib, over a general ring `R`. -/
abbrev Etingof.ProjectiveModule (R : Type*) (M : Type*) [Ring R] [AddCommGroup M]
    [Module R M] :=
  Module.Projective R M

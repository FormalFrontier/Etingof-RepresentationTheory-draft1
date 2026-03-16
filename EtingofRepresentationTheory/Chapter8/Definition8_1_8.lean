import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Definition 8.1.8: Projective and injective objects in abelian categories

A **projective object** in an abelian category C is an object P such that the functor
Hom_C(P, ?) is exact.

An **injective object** in an abelian category C is an object I such that the functor
Hom_C(?, I) is exact.

## Mathlib correspondence

These are exactly `CategoryTheory.Projective` and `CategoryTheory.Injective` in Mathlib.
-/

/-- A projective object in an abelian category, in the sense of Etingof Definition 8.1.8.
This is `CategoryTheory.Projective P` in Mathlib. -/
abbrev Etingof.ProjectiveObject {C : Type*} [CategoryTheory.Category C] (P : C) :=
  CategoryTheory.Projective P

/-- An injective object in an abelian category, in the sense of Etingof Definition 8.1.8.
This is `CategoryTheory.Injective I` in Mathlib. -/
abbrev Etingof.InjectiveObject {C : Type*} [CategoryTheory.Category C] (I : C) :=
  CategoryTheory.Injective I

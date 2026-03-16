import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Definition 8.2.1: Projective resolution

A **projective resolution** of M is an exact sequence
  ⋯ → P₂ → P₁ → P₀ → M → 0
such that all modules Pᵢ, i ≥ 0, are projective.

## Mathlib correspondence

This is exactly `CategoryTheory.ProjectiveResolution X` in Mathlib, which provides a
projective resolution of an object X in an abelian category.
-/

/-- A projective resolution, in the sense of Etingof Definition 8.2.1.
This is `CategoryTheory.ProjectiveResolution X` in Mathlib. -/
abbrev Etingof.ProjectiveResolution {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (X : C) :=
  CategoryTheory.ProjectiveResolution X

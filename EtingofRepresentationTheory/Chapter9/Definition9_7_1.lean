import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Definition 9.7.1: Morita equivalence

Two finite dimensional algebras A and B are **Morita equivalent** if the categories
A-fmod and B-fmod are equivalent as abelian categories.

## Mathlib correspondence

This can be expressed as `CategoryTheory.Equivalence (ModuleCat R) (ModuleCat S)` in Mathlib,
though the finite-dimensional constraint requires additional bundling.
-/

/-- Morita equivalence of finite dimensional algebras, in the sense of Etingof Definition 9.7.1.
A and B are Morita equivalent if their module categories are equivalent. -/
def Etingof.MoritaEquivalent : (sorry : Prop) := sorry

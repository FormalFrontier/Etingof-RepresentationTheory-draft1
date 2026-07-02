import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Definition 7.9.1: Additive and k-linear Functor

A functor F between two abelian categories is **additive** if it induces
homomorphisms on Hom groups.

For k-linear categories, F is **k-linear** if it induces k-linear maps
between Hom spaces.

## Mathlib correspondence

Exact match:
- `CategoryTheory.Functor.Additive` for additive functors
- `CategoryTheory.Functor.Linear` for k-linear functors
-/

/-- An additive functor between preadditive categories, in the sense of
Etingof Definition 7.9.1. This is `CategoryTheory.Functor.Additive` in Mathlib. -/
abbrev Etingof.AdditiveFunctor {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] [CategoryTheory.Preadditive C]
    [CategoryTheory.Preadditive D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Functor.Additive F

/-- A `k`-linear functor between `k`-linear categories, in the sense of the
second half of Etingof Definition 7.9.1: `F` induces `k`-linear maps between
Hom spaces. This is `CategoryTheory.Functor.Linear` in Mathlib. -/
abbrev Etingof.LinearFunctor (k : Type*) [Semiring k] {C : Type*} {D : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
    [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
    (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Functor.Linear k F

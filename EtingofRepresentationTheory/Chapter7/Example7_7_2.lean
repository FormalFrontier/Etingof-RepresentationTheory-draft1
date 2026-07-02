import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-!
# Example 7.7.2: Module Categories are Abelian

The category of modules over an algebra A and the category of finite dimensional
modules over A are abelian categories.

## Mathlib correspondence

The book makes two claims:
(a) the category of all modules over A is abelian, and
(b) the category of finite dimensional modules over A is abelian.

Part (a) is an exact match: `ModuleCat A` is an abelian category in Mathlib via
`ModuleCat.instAbelian`.

Part (b) is captured by `FGModuleCat A`, the category of finitely generated
A-modules. Mathlib proves `Abelian (FGModuleCat A)` whenever A is a (left-)
Noetherian ring (`Mathlib.Algebra.Category.FGModuleCat.Abelian`). In Etingof's
setting A is a finite dimensional algebra over a field, hence Artinian and so
Noetherian, and an A-module is finite dimensional (over the base field) exactly
when it is finitely generated over A. Thus `FGModuleCat A` for Noetherian A is
the faithful rendering of the finite dimensional module category. Specializing A
to the base field k recovers the category of finite dimensional vector spaces,
which is likewise abelian.
-/

open CategoryTheory

/-- The category of modules over a ring A is an abelian category.
(Etingof Example 7.7.2, part (a)) -/
example (A : Type*) [Ring A] : Abelian (ModuleCat A) := inferInstance

/-- The category of finite dimensional modules over A is an abelian category.
For a finite dimensional algebra A over a field, A is Noetherian and the finitely
generated A-modules are exactly the finite dimensional ones, so this is Mathlib's
`Abelian (FGModuleCat A)`.
(Etingof Example 7.7.2, part (b)) -/
example (A : Type*) [Ring A] [IsNoetherianRing A] : Abelian (FGModuleCat A) :=
  inferInstance

/-- Specializing to the base field k: the category of finite dimensional vector
spaces is abelian. -/
example (k : Type*) [Field k] : Abelian (FGModuleCat k) := inferInstance

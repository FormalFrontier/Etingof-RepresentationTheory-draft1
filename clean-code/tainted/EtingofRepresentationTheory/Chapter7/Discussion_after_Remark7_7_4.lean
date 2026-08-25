import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.FGModuleCat.Basic
import EtingofRepresentationTheory.Chapter7.Example7_7_2

/-!
# Discussion after Remark 7.7.4: k-linear abelian categories

An abelian category `𝒞` is **k-linear** (for a field `k`) if the groups
`Hom_𝒞(X, Y)` are equipped with a `k`-vector space structure and composition is
`k`-linear in each argument. The text remarks that the categories in Example 7.7.2
(modules over a `k`-algebra `A`, and finite-dimensional modules over `A`) are
`k`-linear.

## Mathlib correspondence

Exact match. For a field `k` and a `k`-algebra `A`, Mathlib provides the
`CategoryTheory.Linear k (ModuleCat A)` instance, and the induced full-subcategory
structure makes `FGModuleCat A` linear as well. When `A` is finite dimensional over `k`,
finite generation over `A` is equivalent, objectwise after restriction of scalars, to
finite dimensionality over `k` by `module_finite_iff_finiteDimensional`.
-/

open CategoryTheory

/-- The category of all modules over a `k`-algebra is `k`-linear. -/
@[reducible] def Etingof.moduleCatLinear (k : Type*) [Field k] (A : Type*) [Ring A]
    [Algebra k A] :
    Linear k (ModuleCat A) := inferInstance

/-- The category of all modules over a ring is abelian. -/
@[reducible] noncomputable def Etingof.moduleCatAbelian (A : Type*) [Ring A] :
    Abelian (ModuleCat A) := inferInstance

/-- For a finite-dimensional `k`-algebra, its category of finite-dimensional modules,
realized as `FGModuleCat A`, is `k`-linear. -/
@[reducible] def Etingof.fgModuleCatLinear (k : Type*) [Field k] (A : Type*) [Ring A]
    [Algebra k A]
    [FiniteDimensional k A] : Linear k (FGModuleCat A) := inferInstance

/-- For a finite-dimensional `k`-algebra, its category of finite-dimensional modules,
realized as `FGModuleCat A`, is abelian. -/
@[reducible] noncomputable def Etingof.fgModuleCatAbelian (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] [FiniteDimensional k A] : Abelian (FGModuleCat A) :=
  abelian_fgModuleCat_of_finiteDimensional k A

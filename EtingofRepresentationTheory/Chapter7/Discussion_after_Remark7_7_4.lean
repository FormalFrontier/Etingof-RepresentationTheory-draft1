import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# Discussion after Remark 7.7.4: k-linear abelian categories

An abelian category `𝒞` is **k-linear** (for a field `k`) if the groups
`Hom_𝒞(X, Y)` are equipped with a `k`-vector space structure and composition is
`k`-linear in each argument. The text remarks that the categories in Example 7.7.2
(modules over a `k`-algebra `A`, and finite-dimensional modules over `A`) are
`k`-linear.

## Mathlib correspondence

Exact match. For a field `k` and a `k`-algebra `A`, `ModuleCat.linearOverField`
provides the `CategoryTheory.Linear k (ModuleCat A)` instance.
-/

open CategoryTheory

/-- Discussion after Remark 7.7.4: for a field `k` and `k`-algebra `A`, the category
of `A`-modules is `k`-linear. -/
example (k : Type*) [Field k] (A : Type*) [Ring A] [Algebra k A] :
    Linear k (ModuleCat A) := inferInstance

import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# Example 7.1.6: Rep(A) is Enriched over k-vector spaces

The category Rep(A) of representations of a k-algebra A is enriched over the
category of k-vector spaces. That is, the Hom spaces carry a k-module structure.

Representations of a k-algebra `A` are the same as `A`-modules, i.e. objects of
`ModuleCat A`. The claim is that for a k-algebra `A`, the category `ModuleCat A`
is `k`-linear: each Hom space `M ⟶ N` is a `k`-vector space and composition is
`k`-bilinear.

## Mathlib correspondence

`ModuleCat.linearOverField` provides `Linear k (ModuleCat A)` for a field `k`
and a `k`-algebra `A`. The Hom-space `k`-module structure comes from restricting
scalars along `k → A`.
-/

open CategoryTheory

/-- The category of representations of a `k`-algebra `A` (i.e. `A`-modules) is
`k`-linear, hence enriched over the category of `k`-vector spaces.
(Etingof Example 7.1.6) -/
example (k : Type*) [Field k] (A : Type*) [Ring A] [Algebra k A] :
    Linear k (ModuleCat A) := inferInstance

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Definition 9.6.1: Finite abelian category

A **finite abelian category** over a field k is an abelian category 𝒞 which has enough
projectives, and in which there are finitely many simple objects (up to isomorphism).

The primary example is the category of finite dimensional modules over a finite
dimensional k-algebra.

## Mathlib correspondence

Mathlib has `CategoryTheory.Abelian` for abelian categories and
`CategoryTheory.EnoughProjectives` for the enough projectives condition. The finiteness
condition on simple objects is not bundled in Mathlib.
-/

/-- A finite abelian category in the sense of Etingof Definition 9.6.1.
An abelian category with enough projectives and finitely many simple objects. -/
def Etingof.FiniteAbelianCategory : (sorry : Prop) := sorry

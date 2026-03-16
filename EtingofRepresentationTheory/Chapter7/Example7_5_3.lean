import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Example 7.5.3: Representable Forgetful Functor

Let A be an algebra. Then the forgetful functor from the category of left A-modules
to the category of vector spaces is representable, and the representing object is
the free rank 1 module (= the regular representation) M = A.

But if A is infinite dimensional and we restrict to finite dimensional modules,
the forgetful functor is in general not representable.

## Mathlib correspondence

The core equivalence `Hom_R(R, M) ≃ M` is `LinearMap.ringLmapEquivSelf` in Mathlib,
which says the forgetful functor from R-modules to types is representable by R.
-/

/-- The forgetful functor from R-mod to Type is representable by the free module R.
(Etingof Example 7.5.3)

The representing object is R itself (the regular representation): the map `f ↦ f(1)`
gives an equivalence `Hom_R(R, M) ≃ M` for any R-module M. -/
noncomputable def Etingof.forgetful_representable
    (R : Type*) [Semiring R] (M : Type*) [AddCommMonoid M] [Module R M] :
    (R →ₗ[R] M) ≃ₗ[ℕ] M :=
  LinearMap.ringLmapEquivSelf R ℕ M

import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-!
# Definition 8.1.8: Projective and injective objects in abelian categories

A **projective object** in an abelian category C is an object P such that the functor
Hom_C(P, ?) is exact.

An **injective object** in an abelian category C is an object I such that the functor
Hom_C(?, I) is exact.

## Mathlib correspondence

Mathlib's `CategoryTheory.Projective` and `CategoryTheory.Injective` use the
equivalent lifting and extension properties.  The theorems
`Etingof.projectiveObject_iff` and `Etingof.injectiveObject_iff` below prove the
book's exact-Hom characterizations.  They use Mathlib's canonical enriched Hom
functors, valued in modules over the appropriate endomorphism ring; forgetting
the module structure recovers the usual additive Hom functors.
-/

/-- A projective object in an abelian category, in the sense of Etingof Definition 8.1.8.
This is `CategoryTheory.Projective P` in Mathlib. -/
abbrev Etingof.ProjectiveObject {C : Type*} [CategoryTheory.Category C] (P : C) :=
  CategoryTheory.Projective P

/-- An injective object in an abelian category, in the sense of Etingof Definition 8.1.8.
This is `CategoryTheory.Injective I` in Mathlib. -/
abbrev Etingof.InjectiveObject {C : Type*} [CategoryTheory.Category C] (I : C) :=
  CategoryTheory.Injective I

/-- Etingof's characterization of projective objects: `P` is projective if and
only if the covariant Hom functor `Hom(P, -)` is exact.  For functors between
abelian categories, exactness is expressed here by preservation of finite
limits and finite colimits.  The finite-limit (left-exact) half holds for every
`P`; projectivity is precisely what supplies the finite-colimit half. -/
theorem Etingof.projectiveObject_iff {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (P : C) :
    Etingof.ProjectiveObject P ↔
      CategoryTheory.Limits.PreservesFiniteLimits
          (CategoryTheory.preadditiveCoyonedaObj P) ∧
        CategoryTheory.Limits.PreservesFiniteColimits
          (CategoryTheory.preadditiveCoyonedaObj P) := by
  open CategoryTheory CategoryTheory.Limits in
  constructor
  · intro h
    haveI : Projective P := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨_, h⟩
    haveI : PreservesFiniteColimits (preadditiveCoyonedaObj P) := h
    exact projective_of_preservesFiniteColimits_preadditiveCoyonedaObj P

/-- Etingof's characterization of injective objects: `I` is injective if and
only if the contravariant Hom functor `Hom(-, I)` is exact.  As a covariant
functor on the opposite category, exactness again means preservation of finite
limits and finite colimits.  Its finite-limit half is automatic, while
injectivity is precisely the finite-colimit half. -/
theorem Etingof.injectiveObject_iff {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (I : C) :
    Etingof.InjectiveObject I ↔
      CategoryTheory.Limits.PreservesFiniteLimits
          (CategoryTheory.preadditiveYonedaObj I) ∧
        CategoryTheory.Limits.PreservesFiniteColimits
          (CategoryTheory.preadditiveYonedaObj I) := by
  open CategoryTheory CategoryTheory.Limits in
  constructor
  · intro h
    haveI : Injective I := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨_, h⟩
    haveI : PreservesFiniteColimits (preadditiveYonedaObj I) := h
    exact injective_of_preservesFiniteColimits_preadditiveYonedaObj I

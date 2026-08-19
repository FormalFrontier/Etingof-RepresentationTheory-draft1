/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Linear.LinearFunctor
import RepresentationTheory.Alignment.Attribute

/-!
# Additive and linear functors

This module records additivity and linearity properties of induction, restriction,
co-Yoneda, and restriction-of-scalars functors.
-/

open CategoryTheory Opposite

namespace RepresentationTheory.CategoryTheory.LinearFunctors

set_option backward.defeqAttrib.useBackward true in
/-- A left adjoint is linear when its right adjoint is both additive and linear. -/
lemma leftAdjoint_linear_of_rightAdjoint_additive_linear
    {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (R : Type*) [Semiring R] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive] [G.Linear R] : F.Linear R where
  map_smul {X Y} f r :=
    (adj.homEquiv X (F.obj Y)).injective (by simp [Adjunction.homEquiv_unit])

section GroupRepresentations

universe u

variable {k G H : Type u} [Field k] [Group G] [Group H] (φ : G →* H)

/-- Restriction along a group homomorphism is an additive functor. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem resFunctor_additive : (Rep.resFunctor (k := k) φ).Additive := inferInstance

/-- Restriction along a group homomorphism is linear over the coefficient field. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem resFunctor_linear : (Rep.resFunctor (k := k) φ).Linear k := inferInstance

/-- Induction along a group homomorphism is an additive functor. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem indFunctor_additive : (Rep.indFunctor.{u} k φ).Additive :=
  (Rep.indResAdjunction k φ).left_adjoint_additive

/-- Induction along a group homomorphism is linear over the coefficient field. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem indFunctor_linear : (Rep.indFunctor.{u} k φ).Linear k :=
  leftAdjoint_linear_of_rightAdjoint_additive_linear k (Rep.indResAdjunction k φ)

variable (V : Rep k G)

/-- The linear co-Yoneda functor evaluated at a representation is additive. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem linearCoyoneda_obj_additive : ((linearCoyoneda k (Rep k G)).obj (op V)).Additive :=
  inferInstance

/-- The linear co-Yoneda functor evaluated at a representation is linear over the coefficient field. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem linearCoyoneda_obj_linear : ((linearCoyoneda k (Rep k G)).obj (op V)).Linear k where
  map_smul {X Y} f r := by
    ext g
    exact Linear.comp_smul V X Y g r f

end GroupRepresentations

open scoped ModuleCat.Algebra

/-- Restriction of scalars along a ring homomorphism is an additive functor. -/
instance restrictScalars_additive
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Functor.Additive (ModuleCat.restrictScalars f) :=
  inferInstance

/-- Restriction of scalars along an algebra homomorphism is linear over the base semiring. -/
instance restrictScalars_linear
    {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S]
    [Algebra R₀ R] [Algebra R₀ S] (f : R →ₐ[R₀] S) :
    Functor.Linear R₀ (ModuleCat.restrictScalars f.toRingHom) :=
  inferInstance

end RepresentationTheory.CategoryTheory.LinearFunctors

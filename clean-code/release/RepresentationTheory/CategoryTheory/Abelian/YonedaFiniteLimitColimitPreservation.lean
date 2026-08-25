/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.CategoryTheory.Abelian.YonedaFiniteLimitColimitPreservation

/-- A property of an object in a category. -/
@[source_ref "Chapter8/Definition8.1.8" (role := supporting),
  source_ref "Chapter8/Discussion_after_Example8.1.7" (role := supporting)]
abbrev coyonedaObjectProperty {C : Type*} [CategoryTheory.Category C] (P : C) :=
  CategoryTheory.Projective P

/-- A property of an object in a category. -/
@[source_ref "Chapter8/Definition8.1.8" (role := supporting),
  source_ref "Chapter8/Discussion_after_Example8.1.7" (role := supporting)]
abbrev yonedaObjectProperty {C : Type*} [CategoryTheory.Category C] (I : C) :=
  CategoryTheory.Injective I

/-- In an abelian category, the Coyoneda object property holds exactly when the associated
preadditive Coyoneda functor preserves finite limits and finite colimits. -/
@[source_ref "Chapter8/Definition8.1.8" (role := primary)]
theorem coyonedaObjectProperty_iff {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (P : C) :
    coyonedaObjectProperty P ↔
      CategoryTheory.Limits.PreservesFiniteLimits
          (CategoryTheory.preadditiveCoyonedaObj P) ∧
        CategoryTheory.Limits.PreservesFiniteColimits
          (CategoryTheory.preadditiveCoyonedaObj P) := by
  open _root_.CategoryTheory _root_.CategoryTheory.Limits in
  constructor
  · intro h
    haveI : Projective P := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨_, h⟩
    haveI : PreservesFiniteColimits (preadditiveCoyonedaObj P) := h
    exact projective_of_preservesFiniteColimits_preadditiveCoyonedaObj P

/-- In an abelian category, the Yoneda object property holds exactly when the associated
preadditive Yoneda functor preserves finite limits and finite colimits. -/
@[source_ref "Chapter8/Definition8.1.8" (role := primary)]
theorem yonedaObjectProperty_iff {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (I : C) :
    yonedaObjectProperty I ↔
      CategoryTheory.Limits.PreservesFiniteLimits
          (CategoryTheory.preadditiveYonedaObj I) ∧
        CategoryTheory.Limits.PreservesFiniteColimits
          (CategoryTheory.preadditiveYonedaObj I) := by
  open _root_.CategoryTheory _root_.CategoryTheory.Limits in
  constructor
  · intro h
    haveI : Injective I := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨_, h⟩
    haveI : PreservesFiniteColimits (preadditiveYonedaObj I) := h
    exact injective_of_preservesFiniteColimits_preadditiveYonedaObj I

end RepresentationTheory.CategoryTheory.Abelian.YonedaFiniteLimitColimitPreservation

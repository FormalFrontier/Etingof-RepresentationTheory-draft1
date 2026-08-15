/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import RepresentationTheory.Alignment.Attribute

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.EnrichedCorepresentability

universe w v u

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- An auxiliary type operator parameterized by a monoidal category. -/
@[source_ref "Chapter7/Discussion_after_Example7.1.5" (role := primary)]
abbrev AuxiliaryMonoidalTypeOperator (C : Type u) := CategoryTheory.EnrichedCategory V C

/-- The composition morphism between enriched hom-objects. -/
@[source_ref "Chapter7/Discussion_after_Example7.1.5" (role := primary)]
abbrev enrichedComposition {C : Type u} [CategoryTheory.EnrichedCategory V C]
    (X Y Z : C) :=
  CategoryTheory.eComp V X Y Z

variable {C : Type u} [Category C] [EnrichedOrdinaryCategory V C]

/-- States that a functor from an enriched ordinary category into its enriching category is
enriched corepresentable. -/
@[source_ref "Chapter7/Remark7.5.2" (role := supporting)]
def IsEnrichedCorepresentable (F : Functor C V) : Prop :=
  ∃ X : C, Nonempty (F ≅ eCoyoneda V X)

/-- Characterizes enriched corepresentability by isomorphism with an enriched co-Yoneda functor. -/
theorem isEnrichedCorepresentable_iff (F : Functor C V) :
    IsEnrichedCorepresentable V F ↔ ∃ X : C, Nonempty (F ≅ eCoyoneda V X) :=
  Iff.rfl

/-- The enriched co-Yoneda functor is enriched corepresentable. -/
@[source_ref "Chapter7/Remark7.5.2" (role := primary)]
theorem isEnrichedCorepresentable_eCoyoneda (X : C) :
    IsEnrichedCorepresentable V (eCoyoneda V X) :=
  ⟨X, ⟨Iso.refl _⟩⟩

/-- The enriched co-Yoneda functor has a nonempty type of self-isomorphisms. -/
theorem eCoyoneda_selfIso_nonempty (X : C) :
    Nonempty (eCoyoneda V X ≅ eCoyoneda V X) :=
  ⟨Iso.refl _⟩

end RepresentationTheory.CategoryTheory.EnrichedCorepresentability

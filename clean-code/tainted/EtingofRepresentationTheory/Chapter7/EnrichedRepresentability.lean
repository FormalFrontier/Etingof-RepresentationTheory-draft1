/-
Copyright (c) 2026 FormalFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier contributors
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Enriched categories and representable enriched-valued functors

The discussion after Example 7.1.5 replaces hom-sets by hom-objects in a monoidal category
and requires composition to be a morphism in that category.  Mathlib packages exactly this
data as `CategoryTheory.EnrichedCategory`, with composition `CategoryTheory.eComp`.

Remark 7.5.2 extends representability to this setting.  When an ordinary category `C` is
compatibly enriched over `V`, a functor `F : C ⟶ V` is enriched-representable when it is
naturally isomorphic to the enriched coyoneda functor `X ⟶ (X ⟶[V] -)` for some `X`.
-/

open CategoryTheory

namespace Etingof

universe w v u

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- Discussion after Example 7.1.5: a category enriched over the monoidal category `V`.

This source-facing abbreviation re-exports Mathlib's `CategoryTheory.EnrichedCategory`.
Its fields are the enriched hom-object, identity morphism, composition morphism, and the
unit and associativity laws. -/
abbrev EnrichedCategory (C : Type u) := CategoryTheory.EnrichedCategory V C

/-- Discussion after Example 7.1.5: composition of enriched hom-objects is a morphism in
the enriching category.  This is the source-facing name for `CategoryTheory.eComp`. -/
abbrev enrichedComposition {C : Type u} [CategoryTheory.EnrichedCategory V C]
    (X Y Z : C) :=
  CategoryTheory.eComp V X Y Z

variable {C : Type u} [Category C] [EnrichedOrdinaryCategory V C]

/-- Remark 7.5.2: a `V`-valued functor on a `V`-enriched ordinary category is
representable when it is naturally isomorphic to enriched hom from some object. -/
def EnrichedRepresentable (F : Functor C V) : Prop :=
  ∃ X : C, Nonempty (F ≅ eCoyoneda V X)

/-- The definition of enriched representability, exposed as a convenient iff. -/
theorem enrichedRepresentable_iff (F : Functor C V) :
    EnrichedRepresentable V F ↔ ∃ X : C, Nonempty (F ≅ eCoyoneda V X) :=
  Iff.rfl

/-- The enriched coyoneda functor represented by `X` is enriched-representable, with
representing object `X`. -/
theorem eCoyoneda_enrichedRepresentable (X : C) :
    EnrichedRepresentable V (eCoyoneda V X) :=
  ⟨X, ⟨Iso.refl _⟩⟩

/-- A direct witness form of `eCoyoneda_enrichedRepresentable`. -/
theorem eCoyoneda_representedBy (X : C) :
    Nonempty (eCoyoneda V X ≅ eCoyoneda V X) :=
  ⟨Iso.refl _⟩

end Etingof

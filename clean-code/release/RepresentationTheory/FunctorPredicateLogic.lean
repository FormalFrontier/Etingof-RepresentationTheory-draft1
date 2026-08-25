/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Limits.Preserves.Finite
import RepresentationTheory.Alignment.Attribute

/-!
# Logic for functor predicates

Definitions and elementary results for two proposition-valued predicates on functors and their
conjunction.
-/

namespace RepresentationTheory.FunctorPredicateLogic

/-- The left-hand proposition-valued predicate on functors in a conjunction. -/
@[source_ref "Chapter7/Definition7.9.3" (role := supporting)]
abbrev Left {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Limits.PreservesFiniteLimits F

/-- The right-hand proposition-valued predicate on functors in a conjunction. -/
@[source_ref "Chapter7/Definition7.9.3" (role := supporting)]
abbrev Right {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Limits.PreservesFiniteColimits F

/-- A proposition-valued functor predicate equivalent to the conjunction of two other predicates. -/
@[source_ref "Chapter7/Definition7.9.3" (role := supporting),
  source_ref "Chapter7/Introduction_7.9" (role := supporting)]
def Conjunction {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : CategoryTheory.Functor C D) : Prop :=
  Left F ∧ Right F

variable {C : Type*} {D : Type*} [CategoryTheory.Category C]
  [CategoryTheory.Category D] {F : CategoryTheory.Functor C D}

/-- The conjunction predicate holds exactly when its left- and right-hand predicates both hold. -/
@[source_ref "Chapter7/Definition7.9.3" (role := supporting)]
theorem conjunction_iff : Conjunction F ↔ Left F ∧ Right F :=
  Iff.rfl

/-- The conjunction predicate implies its left-hand predicate. -/
theorem Conjunction.left (h : Conjunction F) : Left F :=
  h.1

/-- The conjunction predicate implies its right-hand predicate. -/
theorem Conjunction.right (h : Conjunction F) : Right F :=
  h.2

/-- The left- and right-hand predicates imply the conjunction predicate. -/
theorem Conjunction.of_left_right (hL : Left F) (hR : Right F) : Conjunction F :=
  ⟨hL, hR⟩

end RepresentationTheory.FunctorPredicateLogic

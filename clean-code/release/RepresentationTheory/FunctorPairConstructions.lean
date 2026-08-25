/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.NatTrans
import RepresentationTheory.Alignment.Attribute

/-!
# Constructions for pairs of functors

This module provides constructions associated with pairs of functors between the same categories.
-/

namespace RepresentationTheory.FunctorPairConstructions

/-- The type associated with two functors between the same pair of categories. -/
@[source_ref "Chapter7/Definition7.3.1" (role := supporting)]
abbrev associatedType {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F G : CategoryTheory.Functor C D) :=
  CategoryTheory.NatTrans F G

end RepresentationTheory.FunctorPairConstructions

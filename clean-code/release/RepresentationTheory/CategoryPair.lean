/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Functor.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Category pairs

This module defines a type associated with a pair of categories.
-/

namespace RepresentationTheory.CategoryPair

/-- A universe-polymorphic type associated with a pair of categories. -/
@[source_ref "Chapter7/Definition7.2.1" (role := supporting),
  source_ref "Chapter7/Introduction_7.2" (role := supporting)]
abbrev AssociatedType (C : Type*) (D : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Category D] := CategoryTheory.Functor C D

end RepresentationTheory.CategoryPair

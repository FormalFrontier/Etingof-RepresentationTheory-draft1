/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.CategoryTheory.Equivalence
import RepresentationTheory.Alignment.Attribute

/-!
# Categories

This module defines a type parameterized by two categories.
-/

namespace RepresentationTheory.Categories

/-- A type parameterized by two categories. -/
@[source_ref "Chapter7/Definition7.4.1" (role := primary)]
abbrev ParameterizedType (C : Type*) (D : Type*) [CategoryTheory.Category C]
    [CategoryTheory.Category D] := CategoryTheory.Equivalence C D

end RepresentationTheory.Categories

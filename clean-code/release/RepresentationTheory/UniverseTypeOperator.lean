/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Category.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Universe Type Operator

This module defines a universe type operator.
-/

namespace RepresentationTheory.UniverseTypeOperator

/-- A universe-polymorphic operation assigning to each type a type in a universe large enough for the input level and an additional successor level. -/
@[source_ref "Chapter7/Definition7.1.1" (role := supporting)]
abbrev TypeOperator (C : Type*) := CategoryTheory.Category C

end RepresentationTheory.UniverseTypeOperator

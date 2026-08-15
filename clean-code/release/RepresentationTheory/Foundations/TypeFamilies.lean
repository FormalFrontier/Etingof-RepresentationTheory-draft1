/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Combinatorics.Quiver.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Type families -/

namespace RepresentationTheory.Foundations.TypeFamilies

/-- A universe-polymorphic family of types indexed by a type. -/
abbrev TypeIndexedFamily (V : Type*) := Quiver V

attribute [source_ref "Chapter2/Discussion_after_Theorem2.1.1" (role := supporting)]
  TypeIndexedFamily
attribute [source_ref "Chapter2/Definition2.8.1" (role := supporting)] TypeIndexedFamily

end RepresentationTheory.Foundations.TypeFamilies

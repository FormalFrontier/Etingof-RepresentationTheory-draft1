/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Combinatorics.Quiver.Basic

/-! # Type families -/

namespace RepresentationTheory.Foundations.TypeFamilies

/-- A universe-polymorphic family of types indexed by a type. -/
abbrev TypeIndexedFamily (V : Type*) := Quiver V

end RepresentationTheory.Foundations.TypeFamilies

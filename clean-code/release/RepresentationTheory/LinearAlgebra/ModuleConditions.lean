/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.SimpleModule.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Conditions on modules
-/

namespace RepresentationTheory.LinearAlgebra.ModuleConditions

/-- A predicate on a module over a ring. -/
@[source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable" (role := primary),
  source_ref "Chapter2/Definition2.3.5" (role := supporting)]
abbrev ModuleCondition (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] :=
  IsSimpleModule A V

end RepresentationTheory.LinearAlgebra.ModuleConditions

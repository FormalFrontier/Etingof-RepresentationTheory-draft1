/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.GroupTheory.GroupAction.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Module predicates -/

namespace RepresentationTheory.LinearAlgebra.ModulePredicates

/-- An auxiliary predicate on a module over a ring. -/
@[source_ref "Chapter2/Definition2.7.3" (role := primary)]
abbrev AuxiliaryModulePredicate (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] :=
  FaithfulSMul A V

end RepresentationTheory.LinearAlgebra.ModulePredicates

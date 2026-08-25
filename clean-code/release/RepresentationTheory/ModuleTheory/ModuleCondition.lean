/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.SimpleModule.Basic

/-! # A condition on modules -/

namespace RepresentationTheory.ModuleTheory.ModuleCondition

/-- A proposition associated with a module over a ring. -/
abbrev ModuleCondition (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] :=
  IsSemisimpleModule A V

end RepresentationTheory.ModuleTheory.ModuleCondition

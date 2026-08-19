/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.SimpleModule.Basic
import RepresentationTheory.Alignment.Attribute

/-- An auxiliary proposition depending on a module over a ring. -/
@[source_ref "Chapter3/Definition3.1.1" (role := supporting)]
abbrev RepresentationTheory.ModuleTheory.AuxiliaryCondition.AuxiliaryModuleCondition (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] :=
  IsSemisimpleModule A V

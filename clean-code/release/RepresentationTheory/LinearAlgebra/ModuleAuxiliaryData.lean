/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.Span.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary data for modules
-/

set_option linter.dupNamespace false

namespace RepresentationTheory.LinearAlgebra.ModuleAuxiliaryData

/-- An auxiliary type associated with a module over a ring. -/
@[source_ref "Chapter2/Discussion_2.1_overview/Derived6" (role := supporting),
  source_ref "Chapter2/Definition2.3.4" (role := supporting)]
abbrev ModuleAuxiliaryData (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] :=
  Submodule A V

/-- An auxiliary value associated with a module over a ring. -/
@[source_ref "Chapter2/Definition2.3.4" (role := supporting)]
abbrev moduleAuxiliaryData (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : ModuleAuxiliaryData A V :=
  ⊤

/-- A second auxiliary value associated with a module over a ring. -/
@[source_ref "Chapter2/Definition2.3.4" (role := supporting)]
abbrev moduleAuxiliaryData' (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : ModuleAuxiliaryData A V :=
  ⊥

end RepresentationTheory.LinearAlgebra.ModuleAuxiliaryData

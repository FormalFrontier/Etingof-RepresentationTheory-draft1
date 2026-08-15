/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Order.RelSeries
import Mathlib.Algebra.Module.Submodule.Lattice
import RepresentationTheory.Alignment.Attribute

/-! # Module composition data -/

namespace RepresentationTheory.Module.CompositionData

/-- Inductive data associated with a module from which an increasing relational series of submodules is obtained. -/
structure ModuleCompositionData (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] where
  /-- The relational series of submodules determined by module composition data. -/
  toRelSeries : RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2}
  /-- The first submodule in the relational series determined by module composition data is the bottom submodule. -/
  toRelSeries_head : toRelSeries.head = ⊥
  /-- The last submodule in the relational series determined by module composition data is the top submodule. -/
  toRelSeries_last : toRelSeries.last = ⊤

attribute [source_ref "Chapter3/Definition3.4.1" (role := primary)]
  ModuleCompositionData.toRelSeries ModuleCompositionData.toRelSeries_head
  ModuleCompositionData.toRelSeries_last

end RepresentationTheory.Module.CompositionData

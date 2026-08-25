/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Order.RelSeries
import Mathlib.Algebra.Module.Submodule.Lattice
import RepresentationTheory.Alignment.Attribute

/-- An auxiliary type associated with a module. -/
structure RepresentationTheory.Module.RelSeriesAuxiliary.ModuleRelSeriesAuxiliary (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] where

  /-- The relational series associated with the auxiliary module data. -/
  toRelSeries : RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2}

  /-- The head of the associated relational series is bottom. -/
  toRelSeries_head : toRelSeries.head = ⊥

  /-- The last term of the associated relational series is top. -/
  toRelSeries_last : toRelSeries.last = ⊤

attribute [source_ref "Chapter3/Definition3.4.1" (role := primary)]
  RepresentationTheory.Module.RelSeriesAuxiliary.ModuleRelSeriesAuxiliary.toRelSeries
attribute [source_ref "Chapter3/Definition3.4.1" (role := primary)]
  RepresentationTheory.Module.RelSeriesAuxiliary.ModuleRelSeriesAuxiliary.toRelSeries_head
attribute [source_ref "Chapter3/Definition3.4.1" (role := primary)]
  RepresentationTheory.Module.RelSeriesAuxiliary.ModuleRelSeriesAuxiliary.toRelSeries_last

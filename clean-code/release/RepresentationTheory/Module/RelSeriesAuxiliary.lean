/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Order.RelSeries
import Mathlib.Algebra.Module.Submodule.Lattice
import RepresentationTheory.Alignment.Attribute

structure RepresentationTheory.Module.RelSeriesAuxiliary.ModuleRelSeriesAuxiliary (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] where

  toRelSeries : RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2}

  toRelSeries_head : chain.head = ⊥

  toRelSeries_last : chain.last = ⊤

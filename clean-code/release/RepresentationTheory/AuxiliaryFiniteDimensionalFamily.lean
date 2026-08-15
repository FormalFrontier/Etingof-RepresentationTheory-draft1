/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary Finite-Dimensional Family

This module defines an auxiliary natural-number value for a finite family of finite-dimensional
vector spaces.
-/

/-- An auxiliary natural-number value assigned to each member of a finite family of finite-dimensional vector spaces. -/
@[source_ref "Chapter6/Definition6.5.1" (role := supporting)]
noncomputable def RepresentationTheory.AuxiliaryFiniteDimensionalFamily.auxiliaryNatValue
    {V : Type*} [Fintype V] (k : Type*)
    [Field k] (spaces : V → Type*)
    [∀ v, AddCommGroup (spaces v)] [∀ v, Module k (spaces v)]
    [∀ v, FiniteDimensional k (spaces v)] :
    V → ℕ :=
  fun v => Module.finrank k (spaces v)

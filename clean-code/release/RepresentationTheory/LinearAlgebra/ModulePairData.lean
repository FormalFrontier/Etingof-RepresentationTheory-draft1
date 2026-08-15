/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Module.Equiv.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Data relating pairs of modules
-/

namespace RepresentationTheory.LinearAlgebra.ModulePairData

/-- Data parameterized by an ordered pair of modules over one ring. -/
@[source_ref "Chapter2/Definition2.3.6" (role := supporting)]
abbrev ModulePairDatum (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂] :=
  V₁ ≃ₗ[A] V₂

/-- A further type of data attached to two modules with the same scalars. -/
@[source_ref "Chapter2/Definition2.3.6" (role := supporting)]
abbrev ModulePairWitness (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂] :=
  V₁ →ₗ[A] V₂

/-- A relation between two modules over a common ring. -/
@[source_ref "Chapter2/Definition2.3.6" (role := supporting)]
abbrev ModulePairRelation (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂] : Prop :=
  Nonempty (ModulePairDatum A V₁ V₂)

end RepresentationTheory.LinearAlgebra.ModulePairData

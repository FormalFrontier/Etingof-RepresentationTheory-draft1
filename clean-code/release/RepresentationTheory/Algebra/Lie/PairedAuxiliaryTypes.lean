/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary types for pairs of Lie algebras -/

namespace RepresentationTheory.Algebra.Lie.PairedAuxiliaryTypes

/-- An auxiliary type depending on two Lie algebras over a commutative ring. -/
@[source_ref "Chapter2/Definition2.9.6" (role := supporting)]
abbrev LieAlgebra.AuxiliaryType (k : Type*) (L₁ L₂ : Type*) [CommRing k]
    [LieRing L₁] [LieRing L₂] [LieAlgebra k L₁] [LieAlgebra k L₂] :=
  L₁ →ₗ⁅k⁆ L₂

end RepresentationTheory.Algebra.Lie.PairedAuxiliaryTypes

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Complex.Basic

/-! # A complex matrix Lie subalgebra -/

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices

/-- A distinguished complex Lie subalgebra of two-by-two complex matrices. -/
abbrev complexTwoByTwoMatrixLieSubalgebra : LieSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

end RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices

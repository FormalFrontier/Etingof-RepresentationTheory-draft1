/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary integer matrix-vector property

This module defines an auxiliary property of a finite integer vector relative to a square integer
matrix.
-/

/-- An auxiliary property of an integer-valued finite vector relative to a square integer matrix. -/
@[source_ref "Chapter6/Definition6.4.3" (role := supporting)]
def RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix (n : ℕ)
    (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  x ≠ 0 ∧ dotProduct x ((2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj).mulVec x) = 2

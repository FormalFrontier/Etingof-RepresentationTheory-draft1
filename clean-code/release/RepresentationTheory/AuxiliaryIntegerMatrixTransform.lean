/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary integer matrix transform

This module defines an auxiliary transformation of square integer matrices indexed by a finite
type.
-/

/-- An auxiliary transformation of square integer matrices indexed by a finite type. -/
@[source_ref "Chapter6/Definition6.4.1" (role := primary)]
def RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform (n : ℕ)
    (adj : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj

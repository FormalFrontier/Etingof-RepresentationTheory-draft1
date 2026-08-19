/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary finite-index integer function

This module defines an integer-valued function on a pair of indices in the same finite type.
-/

/-- An auxiliary integer-valued function of two indices in the same finite type. -/
@[source_ref "Chapter6/Definition6.4.5" (role := supporting)]
def RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue (n : ℕ) (i : Fin n) :
    Fin n → ℤ :=
  Pi.single i 1

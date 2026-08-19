/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary integer vector transforms

This module defines auxiliary transformations of integer-valued vectors indexed by finite types.
-/

/-- An auxiliary transformation of an integer-valued finite vector determined by a matrix and a second vector. -/
@[source_ref "Chapter6/Definition6.4.10" (role := supporting)]
def RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (α : Fin n → ℤ) (v : Fin n → ℤ) : Fin n → ℤ :=
  v - (dotProduct v (A.mulVec α)) • α

/-- An auxiliary transformation of an integer-valued finite vector determined by a matrix and a selected coordinate. -/
@[source_ref "Chapter6/Definition6.4.10" (role := supporting)]
def RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : (Fin n → ℤ) → (Fin n → ℤ) :=
  RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform n A
    (Pi.single i 1)

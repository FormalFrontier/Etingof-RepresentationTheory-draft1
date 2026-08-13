/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.AuxiliaryIntegerVectorTransforms
import RepresentationTheory.Alignment.Attribute

/-!
# Integer Matrix-Vector Coordinate Function

An auxiliary integer-valued function determined by a square integer matrix and a finite vector.
-/

/-- An integer-valued function of a square integer matrix, an integer vector, and a finite index. -/
@[source_ref "Chapter6/Definition6.7.1" (role := supporting)]
def RepresentationTheory.IntegerMatrixVectorCoordinateFunction.matrixVectorCoordinateValue
    (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) : Fin n → ℤ :=
  let A := RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform n adj
  (List.ofFn (fun i : Fin n =>
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform n A i)).foldr
    (· ∘ ·) id v

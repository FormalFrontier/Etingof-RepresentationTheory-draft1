/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.AuxiliaryFiniteSetMembership
import RepresentationTheory.QuiverRepresentationQuotientTransform
import RepresentationTheory.AuxiliaryFiniteDimensionalFamily
import RepresentationTheory.AuxiliaryIntegerMatrixTransform
import RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction
import RepresentationTheory.AuxiliaryIntegerVectorTransforms
import RepresentationTheory.Quiver.AuxiliaryNatInt
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.IntegerMatrices

/-- A four-by-four matrix with integer entries. -/
def integerMatrixA : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1;
     0, 0, 0, 1;
     0, 0, 0, 1;
     1, 1, 1, 0]

/-- A four-by-four matrix with integer entries. -/
def integerMatrixB : Matrix (Fin 4) (Fin 4) ℤ :=
  RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform 4 integerMatrixA

/-- Records a theorem whose proposition is not rendered in the packet. -/
theorem integerMatrixB_property :
    integerMatrixB =
      !![2, 0, 0, -1;
         0, 2, 0, -1;
         0, 0, 2, -1;
         -1, -1, -1, 2] := by
  decide

/-- A vector indexed by four positions with integer components. -/
def integerVector : Fin 4 → ℤ := RepresentationTheory.AuxiliaryFiniteIndexIntegerFunction.auxiliaryValue 4 3

/-- Evaluates the displayed operation on the matrix and vector to four entries equal to one. -/
@[source_ref "Chapter6/Example6.8.5" (role := supporting)]
theorem integerMatrixB_operationAtZeroOneTwo_eq_ones :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4 integerMatrixB 0
      (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4 integerMatrixB 1
        (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4 integerMatrixB 2 integerVector)) =
    ![1, 1, 1, 1] := by
  decide

/-- Evaluates the displayed operation on the matrix and vector to the entries one, one, one, and two. -/
@[source_ref "Chapter6/Example6.8.5" (role := supporting)]
theorem integerMatrixB_operationAtThreeZeroOneTwo_eq_oneOneOneTwo :
    RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4 integerMatrixB 3
      (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4 integerMatrixB 0
        (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4 integerMatrixB 1
          (RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform 4 integerMatrixB 2 integerVector))) =
    ![1, 1, 1, 2] := by
  decide

/-- Shows that the displayed tuple `(2, 1, 1, 1)` satisfies the given membership predicate. -/
@[source_ref "Chapter6/Example6.8.5" (role := primary)]
theorem tuple2111_mem :
    (2, 1, 1, 1) ∈ RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.fourVertexDimensionTuples := by
  decide

end RepresentationTheory.IntegerMatrices

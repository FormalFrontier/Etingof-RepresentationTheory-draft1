/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty
import RepresentationTheory.Alignment.Attribute

/-!
# Integer Matrix-Vector Predicates

Auxiliary predicates on square integer matrices and integer vectors with matching finite indices.
-/

/-- A condition on an integer square matrix together with an integer vector over the corresponding finite index type. -/
@[source_ref "Chapter6/Definition6.4.7" (role := supporting)]
def RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition
    (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x ∧
    ∀ i, 0 ≤ x i

/-- A predicate on an integer square matrix and an integer vector with the same finite index type. -/
@[source_ref "Chapter6/Definition6.4.7" (role := supporting)]
def RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorPredicate
    (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix n adj x ∧
    ∀ i, x i ≤ 0

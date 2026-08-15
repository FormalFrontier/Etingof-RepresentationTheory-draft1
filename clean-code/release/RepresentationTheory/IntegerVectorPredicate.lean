/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.IntegerMatrixVectorPredicates
import RepresentationTheory.IntegralVectorSign
import RepresentationTheory.Quiver.DimensionVectorClassification
import RepresentationTheory.Alignment.Attribute

/-! # Integer vector predicate -/

/-- The predicate is preserved by pointwise negation of an integer-valued vector. -/
theorem RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix.neg
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ} {x : Fin n → ℤ}
    (hx : RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix
      n adj x) :
    RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix
      n adj (-x) := by
  refine ⟨neg_ne_zero.mpr hx.1, ?_⟩
  rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  exact hx.2

/-- Under the given condition on the integer matrix, the set of integer-valued vectors satisfying the predicate is finite. -/
@[source_ref "Chapter6/Remark6.4.4" (role := primary)]
theorem RepresentationTheory.IntegerVectorPredicate.finite_setOf_integerVectorPredicate
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix n adj) :
    Set.Finite {x : Fin n → ℤ |
      RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix
        n adj x} := by
  have hpos : Set.Finite {d : Fin n → ℤ |
      RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition
        n adj d} :=
    RepresentationTheory.Quiver.DimensionVectorClassification.finite_setOf_vectorPredicate
      hDynkin
  refine (hpos.union (hpos.image (fun d => -d))).subset ?_
  intro x hx
  have hxr :
      RepresentationTheory.AuxiliaryIntegerMatrixVectorProperty.IsAuxiliaryForMatrix
        n adj x := hx
  rcases RepresentationTheory.IntegralVectorSign.all_nonnegative_or_all_nonpositive
    n adj hDynkin x hxr with hp | hn
  · exact Or.inl ⟨hxr, hp⟩
  · refine Or.inr ⟨-x, ⟨hxr.neg, fun i => ?_⟩, neg_neg x⟩
    simpa using neg_nonneg.mpr (hn i)

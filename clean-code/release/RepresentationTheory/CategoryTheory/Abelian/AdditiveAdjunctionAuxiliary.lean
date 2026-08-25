/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.FunctorPredicateLogic
import RepresentationTheory.Preadditive.FunctorProperties

/-!
# Additive adjunctions between abelian categories

Records the finite-limit and finite-colimit preservation properties supplied by an additive
adjunction between abelian categories.
-/

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.Abelian.AdditiveAdjunctionAuxiliary

/-- An additive adjunction between abelian categories satisfies both auxiliary properties in the
conclusion. -/
@[source_ref "Chapter7/Exercise7.9.7" (role := supporting)]
theorem auxiliaryProperties {C : Type*} {D : Type*} [Category C] [Category D]
    [_root_.CategoryTheory.Abelian C] [_root_.CategoryTheory.Abelian D]
    (F : C ⥤ D) (G : D ⥤ C)
    [RepresentationTheory.Preadditive.FunctorProperties.PreadditiveProperty F]
    [RepresentationTheory.Preadditive.FunctorProperties.PreadditiveProperty G]
    (adj : F ⊣ G) :
    RepresentationTheory.FunctorPredicateLogic.Right F ∧
      RepresentationTheory.FunctorPredicateLogic.Left G := by
  haveI := adj.leftAdjoint_preservesColimits
  haveI := adj.rightAdjoint_preservesLimits
  exact ⟨inferInstance, inferInstance⟩

end RepresentationTheory.CategoryTheory.Abelian.AdditiveAdjunctionAuxiliary

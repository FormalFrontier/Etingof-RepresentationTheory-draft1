/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Basic
import RepresentationTheory.Alignment.Attribute

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.TopCatCongruence

example : Category (Type*) := inferInstance

example : Category GrpCat := inferInstance

example : Category RingCat := inferInstance

example (k : Type*) [Field k] : Category (ModuleCat k) := inferInstance

example (A : Type*) [Ring A] : Category (ModuleCat A) := inferInstance

example : Category TopCat := inferInstance

/-- A relation on morphisms in the category of topological spaces. -/
@[source_ref "Chapter7/Example7.1.3" (role := supporting)]
def topCatHomRel : HomRel TopCat := fun _ _ f g => ContinuousMap.Homotopic f.hom g.hom

/-- The specified topological-space morphism relation is a category congruence. -/
instance topCatHomRel_congruence : Congruence topCatHomRel where
  equivalence :=
    { refl := fun f => ContinuousMap.Homotopic.refl f.hom
      symm := fun h => ContinuousMap.Homotopic.symm h
      trans := fun h₁ h₂ => ContinuousMap.Homotopic.trans h₁ h₂ }
  comp_left := by
    intro X Y Z f g g' h
    exact ContinuousMap.Homotopic.comp h (ContinuousMap.Homotopic.refl f.hom)
  comp_right := by
    intro X Y Z f f' g h
    exact ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g.hom) h

/-- An auxiliary type. -/
@[source_ref "Chapter7/Example7.1.3" (role := supporting)]
abbrev AuxiliaryType := CategoryTheory.Quotient topCatHomRel

example : Category AuxiliaryType := inferInstance

end RepresentationTheory.CategoryTheory.TopCatCongruence

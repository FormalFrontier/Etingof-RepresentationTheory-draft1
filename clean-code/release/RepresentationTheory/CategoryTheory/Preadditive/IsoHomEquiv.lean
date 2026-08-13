/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.Preadditive.IsoHomEquiv

/-- The additive equivalence on morphisms induced by precomposing with an isomorphism. -/
def homPrecomposeIsoAddEquiv {C : Type*} [Category C] [Preadditive C] {X X' Y : C}
    (α : X ≅ X') : (X ⟶ Y) ≃+ (X' ⟶ Y) where
  toFun f := α.inv ≫ f
  invFun g := α.hom ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

/-- Applying the morphism equivalence sends a map to its composite with the inverse isomorphism. -/
@[simp] lemma homPrecomposeIsoAddEquiv_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (f : X ⟶ Y) :
    homPrecomposeIsoAddEquiv α f = α.inv ≫ f := rfl

/-- Applying the inverse morphism equivalence sends a map to its composite with the isomorphism. -/
@[simp] lemma homPrecomposeIsoAddEquiv_symm_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (g : X' ⟶ Y) :
    (homPrecomposeIsoAddEquiv α).symm g = α.hom ≫ g := rfl

end RepresentationTheory.CategoryTheory.Preadditive.IsoHomEquiv

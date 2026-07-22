import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Precomposition with an isomorphism as an additive equivalence

`Etingof.isoPrecompHomEquiv` packages precomposition with an isomorphism `α : X ≅ X'` in a
preadditive category as an additive equivalence `(X ⟶ Y) ≃+ (X' ⟶ Y)`. It is a small shared
helper used by both `HomComplexHomologyK` and `Problem8_2_6_ii_Crux` to identify the degree-`i`
terms of a `HomComplex` with categorical hom-groups; it lives in its own file so the two callers
can import it without duplicating the definition.
-/

open CategoryTheory

namespace Etingof

/-- Precomposition with an isomorphism, as an additive equivalence of hom-groups. -/
def isoPrecompHomEquiv {C : Type*} [Category C] [Preadditive C] {X X' Y : C} (α : X ≅ X') :
    (X ⟶ Y) ≃+ (X' ⟶ Y) where
  toFun f := α.inv ≫ f
  invFun g := α.hom ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

@[simp] lemma isoPrecompHomEquiv_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (f : X ⟶ Y) :
    isoPrecompHomEquiv α f = α.inv ≫ f := rfl

@[simp] lemma isoPrecompHomEquiv_symm_apply {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (α : X ≅ X') (g : X' ⟶ Y) :
    (isoPrecompHomEquiv α).symm g = α.hom ≫ g := rfl

end Etingof

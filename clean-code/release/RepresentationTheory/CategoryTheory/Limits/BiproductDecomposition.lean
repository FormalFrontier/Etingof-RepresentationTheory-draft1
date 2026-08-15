/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.Abelian.SubobjectLength
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Biproduct decompositions

This module constructs an isomorphism that combines two finite indexed biproducts and uses an
object-length induction to decompose objects into finite biproducts of indecomposable objects.
It also records the corresponding decomposition for projective objects.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Limits.BiproductDecomposition

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C]
  [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]

/-- An auxiliary object-level quantity has equal values on isomorphic objects. -/
theorem auxiliary_eq_of_iso {X Y : C} (e : X ≅ Y) :
    RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength X =
      RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength Y := by
  unfold RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength
  rw [← Order.height_orderIso (Subobject.mapIsoToOrderIso e) (⊤ : Subobject X),
    (Subobject.mapIsoToOrderIso e).map_top]

section BiproductSum

variable {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂]

/-- The binary biproduct of two indexed biproducts is isomorphic to the biproduct indexed by
their sum. -/
noncomputable def biprodOfBiproductIsoBiproductSum (f₁ : κ₁ → C) (f₂ : κ₂ → C) :
    (⨁ f₁) ⊞ (⨁ f₂) ≅ ⨁ (Sum.elim f₁ f₂) where
  hom := biprod.desc
    (biproduct.desc fun a => biproduct.ι (Sum.elim f₁ f₂) (Sum.inl a))
    (biproduct.desc fun b => biproduct.ι (Sum.elim f₁ f₂) (Sum.inr b))
  inv := biproduct.desc fun k => match k with
    | Sum.inl a => biproduct.ι f₁ a ≫ biprod.inl
    | Sum.inr b => biproduct.ι f₂ b ≫ biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> rintro j <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, biproduct.ι_desc_assoc,
        Category.comp_id] <;>
      exact biproduct.ι_desc _ _
  inv_hom_id := by
    apply biproduct.hom_ext'
    rintro (a | b) <;> rw [biproduct.ι_desc_assoc] <;> simp

end BiproductSum

/-- Every object is isomorphic to a biproduct whose summands are indecomposable. -/
theorem exists_iso_biproduct_of_indec (X : C) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → C),
      (∀ k, CategoryTheory.Indecomposable (f k)) ∧ Nonempty (X ≅ ⨁ f) := by
  have key : ∀ n, ∀ X : C,
      RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength X = n →
      ∃ (κ : Type) (_ : Fintype κ) (f : κ → C),
        (∀ k, CategoryTheory.Indecomposable (f k)) ∧ Nonempty (X ≅ ⨁ f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X hX
      by_cases hzero : IsZero X
      · refine ⟨Empty, inferInstance, Empty.elim, fun k => k.elim, ⟨?_⟩⟩
        have hbip : IsZero (⨁ (Empty.elim : Empty → C)) := by
          refine ⟨fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
          · exact biproduct.hom_ext' _ _ fun j => j.elim
          · exact biproduct.hom_ext _ _ fun j => j.elim
        exact hzero.iso hbip
      · by_cases hindec : CategoryTheory.Indecomposable X
        · exact ⟨PUnit, inferInstance, fun _ => X, fun _ => hindec,
            ⟨(biproductUniqueIso (fun _ : PUnit => X)).symm⟩⟩
        · have hsplit : ¬ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z :=
            fun hall => hindec ⟨hzero, hall⟩
          push Not at hsplit
          obtain ⟨Y, Z, hiso, hY, hZ⟩ := hsplit
          have hsum :
              RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength X =
                RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength Y +
                  RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength Z := by
            rw [auxiliary_eq_of_iso hiso,
              RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength_biprod]
          have hzposY :=
            RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength_pos_of_not_isZero hY
          have hzposZ :=
            RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength_pos_of_not_isZero hZ
          have hltY :
              RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength Y < n := by
            omega
          have hltZ :
              RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength Z < n := by
            omega
          obtain ⟨κY, finY, fY, hindecY, ⟨eY⟩⟩ :=
            ih (RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength Y)
              hltY Y rfl
          obtain ⟨κZ, finZ, fZ, hindecZ, ⟨eZ⟩⟩ :=
            ih (RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength Z)
              hltZ Z rfl
          haveI := finY
          haveI := finZ
          refine ⟨κY ⊕ κZ, inferInstance, Sum.elim fY fZ, ?_, ⟨?_⟩⟩
          · rintro (a | b)
            · exact hindecY a
            · exact hindecZ b
          · exact hiso ≪≫ biprod.mapIso eY eZ ≪≫
              biprodOfBiproductIsoBiproductSum fY fZ
  exact key (RepresentationTheory.CategoryTheory.Abelian.SubobjectLength.objectLength X) X rfl

/-- A projective object is isomorphic to a biproduct of projective indecomposable objects. -/
theorem exists_iso_biproduct_of_projective_indec {X : C} (hX : Projective X) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → C),
      (∀ k, Projective (f k) ∧ CategoryTheory.Indecomposable (f k)) ∧ Nonempty (X ≅ ⨁ f) := by
  obtain ⟨κ, fin, f, hindec, ⟨e⟩⟩ := exists_iso_biproduct_of_indec X
  haveI := fin
  refine ⟨κ, fin, f, fun k => ⟨?_, hindec k⟩, ⟨e⟩⟩
  haveI : Projective X := hX
  exact Retract.projective
    { i := biproduct.ι f k ≫ e.inv
      r := e.hom ≫ biproduct.π f k
      retract := by simp }

end RepresentationTheory.CategoryTheory.Limits.BiproductDecomposition

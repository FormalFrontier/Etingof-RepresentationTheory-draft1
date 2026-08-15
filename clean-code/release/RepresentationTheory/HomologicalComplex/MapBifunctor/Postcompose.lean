/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Algebra.Homology.TensorProduct
import RepresentationTheory.ModuleCat.RightTensor

set_option backward.isDefEq.respectTransparency false

/-!
# Postcomposition of map-bifunctor complexes

This module constructs the comparison isomorphism between applying an additive functor to a
map-bifunctor complex and forming the map-bifunctor complex of the postcomposed bifunctor.
-/

open CategoryTheory Limits

namespace RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose

set_option linter.dupNamespace false

universe u

variable {C₁ : Type*} {C₂ : Type*} {D : Type*} {D' : Type*}
  [Category C₁] [Category C₂] [Category D] [Category D']
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] [Preadditive D']
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- Constructs a bifunctor into the final category from a bifunctor and a functor out of its target
category. -/
abbrev CategoryTheory.Functor.bifunctorPostcompose
    (F : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ D') : C₁ ⥤ C₂ ⥤ D' :=
  F ⋙ (Functor.whiskeringRight C₂ D D').obj G

section Instances

variable (F : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ D')
  [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms]

/-- Evaluation of the right-whiskering functor at a zero-morphism-preserving functor preserves zero
morphisms. -/
instance CategoryTheory.Functor.PreservesZeroMorphisms.whiskeringRight_obj :
    ((Functor.whiskeringRight C₂ D D').obj G).PreservesZeroMorphisms where
  map_zero H₁ H₂ := by
    ext X
    simp

/-- The bifunctor constructed from two zero-morphism-preserving functors preserves zero
morphisms. -/
instance CategoryTheory.Functor.PreservesZeroMorphisms.bifunctorPostcompose :
    (CategoryTheory.Functor.bifunctorPostcompose F G).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_comp F ((Functor.whiskeringRight C₂ D D').obj G)

/-- At every object of the first category, the functor produced from the given bifunctor and functor
preserves zero morphisms. -/
instance CategoryTheory.Functor.PreservesZeroMorphisms.bifunctorPostcompose_obj
    (X₁ : C₁) :
    ((CategoryTheory.Functor.bifunctorPostcompose F G).obj X₁).PreservesZeroMorphisms :=
  inferInstanceAs ((F.obj X₁ ⋙ G).PreservesZeroMorphisms)

end Instances

section Iso

open _root_.HomologicalComplex

variable (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (G : D ⥤ D') [G.Additive]
  [HasMapBifunctor K₁ K₂ F c]
  [HasMapBifunctor K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G) c]
  [∀ (n : J), Finite (ComplexShape.π c₁ c₂ c ⁻¹' {n} : Set (I₁ × I₂))]

/-- Associates an object of the target category to two homological complexes, a
zero-morphism-preserving bifunctor, a total degree, and an index over that degree. -/
abbrev HomologicalComplex.mapBifunctorIndexObject
    (j : J) : (ComplexShape.π c₁ c₂ c ⁻¹' {j} : Set (I₁ × I₂)) → D :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).toGradedObject.mapObjFun
    (ComplexShape.π c₁ c₂ c) j

/-- For each total degree, the family obtained by applying the given functor to the displayed
indexed objects has a coproduct. -/
instance HomologicalComplex.hasCoproduct_mapBifunctorPostcompose_indexObjects (j : J) :
    HasCoproduct (fun i => G.obj (HomologicalComplex.mapBifunctorIndexObject
      (c := c) K₁ K₂ F j i)) :=
  (‹HasMapBifunctor K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G) c› : _) j

/-- At each degree, the degreewise image of a map-bifunctor complex is isomorphic to the
corresponding object of the map-bifunctor complex for the resulting bifunctor. -/
noncomputable def HomologicalComplex.mapBifunctorPostcomposeXIso (j : J) :
    ((G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c)).X j ≅
      (mapBifunctor K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G) c).X j :=
  PreservesCoproduct.iso G (HomologicalComplex.mapBifunctorIndexObject
    (c := c) K₁ K₂ F j)

/-- The inverse of the degreewise comparison isomorphism is the sigma comparison morphism for the
displayed indexed family. -/
@[simp]
lemma HomologicalComplex.mapBifunctorPostcomposeXIso_inv_eq_sigmaComparison (j : J) :
    (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G j).inv =
      Limits.sigmaComparison G
        (HomologicalComplex.mapBifunctorIndexObject (c := c) K₁ K₂ F j) :=
  PreservesCoproduct.inv_hom G _

/-- Composing a canonical inclusion with the inverse comparison isomorphism gives the mapped
canonical inclusion. -/
@[reassoc]
lemma HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor_inv
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c i₁ i₂ j h ≫
        (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G j).inv =
      G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h) := by
  rw [HomologicalComplex.mapBifunctorPostcomposeXIso_inv_eq_sigmaComparison]
  exact Limits.ι_comp_sigmaComparison G
    (HomologicalComplex.mapBifunctorIndexObject (c := c) K₁ K₂ F j) ⟨(i₁, i₂), h⟩

/-- The equality relating a canonical inclusion and the inverse comparison isomorphism remains
valid after postcomposition by a morphism. -/
add_decl_doc HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor_inv_assoc

/-- Mapping a canonical inclusion and composing with the comparison isomorphism gives the
corresponding canonical inclusion. -/
@[reassoc]
lemma HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h) ≫
        (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G j).hom =
      ιMapBifunctor K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c i₁ i₂ j h := by
  rw [← HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor_inv
    K₁ K₂ F G i₁ i₂ j h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The equality relating mapped canonical inclusions to the comparison isomorphism remains valid
after postcomposition by a morphism. -/
add_decl_doc HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor_assoc

/-- Mapping a canonical inclusion-or-zero morphism and composing with the comparison isomorphism
gives the corresponding canonical inclusion-or-zero morphism. -/
lemma HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctorOrZero
    (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j) ≫
        (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G j).hom =
      ιMapBifunctorOrZero K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c i₁ i₂ j := by
  by_cases h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j
  · rw [ιMapBifunctorOrZero_eq K₁ K₂ F c i₁ i₂ j h,
      ιMapBifunctorOrZero_eq K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c i₁ i₂ j h,
      HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor]
  · rw [ιMapBifunctorOrZero_eq_zero K₁ K₂ F c i₁ i₂ j h,
      ιMapBifunctorOrZero_eq_zero K₁ K₂
        (CategoryTheory.Functor.bifunctorPostcompose F G) c i₁ i₂ j h,
      Functor.map_zero, Limits.zero_comp]

/-- Applying an additive functor to the first map-bifunctor differential and then composing with
the specified isomorphism gives the corresponding first differential. -/
lemma HomologicalComplex.mapBifunctorPostcompose_d1 (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j) ≫
        (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G j).hom =
      mapBifunctor.d₁ K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c i₁ i₂ j := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · rw [mapBifunctor.d₁_eq' K₁ K₂ F c h i₂ j,
      mapBifunctor.d₁_eq' K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c h i₂ j,
      Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctorOrZero]
    rfl
  · rw [mapBifunctor.d₁_eq_zero K₁ K₂ F c i₁ i₂ j h,
      mapBifunctor.d₁_eq_zero K₁ K₂
        (CategoryTheory.Functor.bifunctorPostcompose F G) c i₁ i₂ j h,
      Functor.map_zero, Limits.zero_comp]

/-- Applying an additive functor to the second map-bifunctor differential and then composing with
the specified isomorphism gives the corresponding second differential. -/
lemma HomologicalComplex.mapBifunctorPostcompose_d2 (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j) ≫
        (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G j).hom =
      mapBifunctor.d₂ K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c i₁ i₂ j := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · rw [mapBifunctor.d₂_eq' K₁ K₂ F c i₁ h j,
      mapBifunctor.d₂_eq' K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G)
        c i₁ h j,
      Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctorOrZero]
    rfl
  · rw [mapBifunctor.d₂_eq_zero K₁ K₂ F c i₁ i₂ j h,
      mapBifunctor.d₂_eq_zero K₁ K₂
        (CategoryTheory.Functor.bifunctorPostcompose F G) c i₁ i₂ j h,
      Functor.map_zero, Limits.zero_comp]

omit [HasMapBifunctor K₁ K₂
  (CategoryTheory.Functor.bifunctorPostcompose F G) c] in
/-- Two morphisms from the image of a map-bifunctor object are equal if their composites with every
mapped canonical inclusion are equal. -/
lemma HomologicalComplex.mapBifunctorPostcompose_hom_ext {A : D'} {i : J}
    (f g : G.obj ((mapBifunctor K₁ K₂ F c).X i) ⟶ A)
    (hfg : ∀ (i₁ : I₁) (i₂ : I₂)
      (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = i),
      G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ i h) ≫ f =
        G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ i h) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext
    (isColimitOfHasCoproductOfPreservesColimit G
      (HomologicalComplex.mapBifunctorIndexObject (c := c) K₁ K₂ F i)) f g
    (fun ⟨⟨i₁, i₂⟩, h⟩ => hfg i₁ i₂ h)

/-- The hom maps of the degreewise comparison isomorphisms commute with the differentials of the
two homological complexes. -/
lemma HomologicalComplex.mapBifunctorPostcomposeXIso_hom_naturality (i j : J) :
    (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G i).hom ≫
        (mapBifunctor K₁ K₂
          (CategoryTheory.Functor.bifunctorPostcompose F G) c).d i j =
      ((G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c)).d i j ≫
        (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G j).hom := by
  rw [Functor.mapHomologicalComplex_obj_d]
  apply HomologicalComplex.mapBifunctorPostcompose_hom_ext K₁ K₂ F G
  intro i₁ i₂ h
  rw [← Category.assoc,
    HomologicalComplex.mapBifunctorPostcompose_iotaMapBifunctor,
    ← Category.assoc, ← G.map_comp]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂, G.map_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctorPostcompose_d1,
    HomologicalComplex.mapBifunctorPostcompose_d2]

/-- The degreewise image of a map-bifunctor complex is isomorphic to the map-bifunctor complex
formed with the resulting bifunctor. -/
noncomputable def HomologicalComplex.mapBifunctorPostcomposeIso :
    (G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c) ≅
      mapBifunctor K₁ K₂ (CategoryTheory.Functor.bifunctorPostcompose F G) c :=
  _root_.HomologicalComplex.Hom.isoOfComponents
    (HomologicalComplex.mapBifunctorPostcomposeXIso (c := c) K₁ K₂ F G)
    (fun i j _ =>
      HomologicalComplex.mapBifunctorPostcomposeXIso_hom_naturality K₁ K₂ F G i j)

end Iso

section Smoke

open scoped _root_.TensorProduct
open ComplexShape

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N : Type u) [AddCommGroup N] [Module (A₁ ⊗[k] A₂) N]
variable (K₁ : HomologicalComplex (ModuleCat.{u} A₁ᵐᵒᵖ) (down ℕ))
  (K₂ : HomologicalComplex (ModuleCat.{u} A₂ᵐᵒᵖ) (down ℕ))

noncomputable example :
    ((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
        k (A₁ ⊗[k] A₂) N).mapHomologicalComplex (down ℕ)).obj
      (_root_.HomologicalComplex.mapBifunctor K₁ K₂
        (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
          k A₁ A₂) (down ℕ)) ≅
    _root_.HomologicalComplex.mapBifunctor K₁ K₂
      (CategoryTheory.Functor.bifunctorPostcompose
        (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
          k A₁ A₂)
        (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor
          k (A₁ ⊗[k] A₂) N))
      (down ℕ) :=
  HomologicalComplex.mapBifunctorPostcomposeIso K₁ K₂
    (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
    (RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k (A₁ ⊗[k] A₂) N)

end Smoke

end RepresentationTheory.HomologicalComplex.MapBifunctor.Postcompose

import EtingofRepresentationTheory.Chapter8.ExternalTensorComplex
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

set_option backward.isDefEq.respectTransparency false

/-!
# An additive functor commutes with the total complex `mapBifunctor`

Given a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, a `TotalComplexShape c₁ c₂ c` with *finite* fibers, and an
**additive** functor `G : D ⥤ D'` between preadditive categories, this file constructs the
isomorphism of complexes

```
mapBifunctorPostcompIso :
  (G.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor K₁ K₂ F c)
    ≅ HomologicalComplex.mapBifunctor K₁ K₂ (F ⋙ (Functor.whiskeringRight _ _ _).obj G) c
```

commuting with the differentials, so it is an isomorphism of `HomologicalComplex.Hom`.

The degree-`j` piece of each side is a finite coproduct `∐_{π (i₁, i₂) = j}` over the fiber. An
additive functor preserves finite coproducts, so `G` commutes with the `GradedObject.mapObj`
coproduct that `HomologicalComplex₂.total` is built from: the degreewise iso is exactly
`Limits.PreservesCoproduct.iso`. The differential square then reduces, on each summand, to the
compatibility `G.map (ιMapBifunctor F …) ≫ (postcompX …).hom = ιMapBifunctor (F ⋙ …G) …`, plus the
fact that `G` is `ℤ`-linear on hom-groups (so it commutes with the Koszul sign) and preserves
`d₁ = F.map d` and `d₂` definitionally.

This is step 3 of the four-fold rearrangement for Problem 8.2.8 (`Tor` over a tensor
product of algebras); an instantiation with `G = tensorRightFunctorₖ` and
`F = extTensorFunctor` is provided at the end.
-/

open CategoryTheory Limits

namespace Etingof

universe u

variable {C₁ : Type*} {C₂ : Type*} {D : Type*} {D' : Type*}
  [Category C₁] [Category C₂] [Category D] [Category D']
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] [Preadditive D']
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- The postcomposition of a bifunctor `F : C₁ ⥤ C₂ ⥤ D` with a functor `G : D ⥤ D'`. On objects
`((postcompBifunctor F G).obj X₁).obj X₂ = G.obj ((F.obj X₁).obj X₂)`. -/
abbrev postcompBifunctor (F : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ D') : C₁ ⥤ C₂ ⥤ D' :=
  F ⋙ (Functor.whiskeringRight C₂ D D').obj G

section Instances

variable (F : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ D')
  [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

instance whiskeringRight_obj_preservesZeroMorphisms :
    ((Functor.whiskeringRight C₂ D D').obj G).PreservesZeroMorphisms where
  map_zero H₁ H₂ := by
    ext X
    simp

instance : (postcompBifunctor F G).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_comp F ((Functor.whiskeringRight C₂ D D').obj G)

instance (X₁ : C₁) : ((postcompBifunctor F G).obj X₁).PreservesZeroMorphisms :=
  inferInstanceAs ((F.obj X₁ ⋙ G).PreservesZeroMorphisms)

end Instances

section Iso

open HomologicalComplex

variable (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (G : D ⥤ D') [G.Additive]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor K₁ K₂ (postcompBifunctor F G) c]
  [∀ (n : J), Finite (ComplexShape.π c₁ c₂ c ⁻¹' {n} : Set (I₁ × I₂))]

/-- The family of summands `(F.obj (K₁.X i₁)).obj (K₂.X i₂)` with `π (i₁, i₂) = j`, whose coproduct
is degree `j` of `mapBifunctor K₁ K₂ F c`. -/
abbrev postcompFam (j : J) : (ComplexShape.π c₁ c₂ c ⁻¹' {j} : Set (I₁ × I₂)) → D :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).toGradedObject.mapObjFun
    (ComplexShape.π c₁ c₂ c) j

/-- The coproduct of the `G`-images of the summands exists: it is the corresponding degree of the
postcomposed total complex. -/
instance hasCoproduct_postcompFam (j : J) :
    HasCoproduct (fun i => G.obj (postcompFam (c := c) K₁ K₂ F j i)) :=
  (‹HasMapBifunctor K₁ K₂ (postcompBifunctor F G) c› : _) j

/-- The degreewise isomorphism `G (∐ summands) ≅ ∐ (G summands)`: an additive functor commutes with
the finite coproduct defining a degree of the total complex. -/
noncomputable def postcompX (j : J) :
    ((G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c)).X j ≅
      (mapBifunctor K₁ K₂ (postcompBifunctor F G) c).X j :=
  PreservesCoproduct.iso G (postcompFam (c := c) K₁ K₂ F j)

@[simp]
lemma postcompX_inv (j : J) :
    (postcompX (c := c) K₁ K₂ F G j).inv = Limits.sigmaComparison G (postcompFam (c := c) K₁ K₂ F j) :=
  PreservesCoproduct.inv_hom G _

/-- Summand compatibility (inverse form): the `j`-summand inclusion of the postcomposed total
complex, followed by `(postcompX j).inv`, is `G` applied to the corresponding inclusion. -/
@[reassoc]
lemma ιMapBifunctor_postcomp_comp_postcompX_inv (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j h ≫ (postcompX (c := c) K₁ K₂ F G j).inv =
      G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h) := by
  rw [postcompX_inv]
  exact Limits.ι_comp_sigmaComparison G (postcompFam (c := c) K₁ K₂ F j) ⟨(i₁, i₂), h⟩

/-- Summand compatibility (forward form). -/
@[reassoc]
lemma ιMapBifunctor_comp_postcompX_hom (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h) ≫ (postcompX (c := c) K₁ K₂ F G j).hom =
      ιMapBifunctor K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j h := by
  rw [← ιMapBifunctor_postcomp_comp_postcompX_inv K₁ K₂ F G i₁ i₂ j h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Summand compatibility for the "or zero" inclusion. -/
lemma ιMapBifunctorOrZero_comp_postcompX_hom (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j) ≫ (postcompX (c := c) K₁ K₂ F G j).hom =
      ιMapBifunctorOrZero K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j := by
  by_cases h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j
  · rw [ιMapBifunctorOrZero_eq K₁ K₂ F c i₁ i₂ j h,
      ιMapBifunctorOrZero_eq K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j h,
      ιMapBifunctor_comp_postcompX_hom]
  · rw [ιMapBifunctorOrZero_eq_zero K₁ K₂ F c i₁ i₂ j h,
      ιMapBifunctorOrZero_eq_zero K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j h,
      Functor.map_zero, Limits.zero_comp]

/-- `G` intertwines the first partial differential of the total complex. -/
lemma d₁_postcompX (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j) ≫ (postcompX (c := c) K₁ K₂ F G j).hom =
      mapBifunctor.d₁ K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · rw [mapBifunctor.d₁_eq' K₁ K₂ F c h i₂ j,
      mapBifunctor.d₁_eq' K₁ K₂ (postcompBifunctor F G) c h i₂ j,
      Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp, Category.assoc,
      ιMapBifunctorOrZero_comp_postcompX_hom]
    rfl
  · rw [mapBifunctor.d₁_eq_zero K₁ K₂ F c i₁ i₂ j h,
      mapBifunctor.d₁_eq_zero K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j h,
      Functor.map_zero, Limits.zero_comp]

/-- `G` intertwines the second partial differential of the total complex. -/
lemma d₂_postcompX (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j) ≫ (postcompX (c := c) K₁ K₂ F G j).hom =
      mapBifunctor.d₂ K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · rw [mapBifunctor.d₂_eq' K₁ K₂ F c i₁ h j,
      mapBifunctor.d₂_eq' K₁ K₂ (postcompBifunctor F G) c i₁ h j,
      Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp, Category.assoc,
      ιMapBifunctorOrZero_comp_postcompX_hom]
    rfl
  · rw [mapBifunctor.d₂_eq_zero K₁ K₂ F c i₁ i₂ j h,
      mapBifunctor.d₂_eq_zero K₁ K₂ (postcompBifunctor F G) c i₁ i₂ j h,
      Functor.map_zero, Limits.zero_comp]

/-- Extensionality for maps out of `G (∐ summands)`: an additive functor preserves the coproduct,
so it suffices to check on `G`-images of the summand inclusions. -/
lemma postcompX_hom_ext {A : D'} {i : J}
    (f g : G.obj ((mapBifunctor K₁ K₂ F c).X i) ⟶ A)
    (hfg : ∀ (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = i),
      G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ i h) ≫ f =
        G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ i h) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext
    (isColimitOfHasCoproductOfPreservesColimit G (postcompFam (c := c) K₁ K₂ F i)) f g
    (fun ⟨⟨i₁, i₂⟩, h⟩ => hfg i₁ i₂ h)

/-- The degreewise isos `postcompX` commute with the differentials. -/
lemma postcompX_comm (i j : J) :
    (postcompX (c := c) K₁ K₂ F G i).hom ≫ (mapBifunctor K₁ K₂ (postcompBifunctor F G) c).d i j =
      ((G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c)).d i j ≫
        (postcompX (c := c) K₁ K₂ F G j).hom := by
  rw [Functor.mapHomologicalComplex_obj_d]
  apply postcompX_hom_ext K₁ K₂ F G
  intro i₁ i₂ h
  rw [← Category.assoc, ιMapBifunctor_comp_postcompX_hom, ← Category.assoc, ← G.map_comp]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    G.map_add, Preadditive.add_comp, d₁_postcompX, d₂_postcompX]

/-- **An additive functor commutes with the total complex `mapBifunctor`.** For an additive
`G : D ⥤ D'` and a `TotalComplexShape` with finite fibers, applying `G` degreewise to the total
complex `mapBifunctor K₁ K₂ F c` is isomorphic to the total complex of the postcomposed bifunctor. -/
noncomputable def mapBifunctorPostcompIso :
    (G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c) ≅
      mapBifunctor K₁ K₂ (postcompBifunctor F G) c :=
  HomologicalComplex.Hom.isoOfComponents (postcompX (c := c) K₁ K₂ F G)
    (fun i j _ => postcompX_comm K₁ K₂ F G i j)

end Iso

section Smoke

open scoped TensorProduct
open ComplexShape

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N : Type u) [AddCommGroup N] [Module (A₁ ⊗[k] A₂) N]
variable (K₁ : HomologicalComplex (ModuleCat.{u} A₁ᵐᵒᵖ) (down ℕ))
  (K₂ : HomologicalComplex (ModuleCat.{u} A₂ᵐᵒᵖ) (down ℕ))

/-- Instantiation for Problem 8.2.8 (`Tor`), step 3: the `k`-linear tensor-right functor
`G = tensorRightFunctorₖ` commutes with the external-tensor total complex
`mapBifunctor … (extTensorFunctor …) (down ℕ)`. Used directly by the four-fold rearrangement. -/
noncomputable example :
    ((tensorRightFunctorₖ k (A₁ ⊗[k] A₂) N).mapHomologicalComplex (down ℕ)).obj
        (HomologicalComplex.mapBifunctor K₁ K₂ (extTensorFunctor k A₁ A₂) (down ℕ)) ≅
      HomologicalComplex.mapBifunctor K₁ K₂
        (postcompBifunctor (extTensorFunctor k A₁ A₂) (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) N))
        (down ℕ) :=
  mapBifunctorPostcompIso K₁ K₂ (extTensorFunctor k A₁ A₂) (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) N)

end Smoke

end Etingof

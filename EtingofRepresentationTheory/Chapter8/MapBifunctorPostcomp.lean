import EtingofRepresentationTheory.Chapter8.ExternalTensorComplex
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

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

commuting with the differentials, so it is a genuine `HomologicalComplex.Hom` iso.

The degree-`j` piece of each side is a finite coproduct `∐_{π (i₁, i₂) = j}` over the fiber. An
additive functor preserves finite coproducts, so `G` commutes with the `GradedObject.mapObj`
coproduct that `HomologicalComplex₂.total` is built from: the degreewise iso is exactly
`Limits.PreservesCoproduct.iso`. The differential square then reduces, on each summand, to the
compatibility `G.map (ιMapBifunctor F …) ≫ (postcompX …).hom = ιMapBifunctor (F ⋙ …G) …`, plus the
fact that `G` is `ℤ`-linear on hom-groups (so it commutes with the Koszul sign) and preserves
`d₁ = F.map d` and `d₂` definitionally.

This feeds route step 3 of the four-fold rearrangement for Problem 8.2.8 (`Tor` over a tensor
product of algebras): a smoke instantiation with `G = tensorRightFunctorₖ` and
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

end Etingof

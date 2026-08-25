/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import RepresentationTheory.Alignment.Attribute

/-!
# Properties of functors between preadditive categories

Definitions and elementary binary-biproduct consequences for additive and linear functors.
-/

namespace RepresentationTheory.Preadditive.FunctorProperties

/-- A property of a functor between preadditive categories. -/
@[source_ref "Chapter7/Introduction_7.9" (role := supporting),
  source_ref "Chapter7/Definition7.9.1" (role := supporting)]
abbrev PreadditiveProperty {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] [CategoryTheory.Preadditive C]
    [CategoryTheory.Preadditive D] (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Functor.Additive F

/-- A property of a functor between preadditive categories with linear structures over a semiring. -/
@[source_ref "Chapter7/Introduction_7.9" (role := supporting),
  source_ref "Chapter7/Definition7.9.1" (role := supporting)]
abbrev LinearProperty (k : Type*) [Semiring k] {C : Type*} {D : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
    [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
    (F : CategoryTheory.Functor C D) :=
  CategoryTheory.Functor.Linear k F

namespace PreadditiveProperty

open CategoryTheory CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] (F : C ⥤ D) [F.Additive] (X Y : C)

/-- An additive functor between preadditive categories preserves each binary biproduct. -/
instance preservesBinaryBiproduct : PreservesBinaryBiproduct X Y F :=
  preservesBinaryBiproduct_of_preservesBiproduct F X Y

/-- The comparison isomorphism from the image of a binary biproduct to the binary biproduct of the images under an additive functor. -/
@[source_ref "Chapter7/Discussion_after_Definition7.9.1" (role := primary),
  source_ref "Chapter7/Discussion_after_Definition7.9.1/Derived01" (role := primary)]
noncomputable def binaryBiproductComparisonIso : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  F.mapBiprod X Y

/-- The forward morphism of the binary biproduct comparison is the lift of the images of the two projections. -/
theorem binaryBiproductComparisonIso_hom :
    (binaryBiproductComparisonIso F X Y).hom =
      biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
  F.mapBiprod_hom X Y

end PreadditiveProperty

end RepresentationTheory.Preadditive.FunctorProperties

/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace RepresentationTheory.Mathlib.Algebra.Homology.CochainComplex.Monoidal

universe u

variable {k : Type u} [Field k]

namespace CochainComplex

/-- A binary construction on cochain complexes of modules over a field. -/
noncomputable def binaryOperation (C D : CochainComplex (ModuleCat.{u} k) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  HomologicalComplex.tensorObj C D

/-- Cochain complexes of modules over a field form a monoidal preadditive category. -/
noncomputable instance monoidalPreadditive :
    MonoidalPreadditive (HomologicalComplex (ModuleCat.{u} k) (ComplexShape.up ℤ)) where
  whiskerLeft_zero {X Y Z} := by
    change mapBifunctorMap (𝟙 X) (0 : Y ⟶ Z) _ _ = 0
    refine HomologicalComplex.hom_ext _ _ fun j =>
      mapBifunctor.hom_ext fun i₁ i₂ h => ?_
    simp only [ι_mapBifunctorMap, HomologicalComplex.zero_f, Functor.map_zero, comp_zero, zero_comp]
  zero_whiskerRight {X Y Z} := by
    change mapBifunctorMap (0 : Y ⟶ Z) (𝟙 X) _ _ = 0
    refine HomologicalComplex.hom_ext _ _ fun j =>
      mapBifunctor.hom_ext fun i₁ i₂ h => ?_
    simp only [ι_mapBifunctorMap, HomologicalComplex.zero_f, Functor.map_zero,
      NatTrans.app_zero, zero_comp, comp_zero]
  whiskerLeft_add {X Y Z} f g := by
    change mapBifunctorMap (𝟙 X) (f + g) _ _ =
      mapBifunctorMap (𝟙 X) f _ _ + mapBifunctorMap (𝟙 X) g _ _
    refine HomologicalComplex.hom_ext _ _ fun j =>
      mapBifunctor.hom_ext fun i₁ i₂ h => ?_
    simp only [ι_mapBifunctorMap, HomologicalComplex.add_f_apply, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp]
  add_whiskerRight {X Y Z} f g := by
    change mapBifunctorMap (f + g) (𝟙 X) _ _ =
      mapBifunctorMap f (𝟙 X) _ _ + mapBifunctorMap g (𝟙 X) _ _
    refine HomologicalComplex.hom_ext _ _ fun j =>
      mapBifunctor.hom_ext fun i₁ i₂ h => ?_
    simp only [ι_mapBifunctorMap, HomologicalComplex.add_f_apply, Functor.map_add,
      NatTrans.app_add, Preadditive.comp_add, Preadditive.add_comp]

/-- The binary construction preserves a binary biproduct in its left argument. -/
noncomputable def binaryOperation_biprod_left
    (X Y Z : CochainComplex (ModuleCat.{u} k) ℤ) :
    binaryOperation (X ⊞ Y) Z ≅ binaryOperation X Z ⊞ binaryOperation Y Z :=
  haveI : PreservesBinaryBiproduct X Y (tensorRight Z) :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  (tensorRight Z).mapBiprod X Y

/-- The binary construction preserves a binary biproduct in its right argument. -/
noncomputable def binaryOperation_biprod_right
    (X Y Z : CochainComplex (ModuleCat.{u} k) ℤ) :
    binaryOperation X (Y ⊞ Z) ≅ binaryOperation X Y ⊞ binaryOperation X Z :=
  haveI : PreservesBinaryBiproduct Y Z (tensorLeft X) :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  (tensorLeft X).mapBiprod Y Z

end CochainComplex

end RepresentationTheory.Mathlib.Algebra.Homology.CochainComplex.Monoidal

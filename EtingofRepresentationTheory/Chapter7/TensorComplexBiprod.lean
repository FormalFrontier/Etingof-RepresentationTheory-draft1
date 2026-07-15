import Mathlib

/-!
# Distributivity of the tensor product of complexes over binary biproducts

Mathlib equips `HomologicalComplex (ModuleCat.{u} k) (ComplexShape.up ℤ)` with a monoidal
category structure whose tensor product is `HomologicalComplex.tensorObj` (the total complex of
the bicomplex `Cⱼ ⊗ Dₘ`). This file records that this monoidal structure is *preadditive*
(`MonoidalPreadditive`), i.e. tensoring is additive in each variable. Preadditivity makes the
two endofunctors `tensorLeft X` and `tensorRight Z` additive, hence they preserve binary
biproducts. We package the resulting distributivity isomorphisms as

* `Etingof.tensorComplex_biprodLeftIso`  : `(X ⊞ Y) ⊗ Z ≅ (X ⊗ Z) ⊞ (Y ⊗ Z)`
* `Etingof.tensorComplex_biprodRightIso` : `X ⊗ (Y ⊞ Z) ≅ (X ⊗ Y) ⊞ (X ⊗ Z)`

phrased in terms of `Etingof.tensorComplex` (Etingof's `(C ⊗ D)•`). This is the missing
infrastructure for the Künneth splitting in `Problem7_8_7_iv`.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace Etingof

universe u

variable {k : Type u} [Field k]

/-- Etingof's tensor product complex `(C ⊗ D)•`, with degree-`i` object `⨁_{j+m=i} Cⱼ ⊗ Dₘ`
and the Koszul-signed differential `dᶜ ⊗ 1 + (-1)ʲ · 1 ⊗ dᴰ`. This is Mathlib's
`HomologicalComplex.tensorObj`. -/
noncomputable def tensorComplex (C D : CochainComplex (ModuleCat.{u} k) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  HomologicalComplex.tensorObj C D

/-- Tensoring homological complexes over `ModuleCat.{u} k` is additive in each variable. -/
noncomputable instance :
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

/-- Distributivity of the tensor product of complexes over a binary biproduct in the left
variable: `(X ⊞ Y) ⊗ Z ≅ (X ⊗ Z) ⊞ (Y ⊗ Z)`. -/
noncomputable def tensorComplex_biprodLeftIso
    (X Y Z : CochainComplex (ModuleCat.{u} k) ℤ) :
    tensorComplex (X ⊞ Y) Z ≅ tensorComplex X Z ⊞ tensorComplex Y Z :=
  haveI : PreservesBinaryBiproduct X Y (tensorRight Z) :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  (tensorRight Z).mapBiprod X Y

/-- Distributivity of the tensor product of complexes over a binary biproduct in the right
variable: `X ⊗ (Y ⊞ Z) ≅ (X ⊗ Y) ⊞ (X ⊗ Z)`. -/
noncomputable def tensorComplex_biprodRightIso
    (X Y Z : CochainComplex (ModuleCat.{u} k) ℤ) :
    tensorComplex X (Y ⊞ Z) ≅ tensorComplex X Y ⊞ tensorComplex X Z :=
  haveI : PreservesBinaryBiproduct Y Z (tensorLeft X) :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  (tensorLeft X).mapBiprod Y Z

end Etingof

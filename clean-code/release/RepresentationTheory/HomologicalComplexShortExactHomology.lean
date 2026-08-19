/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Homology.HomologySequence
import RepresentationTheory.Alignment.Attribute

open CategoryTheory

namespace RepresentationTheory.HomologicalComplexShortExactHomology

/-- Returns a morphism from the homology of the third object in degree i to the homology of the
first object in degree j for related degrees. -/
@[source_ref "Chapter7/Definition7.8.6" (role := supporting)]
noncomputable abbrev homologyHomThirdToFirstOfRel
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

/-- The morphism δ followed by the homology map induced by f forms an exact pair. -/
@[source_ref "Chapter7/Definition7.8.6" (role := supporting)]
theorem exact_delta_homologyMap_f
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact :=
  hS.homology_exact₁ i j hij

/-- The homology maps induced by f and g form an exact pair in every degree. -/
@[source_ref "Chapter7/Definition7.8.6" (role := supporting)]
theorem exact_homologyMap_f_g
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i : ι) :
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  hS.homology_exact₂ i

/-- The homology map induced by g followed by the morphism δ forms an exact pair. -/
@[source_ref "Chapter7/Definition7.8.6" (role := supporting)]
theorem exact_homologyMap_g_delta
    {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  hS.homology_exact₃ i j hij

end RepresentationTheory.HomologicalComplexShortExactHomology

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import RepresentationTheory.Preadditive.FunctorProperties
import RepresentationTheory.CategoryTheory.Abelian.CategoryProperties
import RepresentationTheory.Alignment.Attribute

/-!
# Preservation of short exact complexes

Short exact complexes are preserved by additive functors when every short exact complex in the
source abelian category admits a splitting.
-/

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.Abelian.ShortExactPreservation

/-- If the displayed property holds for the source abelian category, an additive functor sends a short exact complex to a short exact complex. -/
@[source_ref "Chapter7/Discussion_after_Example7.9.5" (role := primary),
  source_ref "Chapter7/Discussion_after_Example7.9.5/Derived01" (role := primary)]
theorem shortExact_map_of_abelianCategoryProperty
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (hC : RepresentationTheory.CategoryTheory.Abelian.CategoryProperties.AbelianCategoryProperty C)
    (F : C ⥤ D) [F.Additive] (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map F).ShortExact :=
  ((hC S hS).some.map F).shortExact

end RepresentationTheory.CategoryTheory.Abelian.ShortExactPreservation

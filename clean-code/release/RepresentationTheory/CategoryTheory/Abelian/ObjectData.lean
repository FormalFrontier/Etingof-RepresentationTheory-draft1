/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.CategoryTheory.Abelian.ObjectData

/-- A type of data associated with an object of an abelian category. -/
@[source_ref "Chapter8/Definition8.2.1" (role := supporting)]
abbrev AbelianCategoryObjectData {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (X : C) :=
  CategoryTheory.ProjectiveResolution X

end RepresentationTheory.CategoryTheory.Abelian.ObjectData

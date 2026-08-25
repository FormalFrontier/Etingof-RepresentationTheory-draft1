/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses

/-- The type of degree-indexed extension classes for an ordered pair of objects in an abelian category. -/
@[source_ref "Chapter8/Introduction_8.2" (role := supporting),
  source_ref "Chapter8/Definition8.2.4" (role := supporting)]
noncomputable abbrev CategoryTheory.ExtensionClasses {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C]
    (M N : C) (n : ℕ) : Type _ :=
  CategoryTheory.Abelian.Ext M N n

end RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses

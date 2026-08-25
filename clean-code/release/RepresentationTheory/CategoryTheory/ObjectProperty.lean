/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import RepresentationTheory.Alignment.Attribute

/-!
# Object properties

Definitions associated with object properties on categories.
-/

namespace RepresentationTheory.CategoryTheory.ObjectProperty

/-- The type determined by an object property on a category. -/
@[source_ref "Chapter7/Definition7.1.4" (role := supporting)]
abbrev AssociatedType (C : Type*) [CategoryTheory.Category C]
    (P : CategoryTheory.ObjectProperty C) := P.FullSubcategory

end RepresentationTheory.CategoryTheory.ObjectProperty

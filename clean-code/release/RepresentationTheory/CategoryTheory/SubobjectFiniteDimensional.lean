/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Order.KrullDimension

universe u v

open CategoryTheory

namespace RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional

/-- A category whose subobject orders are finite-dimensional. -/
class SubobjectFiniteDimensional (C : Type u) [Category.{v} C] extends
    toAbelian : Abelian C,
    toEnoughProjectives : EnoughProjectives C where
  /-- An auxiliary type associated to the category. -/
  Auxiliary : Type
  private [auxiliaryFintype : Fintype Auxiliary]
  private auxiliaryObject : Auxiliary → C
  private simple_auxiliaryObject : ∀ i, Simple (auxiliaryObject i)
  private simple_iso_auxiliaryObject_data :
    ∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ auxiliaryObject i)
  private finiteDimensionalOrder_subobject_data :
    ∀ X : C, FiniteDimensionalOrder (Subobject X)

/-
/-- The category has an abelian category structure. -/
/-- The category has enough projectives. -/
-/

namespace SubobjectFiniteDimensional.Auxiliary

/-- The opaque auxiliary type is finite. -/
instance fintype {C : Type u} [Category.{v} C] [SubobjectFiniteDimensional C] :
    Fintype (SubobjectFiniteDimensional.Auxiliary C) :=
  SubobjectFiniteDimensional.auxiliaryFintype

/-- The object of the category associated to an auxiliary index. -/
def object {C : Type u} [Category.{v} C] [SubobjectFiniteDimensional C]
    (i : SubobjectFiniteDimensional.Auxiliary C) : C :=
  SubobjectFiniteDimensional.auxiliaryObject i

/-- The object associated to an auxiliary index is simple. -/
theorem simple_object {C : Type u} [Category.{v} C] [SubobjectFiniteDimensional C]
    (i : SubobjectFiniteDimensional.Auxiliary C) : Simple (object i) := by
  change Simple (SubobjectFiniteDimensional.auxiliaryObject i)
  exact SubobjectFiniteDimensional.simple_auxiliaryObject i

end SubobjectFiniteDimensional.Auxiliary

namespace SubobjectFiniteDimensional

/-- Every simple object is isomorphic to an object indexed by the auxiliary type. -/
theorem simple_iso_auxiliaryObject {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] (X : C) (hX : Simple X) :
    ∃ i, Nonempty (X ≅ Auxiliary.object i) := by
  simpa [Auxiliary.object] using
    SubobjectFiniteDimensional.simple_iso_auxiliaryObject_data X hX

/-- Each object's subobject order is finite-dimensional. -/
theorem finiteDimensionalOrder_subobject' {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] (X : C) : FiniteDimensionalOrder (Subobject X) :=
  SubobjectFiniteDimensional.finiteDimensionalOrder_subobject_data X

/-- The subobjects of any object form a finite-dimensional order. -/
instance finiteDimensionalOrder_subobject {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] (X : C) : FiniteDimensionalOrder (Subobject X) :=
  SubobjectFiniteDimensional.finiteDimensionalOrder_subobject' X

end SubobjectFiniteDimensional

end RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional

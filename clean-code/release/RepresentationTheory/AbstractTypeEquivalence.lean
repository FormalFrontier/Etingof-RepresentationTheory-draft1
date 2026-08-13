/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Equivalence
import RepresentationTheory.Alignment.Attribute

open CategoryTheory

namespace RepresentationTheory.AbstractTypeEquivalence

noncomputable example : FintypeCat.Skeleton ≌ FintypeCat := FintypeCat.Skeleton.equivalence

/-- The type on the left side of the categorical data. -/
def Left : Type := PUnit

/-- The type on the right side of the categorical data. -/
def Right : Type := Bool

/-- A category structure on the left type. -/
instance leftCategory : Category Left where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- A category structure on the right type. -/
instance rightCategory : Category Right where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- A functor from the left type to the right type. -/
def leftToRight : Left ⥤ Right where
  obj _ := true
  map _ := ⟨⟩

/-- A functor from the right type to the left type. -/
def rightToLeft : Right ⥤ Left where
  obj _ := ⟨⟩
  map _ := ⟨⟩

/-- An equivalence between the left and right types equipped with their category structures. -/
@[source_ref "Chapter7/Discussion_after_Definition7.4.1" (role := primary)]
def equivalence : Left ≌ Right where
  functor := leftToRight
  inverse := rightToLeft
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.mk ⟨⟩ ⟨⟩) (fun _ => rfl)
  functor_unitIso_comp _ := rfl

end RepresentationTheory.AbstractTypeEquivalence

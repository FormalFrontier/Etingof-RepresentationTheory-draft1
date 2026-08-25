import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Equivalence

/-!
# Discussion after Definition 7.4.1: Examples of equivalent categories

This file formalizes the two examples of equivalent (but not isomorphic) categories
discussed after Definition 7.4.1.

## FSet and its skeleton

The category **FSet** of finite sets is equivalent to the category whose objects are
the nonnegative integers and whose morphisms `m → n` are the maps
`{1, …, m} → {1, …, n}`. The latter is the *skeleton* of the category of finite sets.

Mathlib's `FintypeCat` is the category of finite types, and `FintypeCat.Skeleton`
is its skeleton (objects are `ℕ`, morphisms `m → n` are functions
`Fin m → Fin n`). The equivalence is `FintypeCat.Skeleton.equivalence`.

## C₁ and C₂

The text introduces two toy categories:

* `C₁`: one object `X` with `Hom(X, X) = {1_X}`.
* `C₂`: two objects `X, Y` with four morphisms `1_X, 1_Y, a : X → Y, b : Y → X`
  satisfying `a ∘ b = 1_Y`, `b ∘ a = 1_X` (so `a`, `b` are mutually inverse).

These are equivalent (`C₁ ≌ C₂`) but not isomorphic (they have different numbers of
objects). We model `C₁` and `C₂` as *codiscrete* categories (every hom-set is a
singleton `PUnit`) on a one- and two-element type respectively; with these models the
four morphisms of `C₂` are exactly the unique elements of its four hom-sets, and
`a, b` are automatically mutually inverse.
-/

open CategoryTheory

namespace Etingof

/-- The category **FSet** of finite sets is equivalent to its skeleton (objects `ℕ`,
morphisms `m → n` given by maps `Fin m → Fin n`). This is
`FintypeCat.Skeleton.equivalence` in Mathlib. (Discussion after Definition 7.4.1) -/
noncomputable example : FintypeCat.Skeleton ≌ FintypeCat := FintypeCat.Skeleton.equivalence

/-- `C₁`: the category with a single object and only its identity morphism. -/
def Cat₁ : Type := PUnit

/-- `C₂`: the category with two objects and four morphisms `1_X, 1_Y, a, b`, where
`a` and `b` are mutually inverse. -/
def Cat₂ : Type := Bool

instance : Category Cat₁ where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

instance : Category Cat₂ where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- The functor `C₁ → C₂` sending the unique object of `C₁` to the first object of
`C₂`. -/
def funct₁₂ : Cat₁ ⥤ Cat₂ where
  obj _ := true
  map _ := ⟨⟩

/-- The functor `C₂ → C₁` collapsing both objects of `C₂` to the unique object of
`C₁`. -/
def funct₂₁ : Cat₂ ⥤ Cat₁ where
  obj _ := ⟨⟩
  map _ := ⟨⟩

/-- `C₁` and `C₂` are equivalent categories. (Discussion after Definition 7.4.1) -/
def cat₁EquivCat₂ : Cat₁ ≌ Cat₂ where
  functor := funct₁₂
  inverse := funct₂₁
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.mk ⟨⟩ ⟨⟩) (fun _ => rfl)
  functor_unitIso_comp _ := rfl

end Etingof

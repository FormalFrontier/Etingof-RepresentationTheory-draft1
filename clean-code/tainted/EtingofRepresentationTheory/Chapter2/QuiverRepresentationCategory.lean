import EtingofRepresentationTheory.Chapter2.Definition2_8_10
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category `Rep Q` of representations of a quiver

Definition 2.8.3 gives the objects (`Etingof.QuiverRepresentation`) and Definition 2.8.10
gives the morphisms (`Etingof.QuiverRepresentationHom`). This file assembles them into a
`CategoryTheory.Category` instance, so that constructions on quiver representations can be
stated as honest functors.

Chapter 6 uses this for the Bernstein-Gelfand-Ponomarev reflection functors
`F⁺ᵢ, F⁻ᵢ : Rep Q → Rep Q̄ᵢ` (Definitions 6.6.3 and 6.6.4), which Example 7.2.2(9) lists
as examples of functors.

The `Quiver` structure is an instance argument, so the same instance also supplies the
category structure on `Rep Q̄ᵢ`: write
`@Etingof.QuiverRepresentation.instCategory k _ Q (Etingof.reversedAtVertex Q i)`.
-/

namespace Etingof

/-- Two representation morphisms are equal as soon as their vertex maps agree. -/
@[ext] theorem QuiverRepresentationHom.ext
    {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    {f g : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂} (h : ∀ v, f.app v = g.app v) : f = g := by
  cases f with
  | mk fa fn => cases g with
    | mk ga gn => have : fa = ga := funext h; subst this; rfl

/-- The identity morphism of a quiver representation: the identity map at every vertex. -/
def QuiverRepresentationHom.id {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    (ρ : Etingof.QuiverRepresentation k Q) : Etingof.QuiverRepresentationHom k Q ρ ρ where
  app _ := LinearMap.id
  naturality _ _ := rfl

/-- Composition of morphisms of quiver representations, vertexwise. -/
def QuiverRepresentationHom.comp {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (g : Etingof.QuiverRepresentationHom k Q ρ₂ ρ₃) :
    Etingof.QuiverRepresentationHom k Q ρ₁ ρ₃ where
  app v := (g.app v).comp (f.app v)
  naturality e x := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [f.naturality e x, g.naturality e (f.app _ x)]

@[simp] theorem QuiverRepresentationHom.id_app {k : Type*} {Q : Type*} [CommSemiring k]
    [Quiver Q] (ρ : Etingof.QuiverRepresentation k Q) (v : Q) :
    (QuiverRepresentationHom.id ρ).app v = LinearMap.id := rfl

@[simp] theorem QuiverRepresentationHom.comp_app {k : Type*} {Q : Type*} [CommSemiring k]
    [Quiver Q] {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (g : Etingof.QuiverRepresentationHom k Q ρ₂ ρ₃) (v : Q) :
    (f.comp g).app v = (g.app v).comp (f.app v) := rfl

/-- The category `Rep Q` of representations of a quiver `Q` over `k`: objects are
`Etingof.QuiverRepresentation k Q` (Definition 2.8.3) and morphisms are
`Etingof.QuiverRepresentationHom` (Definition 2.8.10). -/
instance QuiverRepresentation.instCategory {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] : CategoryTheory.Category (Etingof.QuiverRepresentation k Q) where
  Hom ρ₁ ρ₂ := Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂
  id ρ := QuiverRepresentationHom.id ρ
  comp f g := QuiverRepresentationHom.comp f g
  id_comp _ := by ext v; simp
  comp_id _ := by ext v; simp
  assoc _ _ _ := by ext v; simp

@[simp] theorem QuiverRepresentation.id_app {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] (ρ : Etingof.QuiverRepresentation k Q) (v : Q) :
    Etingof.QuiverRepresentationHom.app (CategoryTheory.CategoryStruct.id ρ) v =
      LinearMap.id := rfl

@[simp] theorem QuiverRepresentation.comp_app {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation k Q} (f : ρ₁ ⟶ ρ₂) (g : ρ₂ ⟶ ρ₃)
    (v : Q) :
    Etingof.QuiverRepresentationHom.app
      (CategoryTheory.CategoryStruct.comp f g) v = (g.app v).comp (f.app v) := rfl

end Etingof

import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

/-- A property characterized by projectivity and epimorphic coproduct desc morphisms. -/
def IsProjectiveEpiSigmaDesc {C : Type u} [Category.{v} C] (P : C) : Prop :=
  Projective P ∧ IsSeparator P

namespace IsProjectiveEpiSigmaDesc

variable {C : Type u} [Category.{v} C] {P : C}

/-- Every object satisfying this property is projective. -/
theorem projective (h : IsProjectiveEpiSigmaDesc P) : Projective P := h.1

/-- Every object satisfying this property is a separator. -/
theorem isSeparator (h : IsProjectiveEpiSigmaDesc P) : IsSeparator P := h.2

/-- Projectivity together with epimorphic coproduct desc morphisms characterizes this property. -/
theorem iff_projective_and_epi_sigma_desc [∀ X : C, HasCoproduct fun _ : P ⟶ X => P] :
    IsProjectiveEpiSigmaDesc P ↔
      Projective P ∧ ∀ X : C, Epi (Sigma.desc fun f : P ⟶ X => f) := by
  rw [IsProjectiveEpiSigmaDesc, isSeparator_iff_epi]

end IsProjectiveEpiSigmaDesc

/-- A property of an object in a category with zero morphisms that supplies epimorphism witnesses
and entails projectivity. -/
class HasProjectiveEpiWitnesses {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : C)
    extends Projective P where
  /-- For each object, the property supplies existential data whose final morphism is an
  epimorphism. -/
  exists_epi : ∀ (X : C), ∃ (n : ℕ) (_ : HasBiproduct (fun _ : Fin n => P))
    (f : biproduct (fun _ : Fin n => P) ⟶ X), Epi f

/-
/-- The projectivity structure carried by an object satisfying this property. -/
-/

end RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

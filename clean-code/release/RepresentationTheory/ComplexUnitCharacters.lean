/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Group.CharacterDuality
import RepresentationTheory.FiniteGroups.CharacterRigidity

noncomputable section

open CategoryTheory Module

namespace RepresentationTheory.ComplexUnitCharacters

variable {G : Type} [CommGroup G]

/-- Constructs a representation on the complex numbers from a homomorphism into the complex units. -/
def representationOfComplexUnitCharacter (ξ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((ξ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((ξ (a * b) : ℂˣ) : ℂ) * x = ((ξ a : ℂˣ) : ℂ) * (((ξ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The representation associated to a complex unit character acts by multiplication by the character value. -/
@[simp] lemma representationOfComplexUnitCharacter_apply (ξ : G →* ℂˣ) (g : G) (z : ℂ) :
    representationOfComplexUnitCharacter ξ g z = (ξ g : ℂ) * z := by
  change (((ξ g : ℂˣ) : ℂ) • LinearMap.id) z = _
  simp

/-- Constructs a finite-dimensional complex representation from a homomorphism into the units of the complex numbers. -/
def fdRepOfComplexUnitCharacter (ξ : G →* ℂˣ) : FDRep ℂ G :=
  FDRep.of (representationOfComplexUnitCharacter ξ)

/-- The character of the finite-dimensional representation associated to a complex unit character is the value of that character. -/
@[simp] lemma character_fdRepOfComplexUnitCharacter (ξ : G →* ℂˣ) (g : G) :
    (fdRepOfComplexUnitCharacter ξ).character g = (ξ g : ℂ) := by
  rw [show (fdRepOfComplexUnitCharacter ξ).character g =
    LinearMap.trace ℂ ℂ (representationOfComplexUnitCharacter ξ g) from rfl]
  change LinearMap.trace ℂ ℂ (((ξ g : ℂˣ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

/-- The finite-dimensional representation associated to a complex unit character has rank one. -/
@[simp] lemma finrank_fdRepOfComplexUnitCharacter (ξ : G →* ℂˣ) :
    Module.finrank ℂ (fdRepOfComplexUnitCharacter ξ : Type) = 1 :=
  Module.finrank_self ℂ

/-- The module underlying the representation associated to a complex unit character is simple. -/
lemma isSimpleModule_representationOfComplexUnitCharacter (ξ : G →* ℂˣ) :
    IsSimpleModule (MonoidAlgebra ℂ G) (representationOfComplexUnitCharacter ξ).asModule := by
  haveI hℂ : IsSimpleModule ℂ ℂ := inferInstance
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := representationOfComplexUnitCharacter ξ)).isSimpleOrder_iff]
  haveI : Nontrivial (Subrepresentation (representationOfComplexUnitCharacter ξ)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have hbt : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact absurd hbt bot_ne_top
  refine ⟨fun W' => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top W'.toSubmodule with h | h
  · left; exact Subrepresentation.toSubmodule_injective h
  · right; exact Subrepresentation.toSubmodule_injective h

/-- The finite-dimensional representation associated to a complex unit character is simple. -/
instance simple_fdRepOfComplexUnitCharacter (ξ : G →* ℂˣ) :
    Simple (fdRepOfComplexUnitCharacter ξ) :=
  haveI := isSimpleModule_representationOfComplexUnitCharacter ξ
  RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule
    (representationOfComplexUnitCharacter ξ)

/-- Two finite-dimensional representations associated to complex unit characters are isomorphic exactly when the characters are equal. -/
lemma fdRepOfComplexUnitCharacter_iso_iff {ξ ξ' : G →* ℂˣ} :
    Nonempty (fdRepOfComplexUnitCharacter ξ ≅ fdRepOfComplexUnitCharacter ξ') ↔ ξ = ξ' := by
  constructor
  · rintro ⟨α⟩
    ext g
    have hg := congrFun (FDRep.char_iso α) g
    rw [character_fdRepOfComplexUnitCharacter, character_fdRepOfComplexUnitCharacter] at hg
    exact hg
  · rintro rfl; exact ⟨Iso.refl _⟩

private lemma rho_eq_character_smul (S : FDRep ℂ G)
    (hdim : Module.finrank ℂ (S : Type) = 1) (g : G) :
    S.ρ g = (S.character g : ℂ) • LinearMap.id := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (S.ρ g)
  have hchar : S.character g = c := by
    change LinearMap.trace ℂ _ (S.ρ g) = c
    rw [hc, map_smul, LinearMap.trace_id, hdim]
    simp
  rw [hchar]; exact hc

private lemma smul_id_inj (S : FDRep ℂ G) (hdim : Module.finrank ℂ (S : Type) = 1) {a b : ℂ}
    (h : (a : ℂ) • (LinearMap.id : (S : Type) →ₗ[ℂ] (S : Type)) = b • LinearMap.id) : a = b := by
  have := congrArg (LinearMap.trace ℂ (S : Type)) h
  rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at this

/-- Every simple finite-dimensional complex representation of a finite commutative group is isomorphic to one associated to a complex unit character. -/
theorem simple_fdRep_iso_fdRepOfComplexUnitCharacter [Finite G] (S : FDRep ℂ G) [Simple S] :
    ∃ ξ : G →* ℂˣ, Nonempty (S ≅ fdRepOfComplexUnitCharacter ξ) := by
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ G) (Representation.asModule S.ρ) :=
    RepresentationTheory.SimpleRepresentationModules.isSimpleModule_of_simple_fdRep S
  have hdim : Module.finrank ℂ (S : Type) = 1 :=
    RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule S.ρ
  have hone : S.character (1 : G) = 1 := by
    rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g h : G, S.character (g * h) = S.character g * S.character h := by
    intro g h
    apply smul_id_inj S hdim
    have h1 : S.ρ (g * h) = (S.character (g * h) : ℂ) • LinearMap.id :=
      rho_eq_character_smul S hdim (g * h)
    have h2 : S.ρ (g * h) = (S.character g * S.character h : ℂ) • LinearMap.id := by
      rw [map_mul, rho_eq_character_smul S hdim g, rho_eq_character_smul S hdim h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    rw [← h1, ← h2]
  have hne : ∀ g : G, S.character g ≠ 0 := by
    intro g h0
    have hgi := hmul g g⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at hgi
    exact one_ne_zero hgi
  let ξ : G →* ℂˣ :=
    { toFun := fun g => Units.mk0 (S.character g) (hne g)
      map_one' := Units.ext (by simp [hone])
      map_mul' := fun g h => Units.ext (by simp [hmul g h, Units.val_mul]) }
  have hcharEq : S.character = (fdRepOfComplexUnitCharacter ξ).character := by
    funext g
    rw [character_fdRepOfComplexUnitCharacter]
    change S.character g = ((Units.mk0 (S.character g) (hne g) : ℂˣ) : ℂ)
    rw [Units.val_mk0]
  exact ⟨ξ, RepresentationTheory.FiniteGroups.CharacterRigidity.nonempty_iso_of_character_eq S
    (fdRepOfComplexUnitCharacter ξ) hcharEq⟩

/-- For a finite commutative group, the number of homomorphisms into the units of the complex numbers equals the number of group elements. -/
theorem natCard_complexUnitCharacters_eq [Finite G] : Nat.card (G →* ℂˣ) = Nat.card G := by
  haveI : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ

end RepresentationTheory.ComplexUnitCharacters

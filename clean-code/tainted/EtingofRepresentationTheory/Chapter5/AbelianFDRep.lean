import Mathlib
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Example4_3_FiniteAbelianGroups
import EtingofRepresentationTheory.Chapter5.CharEqIso

/-!
# Irreducible complex representations of a finite abelian group

For a finite abelian group `G`, the irreducible complex representations are exactly the
one-dimensional characters `ξ : G →* ℂˣ` (Example 4.3: over an algebraically closed field, every
irreducible representation of a commutative group is one-dimensional). This file packages that
classification at the `FDRep ℂ G` level, in the form used by the orbit-method
classification exercises (Exercise 5.27.2 for the affine, Heisenberg, and dihedral groups), whose
stabilizers `G_χ` are abelian.

## Main definitions and results

* `charFDRep ξ`: the one-dimensional `FDRep ℂ G` on which `g` acts by multiplication by `ξ g`.
  Its `ℂ`-dimension is `1` (`charFDRep_finrank`) and its character is `g ↦ ξ g`
  (`charFDRep_character`).
* `charFDRep_simple`: every `charFDRep ξ` is a simple object of `FDRep ℂ G`.
* `charFDRep_iso_iff`: `charFDRep ξ ≅ charFDRep ξ'` iff `ξ = ξ'` (the characters are pairwise
  non-isomorphic).
* `exists_charFDRep_iso` (completeness): every simple `FDRep ℂ G` is isomorphic to some
  `charFDRep ξ`.
* `card_charFDRep_dual`: there are exactly `|G|` characters, `Nat.card (G →* ℂˣ) = Nat.card G`.

The simplicity and module-transfer lemmas reuse `Etingof.simple_fdRepOf_of_isSimpleModule` and
`Etingof.isSimpleModule_asModule_of_simple` (Exercise 4.2.3), the one-dimensionality of abelian
irreducibles `Etingof.Example4_3_FiniteAbelianGroups`, and the character-to-isomorphism result
`Etingof.charEq_iso` (`CharEqIso`).
-/

noncomputable section

open CategoryTheory Module

namespace Etingof.AbelianFDRep

variable {G : Type} [CommGroup G]

/-- The one-dimensional representation on `ℂ` attached to a character `ξ : G →* ℂˣ`:
`g` acts by multiplication by `ξ g`. -/
def charRep (ξ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((ξ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((ξ (a * b) : ℂˣ) : ℂ) * x = ((ξ a : ℂˣ) : ℂ) * (((ξ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

@[simp] lemma charRep_apply (ξ : G →* ℂˣ) (g : G) (z : ℂ) :
    charRep ξ g z = (ξ g : ℂ) * z := by
  change (((ξ g : ℂˣ) : ℂ) • LinearMap.id) z = _
  simp

/-- The one-dimensional `FDRep ℂ G` attached to a character `ξ : G →* ℂˣ`. -/
def charFDRep (ξ : G →* ℂˣ) : FDRep ℂ G := FDRep.of (charRep ξ)

/-- The character of `charFDRep ξ` is `g ↦ ξ g`. -/
@[simp] lemma charFDRep_character (ξ : G →* ℂˣ) (g : G) :
    (charFDRep ξ).character g = (ξ g : ℂ) := by
  rw [show (charFDRep ξ).character g = LinearMap.trace ℂ ℂ (charRep ξ g) from rfl]
  change LinearMap.trace ℂ ℂ (((ξ g : ℂˣ) : ℂ) • LinearMap.id) = _
  rw [map_smul, LinearMap.trace_id]
  simp

/-- `charFDRep ξ` is one-dimensional. -/
@[simp] lemma charFDRep_finrank (ξ : G →* ℂˣ) :
    Module.finrank ℂ (charFDRep ξ : Type) = 1 :=
  Module.finrank_self ℂ

/-- The one-dimensional `charRep ξ` is simple as a `ℂ[G]`-module: its only `ℂ`-subspaces are `⊥`
and `⊤`, and all of them are invariant. -/
lemma charRep_asModule_simple (ξ : G →* ℂˣ) :
    IsSimpleModule (MonoidAlgebra ℂ G) (charRep ξ).asModule := by
  haveI hℂ : IsSimpleModule ℂ ℂ := inferInstance
  rw [isSimpleModule_iff,
    ← (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := charRep ξ)).isSimpleOrder_iff]
  haveI : Nontrivial (Subrepresentation (charRep ξ)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have hbt : (⊥ : Submodule ℂ ℂ) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact absurd hbt bot_ne_top
  refine ⟨fun W' => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top W'.toSubmodule with h | h
  · left; exact Subrepresentation.toSubmodule_injective h
  · right; exact Subrepresentation.toSubmodule_injective h

/-- Every `charFDRep ξ` is a simple object of `FDRep ℂ G`. -/
instance charFDRep_simple (ξ : G →* ℂˣ) : Simple (charFDRep ξ) :=
  haveI := charRep_asModule_simple ξ
  Etingof.simple_fdRepOf_of_isSimpleModule (charRep ξ)

/-- **Pairwise non-isomorphism.** Two characters give isomorphic one-dimensional representations
iff they are equal. -/
lemma charFDRep_iso_iff {ξ ξ' : G →* ℂˣ} :
    Nonempty (charFDRep ξ ≅ charFDRep ξ') ↔ ξ = ξ' := by
  constructor
  · rintro ⟨α⟩
    ext g
    have hg := congrFun (FDRep.char_iso α) g
    rw [charFDRep_character, charFDRep_character] at hg
    exact hg
  · rintro rfl; exact ⟨Iso.refl _⟩

/-- A one-dimensional endomorphism of a simple `FDRep ℂ G` acts as the scalar given by its
character: `S.ρ g = (S.character g) • id`. -/
private lemma rho_eq_character_smul (S : FDRep ℂ G) (hdim : Module.finrank ℂ (S : Type) = 1)
    (g : G) : S.ρ g = (S.character g : ℂ) • LinearMap.id := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (S.ρ g)
  have hchar : S.character g = c := by
    change LinearMap.trace ℂ _ (S.ρ g) = c
    rw [hc, map_smul, LinearMap.trace_id, hdim]
    simp
  rw [hchar]; exact hc

/-- Scalars are determined by their action on a one-dimensional space. -/
private lemma smul_id_inj (S : FDRep ℂ G) (hdim : Module.finrank ℂ (S : Type) = 1) {a b : ℂ}
    (h : (a : ℂ) • (LinearMap.id : (S : Type) →ₗ[ℂ] (S : Type)) = b • LinearMap.id) : a = b := by
  have := congrArg (LinearMap.trace ℂ (S : Type)) h
  rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at this

/-- **Completeness.** Every simple `FDRep ℂ G` for a finite abelian group `G` is isomorphic to
`charFDRep ξ` for some character `ξ : G →* ℂˣ`. -/
theorem exists_charFDRep_iso [Finite G] (S : FDRep ℂ G) [Simple S] :
    ∃ ξ : G →* ℂˣ, Nonempty (S ≅ charFDRep ξ) := by
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ G) (Representation.asModule S.ρ) :=
    Etingof.isSimpleModule_asModule_of_simple S
  have hdim : Module.finrank ℂ (S : Type) = 1 := Etingof.Example4_3_FiniteAbelianGroups S.ρ
  -- the eigenvalue of `g` is `S.character g`; establish it is a nonzero multiplicative character
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
  have hcharEq : S.character = (charFDRep ξ).character := by
    funext g
    rw [charFDRep_character]
    change S.character g = ((Units.mk0 (S.character g) (hne g) : ℂˣ) : ℂ)
    rw [Units.val_mk0]
  exact ⟨ξ, Etingof.charEq_iso S (charFDRep ξ) hcharEq⟩

/-- **Counting.** For a finite abelian group `G`, there are exactly `|G|` characters. -/
theorem card_charFDRep_dual [Finite G] : Nat.card (G →* ℂˣ) = Nat.card G := by
  haveI : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ

end Etingof.AbelianFDRep

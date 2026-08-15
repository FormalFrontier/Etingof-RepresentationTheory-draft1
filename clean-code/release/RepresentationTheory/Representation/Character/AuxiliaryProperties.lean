/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroupRepresentations.Auxiliary
import RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar
import RepresentationTheory.Representation.Character.InversionAndInvariantForms
import RepresentationTheory.Representation.Character.AuxiliaryVanishing
import RepresentationTheory.Alignment.Attribute

open scoped MonoidAlgebra

namespace RepresentationTheory.Representation.Character.AuxiliaryProperties

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

private lemma cardCastNeZero : (Fintype.card G : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_pos.ne'

/-- If an auxiliary predicate fails, the character agrees at every group element and its inverse. -/
theorem character_inversionInvariant_of_not_auxiliaryPredicate (ρ : Representation ℂ G V)
    (h : ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty ρ) :
    ∀ g, ρ.character g⁻¹ = ρ.character g := by
  have hex : ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v) := by
    by_contra hc; exact h hc
  obtain ⟨e, he⟩ := hex
  intro g
  have hconj : ρ.dual g = e.conj (ρ g) := by
    ext w
    rw [LinearEquiv.conj_apply_apply, he g (e.symm w), LinearEquiv.apply_symm_apply]
  calc ρ.character g⁻¹
      = ρ.dual.character g := (ρ.char_dual g).symm
    _ = LinearMap.trace ℂ (Module.Dual ℂ V) (e.conj (ρ g)) := by
          rw [Representation.character, hconj]
    _ = LinearMap.trace ℂ V (ρ g) := LinearMap.trace_conj' (ρ g) e
    _ = ρ.character g := rfl

/-- For a simple representation, the second and third auxiliary predicates displayed here are incompatible. -/
theorem simpleRepresentation_not_secondAndThirdAuxiliaryPredicates (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    ¬ (RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ ∧
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ) := by
  classical
  rintro ⟨⟨Bs, hBs_sym, hBs_nd, hBs_inv⟩, ⟨Bq, hBq_skew, hBq_nd, hBq_inv⟩⟩
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  haveI : Nonempty G := ⟨1⟩
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.card_pos.ne')
  haveI hNT : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hchar_sd : ∀ g, ρ.character g⁻¹ = ρ.character g := by
    obtain ⟨e, he⟩ :=
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.exists_intertwiner_to_dual_of_nondegenerate_invariant_form ρ Bs hBs_nd hBs_inv
    intro g
    have hconj : ρ.dual g = e.conj (ρ g) := by
      ext w; rw [LinearEquiv.conj_apply_apply, he g (e.symm w), LinearEquiv.apply_symm_apply]
    calc ρ.character g⁻¹
        = ρ.dual.character g := (ρ.char_dual g).symm
      _ = LinearMap.trace ℂ (Module.Dual ℂ V) (e.conj (ρ g)) := by
            rw [Representation.character, hconj]
      _ = LinearMap.trace ℂ V (ρ g) := LinearMap.trace_conj' (ρ g) e
      _ = ρ.character g := rfl
  have hd1 : Module.finrank ℂ ((Representation.linHom ρ ρ.dual).invariants) = 1 := by
    have hkey := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom ρ ρ.dual)
    have hortho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
    have hchar : ∀ g, (Representation.linHom ρ ρ.dual).character g
        = ρ.character g * ρ.character g⁻¹ := fun g => by
      rw [Representation.char_linHom, Representation.char_dual, hchar_sd g]
    rw [Finset.sum_congr rfl (fun g _ => hchar g), hortho] at hkey
    exact_mod_cast hkey.symm
  have hmem : ∀ B : V →ₗ[ℂ] Module.Dual ℂ V, (∀ g v w, B (ρ g v) (ρ g w) = B v w) →
      B ∈ (Representation.linHom ρ ρ.dual).invariants := by
    intro B hB
    rw [Representation.mem_invariants]
    intro g
    ext v w
    rw [Representation.linHom_apply]
    simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply]
    exact hB g⁻¹ v w
  have memS : (Bs : V →ₗ[ℂ] Module.Dual ℂ V) ∈ (Representation.linHom ρ ρ.dual).invariants :=
    hmem Bs hBs_inv
  have memQ : (Bq : V →ₗ[ℂ] Module.Dual ℂ V) ∈ (Representation.linHom ρ ρ.dual).invariants :=
    hmem Bq hBq_inv
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  have hBsne : (⟨Bs, memS⟩ : (Representation.linHom ρ ρ.dual).invariants) ≠ 0 := by
    intro h0
    have hBs0 : Bs = 0 := by simpa using congrArg Subtype.val h0
    exact hv0 (hBs_nd v0 (fun w => by simp [hBs0]))
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (⟨Bs, memS⟩ : (Representation.linHom ρ ρ.dual).invariants)
      hBsne).mp hd1 ⟨Bq, memQ⟩
  have hcoe : c • Bs = Bq := by simpa using congrArg Subtype.val hc
  have hBqzero : Bq = 0 := by
    ext v w
    have hxvw : Bq v w = c * Bs v w := by rw [← hcoe]; simp
    have hxwv : Bq w v = c * Bs v w := by rw [← hcoe]; simp [hBs_sym w v]
    have hz : Bq v w = 0 := by
      linear_combination (1 / 2 : ℂ) * hxvw - (1 / 2 : ℂ) * hxwv + (1 / 2 : ℂ) * hBq_skew v w
    simpa using hz
  exact hv0 (hBq_nd v0 (fun w => by simp [hBqzero]))

private noncomputable def invertibleCardCast : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero cardCastNeZero

private theorem neZeroNatCardCast : NeZero (Nat.card G : ℂ) :=
  ⟨by rw [Nat.card_eq_fintype_card]; exact cardCastNeZero⟩

/-- For a simple complex representation, an auxiliary predicate is equivalent to an associated auxiliary value being one. -/
@[source_ref "Chapter5/Definition5.1.4" (role := primary),
  source_ref "Chapter5/Theorem5.1.5/Derived2" (role := supporting)]
theorem auxiliaryPredicate_iff_auxiliaryValue_eq_one (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ ↔
      RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1 :=
  ⟨RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_eq_one_of_auxiliary_property ρ hρ,
    RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_of_auxiliary_eq_one ρ hρ⟩

/-- Auxiliary declaration whose formal type could not be displayed. -/
theorem auxiliaryStatement (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hq : RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = -1 := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  have hsd := character_inversionInvariant_of_not_auxiliaryPredicate ρ
    (RepresentationTheory.FiniteGroupRepresentations.Auxiliary.not_auxiliaryRepresentationProperty_of_conditionOne hq)
  rcases RepresentationTheory.Representation.Character.AuxiliaryVanishing.auxiliaryStatement ρ hρ hsd with h1 | hm1
  · exact absurd ⟨RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_of_auxiliary_eq_one ρ hρ h1, hq⟩
      (simpleRepresentation_not_secondAndThirdAuxiliaryPredicates ρ hρ)
  · exact hm1

/-- Auxiliary declaration whose formal type could not be displayed. -/
theorem auxiliaryStatement'''' (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = -1) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  by_cases hsd : ∀ g, ρ.character g⁻¹ = ρ.character g
  · rcases RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_or_auxiliary_condition_of_character_inv_eq ρ hρ hsd with hr | hq
    · exact absurd (RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_eq_one_of_auxiliary_property ρ hρ hr)
        (by rw [h]; norm_num)
    · exact hq
  · exact absurd (RepresentationTheory.Representation.Character.AuxiliaryVanishing.auxiliaryValue_eq_zero_of_character_not_inversionInvariant ρ hρ hsd)
      (by rw [h]; norm_num)

/-- Auxiliary declaration whose formal type could not be displayed. -/
@[source_ref "Chapter5/Definition5.1.4" (role := supporting),
  source_ref "Chapter5/Theorem5.1.5/Derived2" (role := supporting)]
theorem auxiliaryStatement''' (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ ↔
      RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = -1 :=
  ⟨auxiliaryStatement ρ hρ,
    auxiliaryStatement'''' ρ hρ⟩

/-- Auxiliary declaration whose formal type could not be displayed. -/
theorem auxiliaryStatement' (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 0 ∨
      RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1 ∨
      RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = -1 := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  by_cases hsd : ∀ g, ρ.character g⁻¹ = ρ.character g
  · rcases RepresentationTheory.Representation.Character.AuxiliaryVanishing.auxiliaryStatement ρ hρ hsd with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (RepresentationTheory.Representation.Character.AuxiliaryVanishing.auxiliaryValue_eq_zero_of_character_not_inversionInvariant ρ hρ hsd)

/-- Auxiliary declaration whose formal type could not be displayed. -/
theorem auxiliaryStatement'' (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ ∈
      ({0, 1, -1} : Set ℂ) := by
  rcases auxiliaryStatement' ρ hρ with h | h | h <;>
    simp [h]

/-- For a simple complex representation, an auxiliary predicate is equivalent to vanishing of an associated auxiliary value. -/
@[source_ref "Chapter5/Definition5.1.4" (role := primary),
  source_ref "Chapter5/Theorem5.1.5/Derived2" (role := supporting)]
theorem auxiliaryPredicate_iff_auxiliaryValue_eq_zero (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty ρ ↔
      RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 0 := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  constructor
  · intro hc
    have hnr : ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ :=
      fun hr => RepresentationTheory.FiniteGroupRepresentations.Auxiliary.not_auxiliaryRepresentationProperty_of_conditionTwo hr hc
    have hnq : ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ := fun hq =>
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.not_auxiliaryRepresentationProperty_of_conditionOne hq hc
    rcases auxiliaryStatement' ρ hρ with h0 | h1 | hm1
    · exact h0
    · exact absurd (RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_of_auxiliary_eq_one ρ hρ h1) hnr
    · exact absurd (auxiliaryStatement'''' ρ hρ hm1) hnq
  · intro h0
    by_contra hnc
    have hsd := character_inversionInvariant_of_not_auxiliaryPredicate ρ hnc
    rcases RepresentationTheory.Representation.Character.AuxiliaryVanishing.auxiliaryStatement ρ hρ hsd with h1 | hm1
    · rw [h0] at h1; norm_num at h1
    · rw [h0] at hm1; norm_num at hm1

/-- A simple complex representation satisfies at least one of three displayed auxiliary predicates. -/
theorem simpleRepresentation_auxiliaryPredicate_disjunction (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty ρ ∨
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ ∨
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ := by
  by_cases hsd : ∀ g, ρ.character g⁻¹ = ρ.character g
  · rcases RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_or_auxiliary_condition_of_character_inv_eq ρ hρ hsd with hr | hq
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hq)
  · refine Or.inl ?_
    by_contra hnc
    exact hsd (character_inversionInvariant_of_not_auxiliaryPredicate ρ hnc)

/-- The first and third auxiliary predicates displayed here are incompatible. -/
theorem not_firstAndThirdAuxiliaryPredicates (ρ : Representation ℂ G V) :
    ¬ (RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty ρ ∧
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ) :=
  fun ⟨hc, hr⟩ =>
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.not_auxiliaryRepresentationProperty_of_conditionTwo hr hc

/-- The first and second auxiliary predicates displayed here are incompatible. -/
theorem not_firstAndSecondAuxiliaryPredicates (ρ : Representation ℂ G V) :
    ¬ (RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty ρ ∧
      RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ) :=
  fun ⟨hc, hq⟩ =>
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.not_auxiliaryRepresentationProperty_of_conditionOne hq hc

end RepresentationTheory.Representation.Character.AuxiliaryProperties

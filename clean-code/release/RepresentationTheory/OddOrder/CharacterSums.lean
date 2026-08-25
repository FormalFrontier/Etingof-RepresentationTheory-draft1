/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteGroupRepresentations.Auxiliary
import RepresentationTheory.Representation.Character.InversionAndInvariantForms
import RepresentationTheory.FiniteGroupCharacterArithmetic
import RepresentationTheory.SimpleRepresentationModules
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.OddOrder.CharacterSums

section CharacterSums

variable {G : Type*} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- Provides an auxiliary self-equivalence for a finite group of odd cardinality. -/
def auxiliaryEquivOfOddCard (hodd : Odd (Fintype.card G)) : G ≃ G where
  toFun g := g ^ 2
  invFun g := g ^ ((Fintype.card G + 1) / 2)
  left_inv g := by
    have hdvd : 2 ∣ Fintype.card G + 1 := hodd.add_one.two_dvd
    change (g ^ 2) ^ ((Fintype.card G + 1) / 2) = g
    rw [← pow_mul, Nat.mul_div_cancel' hdvd, pow_succ, pow_card_eq_one, one_mul]
  right_inv g := by
    have hdvd : 2 ∣ Fintype.card G + 1 := hodd.add_one.two_dvd
    change (g ^ ((Fintype.card G + 1) / 2)) ^ 2 = g
    rw [← pow_mul, Nat.div_mul_cancel hdvd, pow_succ, pow_card_eq_one, one_mul]

/-- The auxiliary self-equivalence sends each group element to its square. -/
@[simp] theorem auxiliaryEquivOfOddCard_apply_eq_square (hodd : Odd (Fintype.card G)) (g : G) :
    auxiliaryEquivOfOddCard hodd g = g ^ 2 := rfl

/-- For a finite group of odd cardinality, summing a character on squares gives its ordinary sum. -/
theorem sum_character_square_eq_sum_character_of_odd_card (hodd : Odd (Fintype.card G)) (ρ : Representation ℂ G V) :
    ∑ g : G, ρ.character (g ^ 2) = ∑ g : G, ρ.character g :=
  Equiv.sum_comp (auxiliaryEquivOfOddCard hodd) ρ.character

private def stableSubmodule (ρ : Representation ℂ G V) (P : Submodule ℂ ρ.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, ρ g (ρ.asModuleEquiv x) ∈ P) :
    Submodule (MonoidAlgebra ℂ G) ρ.asModule where
  carrier := P
  add_mem' hx hy := P.add_mem hx hy
  zero_mem' := P.zero_mem
  smul_mem' r x hx := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r₁ r₂ h₁ h₂ => rw [add_smul]; exact P.add_mem h₁ h₂
    | single g a =>
        have hsingle : (MonoidAlgebra.single g a : MonoidAlgebra ℂ G) =
            a • MonoidAlgebra.single g (1 : ℂ) := by
          rw [MonoidAlgebra.smul_single', mul_one]
        rw [hsingle, smul_assoc]
        apply P.smul_mem
        rw [Representation.single_smul, one_smul]
        exact hP g x hx

private theorem mem_stableSubmodule (ρ : Representation ℂ G V) (P : Submodule ℂ ρ.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, ρ g (ρ.asModuleEquiv x) ∈ P) (x : ρ.asModule) :
    x ∈ stableSubmodule ρ P hP ↔ x ∈ P :=
  Iff.rfl

/-- A nontrivial simple representation has trivial invariant subspace. -/
theorem invariants_eq_bot_of_simple_of_nontrivial (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) (hnontriv : ∃ g, ρ g ≠ 1) :
    Representation.invariants ρ = ⊥ := by
  have hP : ∀ (g : G), ∀ x ∈ Representation.invariants ρ,
      ρ g (ρ.asModuleEquiv x) ∈ Representation.invariants ρ := by
    intro g x hx
    have hxx : ρ g (ρ.asModuleEquiv x) = x :=
      (Representation.mem_invariants ρ x).mp hx g
    rw [hxx]; exact hx
  rcases hirr.eq_bot_or_eq_top (stableSubmodule ρ (Representation.invariants ρ) hP) with h | h
  · rw [Submodule.eq_bot_iff] at h ⊢
    intro x hx
    exact h x ((mem_stableSubmodule ρ _ hP x).mpr hx)
  · exfalso
    obtain ⟨g, hg⟩ := hnontriv
    apply hg
    ext v
    have hv : v ∈ Representation.invariants ρ :=
      (mem_stableSubmodule ρ _ hP v).mp (h ▸ Submodule.mem_top)
    rw [Module.End.one_apply]
    exact (Representation.mem_invariants ρ v).mp hv g

/-- The character sum on squares vanishes for a nontrivial simple representation of a finite group of odd cardinality. -/
theorem sum_character_square_eq_zero_of_odd_card (hodd : Odd (Fintype.card G)) (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) (hnontriv : ∃ g, ρ g ≠ 1) :
    ∑ g : G, ρ.character (g ^ 2) = 0 := by
  rw [sum_character_square_eq_sum_character_of_odd_card hodd ρ]
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  have hkey := Representation.card_inv_mul_sum_char_eq_finrank ρ
  rw [invariants_eq_bot_of_simple_of_nontrivial ρ hirr hnontriv, finrank_bot,
    Nat.cast_zero] at hkey
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd (inv_eq_zero.mp h) hcard
  · exact h

/-- Under an auxiliary condition, the character sum on squares equals the group cardinality. -/
theorem character_sum_square_eq_card_of_auxiliary (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ) :
    ∑ g : G, ρ.character (g ^ 2) = (Fintype.card G : ℂ) := by
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hFS : RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar ρ = 1 :=
    RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_eq_one_of_auxiliary_property ρ hirr h
  rw [RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar, inv_mul_eq_one₀ hcard] at hFS

  rw [hFS]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.character, pow_two]

/-- Auxiliary dichotomy for a simple representation admitting a comparison with its dual. -/
theorem auxiliary_of_simple_of_dual_intertwiner
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hsd : ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v)) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ ∨ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ := by
  classical
  obtain ⟨e, he⟩ := hsd

  have hchar : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g := by
    intro g
    have hconj : ρ.dual g = e.conj (ρ g) := by
      ext w
      rw [LinearEquiv.conj_apply_apply, he g (e.symm w), LinearEquiv.apply_symm_apply]
    calc Representation.character ρ g⁻¹
        = Representation.character ρ.dual g := (ρ.char_dual g).symm
      _ = LinearMap.trace ℂ (Module.Dual ℂ V) (e.conj (ρ g)) := by rw [Representation.character,
            hconj]
      _ = LinearMap.trace ℂ V (ρ g) := LinearMap.trace_conj' (ρ g) e
      _ = Representation.character ρ g := rfl
  exact RepresentationTheory.Representation.Character.InversionAndInvariantForms.auxiliary_property_or_auxiliary_condition_of_character_inv_eq ρ hirr hchar

/-- Auxiliary exclusion for a nontrivial simple representation of a finite group of odd cardinality. -/
theorem auxiliary_not_of_odd_card_of_simple_of_nontrivial
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnontriv : ∃ g, ρ g ≠ 1) :
    ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo ρ := by
  intro hreal
  have h0 : ∑ g : G, ρ.character (g ^ 2) = 0 :=
    sum_character_square_eq_zero_of_odd_card hodd ρ hirr hnontriv
  have hc : ∑ g : G, ρ.character (g ^ 2) = (Fintype.card G : ℂ) :=
    character_sum_square_eq_card_of_auxiliary ρ hirr hreal
  rw [h0] at hc
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hc.symm

/-- Auxiliary exclusion for a simple representation of a finite group of odd cardinality. -/
theorem auxiliary_not_of_odd_card_of_simple
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    ¬ RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne ρ := by
  classical
  intro hquat

  have heven : Even (Module.finrank ℂ V) :=
    RepresentationTheory.Representation.Character.InversionAndInvariantForms.even_finrank_of_auxiliary ρ hquat

  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule := hirr
  haveI := RepresentationTheory.SimpleRepresentationModules.simple_fdRep_of_isSimpleModule ρ

  have hdvd : Module.finrank ℂ V ∣ Fintype.card G := RepresentationTheory.FiniteGroupCharacterArithmetic.finrank_dvd_card_of_simple G (FDRep.of ρ)

  obtain ⟨k, hk⟩ := heven
  obtain ⟨m, hm⟩ := hdvd
  rw [Nat.odd_iff] at hodd
  have hcard : Fintype.card G = 2 * (k * m) := by rw [hm, hk]; ring
  omega

/-- Auxiliary consequence for a nontrivial simple representation of a finite group of odd cardinality. -/
@[source_ref "Chapter5/Exercise5.3.3" (role := primary)]
theorem auxiliary_of_odd_card_of_simple_of_nontrivial
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnontriv : ∃ g, ρ g ≠ 1) :
    RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty ρ := by

  intro hsd
  rcases auxiliary_of_simple_of_dual_intertwiner ρ hirr hsd with hreal | hquat
  · exact auxiliary_not_of_odd_card_of_simple_of_nontrivial hodd ρ hirr hnontriv hreal
  · exact auxiliary_not_of_odd_card_of_simple hodd ρ hirr hquat

end CharacterSums

end RepresentationTheory.OddOrder.CharacterSums

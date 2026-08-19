/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.CharacterIntegrality
import RepresentationTheory.NumberTheory.IntegralClosure.Rat
import RepresentationTheory.Alignment.Attribute

/-!
# Finite Group Character Arithmetic
-/

namespace RepresentationTheory.FiniteGroupCharacterArithmetic

set_option linter.unusedFintypeInType false in
open CategoryTheory Polynomial Matrix in
/-- Every value of a finite-group complex character is integral over the integers. -/
@[source_ref "Chapter5/Discussion_proof_of_Theorem5.3.1" (role := supporting)]
theorem character_isIntegral
    {G : Type*} [Group G] [Fintype G]
    (V : FDRep ℂ G) (g : G) :
    IsIntegral ℤ (V.character g) := by
  classical
  set N := Fintype.card G with hN
  have hNpos : 0 < N := Fintype.card_pos
  set f : Module.End ℂ V := V.ρ g with hf
  have hfN : f ^ N = 1 := by rw [hf, ← map_pow, pow_card_eq_one, map_one]
  have hchar : V.character g = f.charpoly.roots.sum := by
    rw [FDRep.character,
      Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits f.charpoly)]
  rw [hchar]
  have hroot : ∀ r ∈ f.charpoly.roots, IsIntegral ℤ r := by
    intro r hr
    have hr0 : f.charpoly.IsRoot r :=
      (Polynomial.mem_roots (f.charpoly_monic.ne_zero)).mp hr
    have heig : f.HasEigenvalue r :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f r).mpr hr0
    have heigN : (1 : Module.End ℂ V).HasEigenvalue (r ^ N) := by
      have := heig.pow N
      rwa [hfN] at this
    have hrN : r ^ N = 1 := by
      obtain ⟨v, hv⟩ := heigN.exists_hasEigenvector
      have happ : v = r ^ N • v := by
        have h := hv.apply_eq_smul
        rwa [Module.End.one_apply] at h
      have : (r ^ N - 1) • v = 0 := by
        rw [sub_smul, one_smul, ← happ, sub_self]
      rcases smul_eq_zero.mp this with hz | hz
      · exact sub_eq_zero.mp hz
      · exact absurd hz hv.2
    refine ⟨X ^ N - C 1, Polynomial.monic_X_pow_sub_C 1 hNpos.ne', ?_⟩
    simp [hrN]
  have hmem : f.charpoly.roots.sum ∈ integralClosure ℤ ℂ :=
    (integralClosure ℤ ℂ).multiset_sum_mem (fun r hr => hroot r hr)
  exact hmem

open CategoryTheory in
/-- The complex dimension of a simple finite-group representation divides the group order. -/
@[source_ref "Chapter5/Introduction_5.3" (role := supporting),
  source_ref "Chapter5/Theorem5.3.1" (role := primary),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.3.1" (role := primary)]
theorem finrank_dvd_card_of_simple
    (G : Type*) [Group G] [Fintype G]
    (V : FDRep ℂ G) [Simple V] :
    Module.finrank ℂ V ∣ Fintype.card G := by
  classical
  have hN0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hN0
  have hortho : ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
    have h := FDRep.char_orthonormal V V
    rw [if_pos ⟨Iso.refl V⟩] at h
    have h2 := congrArg (fun x => (Fintype.card G : ℂ) • x) h
    simpa using h2
  have hdpos : 0 < Module.finrank ℂ V := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with hfr0 | hpos
    · exfalso
      haveI : Subsingleton V := Module.finrank_zero_iff.mp hfr0
      have hzero : ∀ g : G, V.character g = 0 := fun g => by
        rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
      rw [Finset.sum_congr rfl (fun g _ => by rw [hzero g, zero_mul]),
        Finset.sum_const_zero] at hortho
      exact hN0 hortho.symm
    · exact hpos
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  set T : ℂ := ∑ K : ConjClasses G,
      ((Fintype.card {h // IsConj K.out h} : ℂ) * V.character K.out
          / (Module.finrank ℂ V : ℂ)) * V.character (K.out)⁻¹ with hT_def
  have hT_int : IsIntegral ℤ T := by
    rw [hT_def]
    refine (integralClosure ℤ ℂ).sum_mem (fun K _ => ?_)
    exact
      (RepresentationTheory.CharacterIntegrality.isIntegral_card_conjClass_mul_character_div_finrank
        G V K.out hdpos).mul (character_isIntegral V (K.out)⁻¹)
  have hregroup : ∑ g : G, V.character g * V.character g⁻¹
      = ∑ K : ConjClasses G,
          (Fintype.card {h // IsConj K.out h} : ℂ)
            * (V.character K.out * V.character (K.out)⁻¹) := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (ConjClasses G)))
          (g := ConjClasses.mk) (f := fun g => V.character g * V.character g⁻¹)
          (fun g _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    have hmkout : ConjClasses.mk K.out = K := Quotient.out_eq K
    have hconst : ∀ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = K),
        V.character g * V.character g⁻¹
          = V.character K.out * V.character (K.out)⁻¹ := by
      intro g hg
      rw [Finset.mem_filter] at hg
      have hconj : IsConj g K.out :=
        ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [hmkout]; exact hg.2)
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have e1 : V.character K.out = V.character g := by
        rw [← hc]; exact V.char_conj g c
      have e2 : V.character (K.out)⁻¹ = V.character g⁻¹ := by
        rw [← hc, show (c * g * c⁻¹)⁻¹ = c * g⁻¹ * c⁻¹ by group]
        exact V.char_conj g⁻¹ c
      rw [e1, e2]
    have hfilt : Finset.univ.filter (fun g => ConjClasses.mk g = K)
        = Finset.univ.filter (fun h => IsConj K.out h) := by
      apply Finset.filter_congr
      intro g _
      have hiff : (ConjClasses.mk g = K) ↔ (ConjClasses.mk g = ConjClasses.mk K.out) := by
        rw [hmkout]
      rw [hiff, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]
    have hcard : (Finset.univ.filter (fun g => ConjClasses.mk g = K)).card
        = Fintype.card {h // IsConj K.out h} := by
      rw [hfilt, ← Fintype.card_subtype]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcard]
  have hdT : (Module.finrank ℂ V : ℂ) * T = (Fintype.card G : ℂ) := by
    rw [hT_def, Finset.mul_sum]
    have hstep : ∀ K : ConjClasses G,
        (Module.finrank ℂ V : ℂ)
            * (((Fintype.card {h // IsConj K.out h} : ℂ) * V.character K.out
                  / (Module.finrank ℂ V : ℂ)) * V.character (K.out)⁻¹)
          = (Fintype.card {h // IsConj K.out h} : ℂ)
              * (V.character K.out * V.character (K.out)⁻¹) := by
      intro K
      field_simp
    rw [Finset.sum_congr rfl (fun K _ => hstep K), ← hregroup, hortho]
  set q : ℚ := (Fintype.card G : ℚ) / (Module.finrank ℂ V : ℚ) with hq_def
  have hq_c : algebraMap ℚ ℂ q = (Fintype.card G : ℂ) / (Module.finrank ℂ V : ℂ) := by
    rw [hq_def, map_div₀, map_natCast, map_natCast]
  have hT_c : T = (Fintype.card G : ℂ) / (Module.finrank ℂ V : ℂ) := by
    rw [eq_div_iff hd0, mul_comm]; exact hdT
  have hqint : ∃ n : ℤ, q = n := by
    rw [← RepresentationTheory.NumberTheory.IntegralClosure.Rat.Rat.isIntegral_complex_iff q,
      hq_c, ← hT_c]; exact hT_int
  obtain ⟨n, hn⟩ := hqint
  rw [hq_def, div_eq_iff (by exact_mod_cast hdpos.ne')] at hn
  have hZ : (Fintype.card G : ℤ) = n * (Module.finrank ℂ V : ℤ) := by exact_mod_cast hn
  have : (Module.finrank ℂ V : ℤ) ∣ (Fintype.card G : ℤ) := ⟨n, by rw [hZ]; ring⟩
  exact_mod_cast this

end RepresentationTheory.FiniteGroupCharacterArithmetic

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FDRep.RegularRepresentationCharacter
import RepresentationTheory.NumberTheory.IntegralClosure.Rat
import RepresentationTheory.Alignment.Attribute

open Representation CategoryTheory Finset
open RepresentationTheory.FDRep.GroupAlgebraDecomposition
open RepresentationTheory.FDRep.RegularRepresentationCharacter

namespace RepresentationTheory.FiniteGroup.PrimePowerConjugacyClass.Auxiliary

variable (G : Type) [Group G] [Fintype G] [DecidableEq G]

set_option linter.unusedFintypeInType false in
omit [DecidableEq G] in
private lemma characterValue_isIntegral (V : FDRep ℂ G) (g : G) :
    IsIntegral ℤ (V.character g) := by
  let b := Module.Free.chooseBasis ℂ V
  set M := LinearMap.toMatrix b b (V.ρ g) with hM_def
  set n := Fintype.card G
  have htrace : V.character g = M.trace :=
    LinearMap.trace_eq_matrix_trace ℂ b _
  rw [htrace, Matrix.trace_eq_sum_roots_charpoly M]
  apply IsIntegral.multiset_sum
  intro r hr
  have hr_root : M.charpoly.IsRoot r :=
    (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hr
  have hρ_pow : (V.ρ g) ^ n = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have hMn : M ^ n = 1 := by
    rw [hM_def, LinearMap.toMatrix_pow, hρ_pow, LinearMap.toMatrix_one]
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℂ V) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : M.charpoly = 1 := by
      simp [Matrix.charpoly, Matrix.det_isEmpty]
    simp at hr
  have h_spec : r ∈ spectrum ℂ M :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hr_root
  have h_pow : r ^ n ∈ spectrum ℂ (M ^ n) :=
    spectrum.pow_mem_pow M n h_spec
  rw [hMn, spectrum.one_eq] at h_pow
  have hrn : r ^ n = 1 := Set.mem_singleton_iff.mp h_pow
  refine ⟨Polynomial.X ^ n - 1,
    Polynomial.monic_X_pow_sub_C 1 Fintype.card_pos.ne', ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_one, hrn, sub_self]

omit [Fintype G] [DecidableEq G] in
private lemma trivialRepresentation_character_eq_one (g : G) :
    (FDRep.of (Representation.trivial ℂ G ℂ)).character g = 1 := by
  change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) g) = 1
  simp [Representation.trivial]

set_option linter.unusedFintypeInType false in
omit [DecidableEq G] in
private lemma trivialRepresentation_simple :
    Simple (FDRep.of (Representation.trivial ℂ G ℂ)) := by
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  haveI : IsSimpleModule (MonoidAlgebra ℂ G)
      (Representation.trivial ℂ G ℂ).asModule := by
    rw [isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      ((Representation.trivial ℂ G ℂ).asModuleEquiv.finrank_eq.trans
        (Module.finrank_self ℂ))
  infer_instance

private lemma card_conjugacyClass_one :
    Fintype.card { h : G // IsConj (1 : G) h } = 1 := by
  have : Unique { h : G // IsConj (1 : G) h } := by
    refine ⟨⟨⟨1, IsConj.refl 1⟩⟩, ?_⟩
    rintro ⟨h, hh⟩
    simp only [Subtype.mk.injEq]
    rwa [isConj_one_right] at hh
  exact Fintype.card_unique

end RepresentationTheory.FiniteGroup.PrimePowerConjugacyClass.Auxiliary

open RepresentationTheory.FiniteGroup.PrimePowerConjugacyClass.Auxiliary

namespace RepresentationTheory.FiniteGroup.PrimePowerConjugacyClass

/-- A finite group element with conjugacy class of positive prime-power size admits a
nontrivial simple complex representation whose dimension is not divisible by that prime and
whose character does not vanish at the element. -/
@[source_ref"Chapter5/Lemma5.4.7"(role:=primary),
  source_ref"Chapter5/Discussion_proof_of_Theorem5.4.6"(role:=supporting)]
theorem exists_simple_representation_of_conj_class_card_prime_pow
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G) (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    ∃ V : FDRep ℂ G, Simple V ∧
      ¬ Nonempty (V ≅ FDRep.of (Representation.trivial ℂ G ℂ)) ∧
      ¬ (p ∣ Module.finrank ℂ V) ∧
      V.character g ≠ 0 := by
  have hg_ne : g ≠ 1 := by
    intro heq
    subst heq
    rw [card_conjugacyClass_one] at hconj
    have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
    omega
  haveI : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  haveI : NeZero (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    exact ⟨Nat.cast_ne_zero.mpr (Fintype.card_pos (α := G)).ne'⟩
  let D := DecompositionData.default (k := ℂ) (G := G)
  have hsum : ∑ i : Fin D.count,
      (D.dimension i : ℂ) * (D.representation i).character g = 0 := by
    have := sum_finrank_mul_character_eq_zero_of_ne_one D D.representation
      D.simple_representation D.representation_index_eq_of_iso g hg_ne
    simp_rw [D.finrank_representation] at this
    exact this
  obtain ⟨i₀, ⟨iso₀⟩⟩ :=
    D.exists_iso_representation_of_simple _ (trivialRepresentation_simple G)
  have hd_triv : D.dimension i₀ = 1 := by
    rw [← D.finrank_representation i₀]
    have := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv iso₀)
    simp [FDRep.of, Module.finrank_self] at this
    omega
  have hchar_triv : (D.representation i₀).character g = 1 := by
    have h := FDRep.char_iso iso₀
    rw [← congr_fun h g]
    exact trivialRepresentation_character_eq_one G g
  by_contra hcon
  rw [not_exists] at hcon
  have hcoprime_vanish : ∀ i : Fin D.count, i ≠ i₀ →
      ¬ (p ∣ D.dimension i) → (D.representation i).character g = 0 := by
    intro i hi hndvd
    haveI := D.simple_representation i
    by_contra hne
    refine hcon (D.representation i) ⟨D.simple_representation i, ?_, ?_, hne⟩
    · exact fun ⟨f⟩ => hi (D.representation_index_eq_of_iso i i₀ ⟨f ≪≫ iso₀⟩)
    · rwa [D.finrank_representation]
  have hterm_i₀ :
      (D.dimension i₀ : ℂ) * (D.representation i₀).character g = 1 := by
    rw [hd_triv, hchar_triv]
    simp
  have hrest_sum : ∑ i ∈ Finset.univ.erase i₀,
      (D.dimension i : ℂ) * (D.representation i).character g = -1 := by
    have h := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h
    rw [hterm_i₀] at h
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  have honly_dvd : ∑ i ∈ (Finset.univ.erase i₀).filter (fun i => p ∣ D.dimension i),
      (D.dimension i : ℂ) * (D.representation i).character g = -1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i₀)
      (fun i => p ∣ D.dimension i)
      (fun i => (D.dimension i : ℂ) * (D.representation i).character g)
    have hzero : ∑ i ∈ (Finset.univ.erase i₀).filter (fun i => ¬ (p ∣ D.dimension i)),
        (D.dimension i : ℂ) * (D.representation i).character g = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hcoprime_vanish i (Finset.ne_of_mem_erase hi.1) hi.2, mul_zero]
    rw [hzero, add_zero] at hsplit
    rw [hsplit]
    exact hrest_sum
  set S_set := (Finset.univ.erase i₀).filter (fun i => p ∣ D.dimension i)
  set S := ∑ i ∈ S_set,
    ((D.dimension i / p : ℕ) : ℂ) * (D.representation i).character g
  have hfactor : ∑ i ∈ S_set,
      (D.dimension i : ℂ) * (D.representation i).character g = (p : ℂ) * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    have : (D.dimension i : ℂ) =
        (p : ℂ) * ((D.dimension i / p : ℕ) : ℂ) := by
      have hdi : D.dimension i = p * (D.dimension i / p) :=
        Nat.eq_mul_of_div_eq_right hi.2 rfl
      exact_mod_cast hdi
    rw [this]
    ring
  have hpS : (p : ℂ) * S = -1 := by
    rw [← hfactor]
    exact honly_dvd
  have hS_int : IsIntegral ℤ S := IsIntegral.sum _ fun i _ =>
    (isIntegral_algebraMap (R := ℤ)).mul
      (characterValue_isIntegral G (D.representation i) g)
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hS_val : S = -(1 / (p : ℂ)) := by
    field_simp
    linear_combination hpS
  have h_rat_eq : algebraMap ℚ ℂ (-(1 / (p : ℚ))) = -(1 / (p : ℂ)) := by
    push_cast
    ring
  have h_integral : IsIntegral ℤ (algebraMap ℚ ℂ (-(1 / (p : ℚ)))) := by
    rw [h_rat_eq, ← hS_val]
    exact hS_int
  obtain ⟨n, hn⟩ :=
    (RepresentationTheory.NumberTheory.IntegralClosure.Rat.Rat.isIntegral_complex_iff _).mp
      h_integral
  have h1 : (n : ℚ) * p = -1 := by
    have hp_ne_q : (p : ℚ) ≠ 0 := by
      exact_mod_cast hp.ne_zero
    have := hn
    field_simp at this
    linarith
  have h2 : n * (p : ℤ) = -1 := by
    exact_mod_cast h1
  have h3 : (p : ℤ) ∣ 1 := ⟨-n, by linear_combination h2⟩
  have h4 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h3
  have h5 : 1 < (p : ℤ) := by
    exact_mod_cast hp.one_lt
  omega

end RepresentationTheory.FiniteGroup.PrimePowerConjugacyClass

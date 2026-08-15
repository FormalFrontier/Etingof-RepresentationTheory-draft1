/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.FDRep.Character

/-!
# Integrality of finite-group character values

This module proves that character values and normalized conjugacy-class character values of
finite-dimensional complex representations are algebraic integers, and deduces that the dimension
of a simple representation divides the order of the group.
-/

open Polynomial Matrix Module CategoryTheory

namespace RepresentationTheory.FiniteGroupCharacterIntegrality

/-- A complex number whose positive power equals one is integral over the integers. -/
theorem isIntegral_of_pow_eq_one {r : ℂ} {n : ℕ} (hn : 0 < n) (h : r ^ n = 1) :
    IsIntegral ℤ r := by
  refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 hn.ne', ?_⟩
  simp [h]

section

variable {G : Type*} [Group G] [Finite G]

/-- The character value of a finite-dimensional complex representation of a finite group is
integral over the integers. -/
theorem character_isIntegral (V : FDRep ℂ G) (g : G) : IsIntegral ℤ (V.character g) := by
  classical
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  set n := orderOf g with hn
  have hn0 : 0 < n := hfin.orderOf_pos
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hρ : (V.ρ g) ^ n = 1 := by rw [← map_pow, hgn, map_one]
  set d := finrank ℂ V with hd
  set b := Module.finBasis ℂ V with hb
  set A : Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix b b (V.ρ g) with hA
  have hAn : A ^ n = 1 := by
    rw [hA, LinearMap.toMatrix_pow, hρ, LinearMap.toMatrix_one]
  have htr : V.character g = A.trace := by
    rw [show V.character g = LinearMap.trace ℂ V (V.ρ g) from rfl,
      LinearMap.trace_eq_matrix_trace ℂ b (V.ρ g)]
  have hsum : V.character g = (A.charpoly.roots).sum := by
    rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  have hroot : ∀ r ∈ A.charpoly.roots, IsIntegral ℤ r := by
    intro r hr
    have hIsRoot : A.charpoly.IsRoot r := (Polynomial.mem_roots'.mp hr).2
    have hdet : (Matrix.scalar (Fin d) r - A).det = 0 := by
      rw [← Matrix.eval_charpoly]
      exact hIsRoot
    obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hscal : (Matrix.scalar (Fin d) r) *ᵥ v = r • v := by
      rw [Matrix.scalar_apply]
      funext x
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    have hev : A *ᵥ v = r • v := by
      have hsub : (Matrix.scalar (Fin d) r) *ᵥ v - A *ᵥ v = 0 := by
        rw [← Matrix.sub_mulVec]
        exact hMv
      rw [hscal] at hsub
      exact (sub_eq_zero.mp hsub).symm
    have hpow : ∀ k, (A ^ k) *ᵥ v = r ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, ih, smul_smul,
          ← pow_succ']
    have hrn : r ^ n = 1 := by
      have he := hpow n
      rw [hAn, Matrix.one_mulVec] at he
      have hz : (r ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← he, sub_self]
      rcases smul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv0
    exact isIntegral_of_pow_eq_one hn0 hrn
  rw [hsum]
  exact IsIntegral.multiset_sum hroot

/-- For a simple complex representation of a finite group, the conjugacy-class size times a
character value divided by the representation dimension is integral over the integers. -/
theorem conjugacyClassCard_mul_character_div_finrank_isIntegral
    (V : FDRep ℂ G) [Simple V] (g₀ : G) :
    IsIntegral ℤ
      ((Nat.card {x // IsConj g₀ x} : ℂ) * V.character g₀ / (finrank ℂ V : ℂ)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hpos : 0 < finrank ℂ V := by
    by_contra h
    have h0 : finrank ℂ V = 0 := by omega
    have hsub : Subsingleton (V : Type) := Module.finrank_zero_iff.mp h0
    have hsub2 : Subsingleton (V ⟶ V) :=
      ⟨fun f g => Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext fun x => hsub.elim _ _))⟩
    have hSS : finrank ℂ (V ⟶ V) = 1 := by rw [FDRep.finrank_hom_simple_simple]; simp
    have : finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
    omega
  haveI : Nontrivial (V : Type) := (finrank_pos_iff (R := ℂ)).mp hpos
  have hfr0 : (finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  set C : Finset G := Finset.univ.filter (fun x => IsConj g₀ x) with hC
  set z : MonoidAlgebra ℤ G := ∑ x ∈ C, MonoidAlgebra.single x 1 with hz
  set Φ : MonoidAlgebra ℤ G →ₐ[ℤ] Module.End ℂ (V : Type) :=
    MonoidAlgebra.lift ℤ (Module.End ℂ V) G V.ρ with hΦ
  have hΦz : Φ z = ∑ x ∈ C, V.ρ x := by
    rw [hz, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hΦ, MonoidAlgebra.lift_single, one_smul]
  have hcomm : ∀ g : G, V.ρ g * Φ z = Φ z * V.ρ g := by
    intro g
    rw [hΦz, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_nbij' (fun x => g * x * g⁻¹) (fun x => g⁻¹ * x * g) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.trans (isConj_iff.mpr ⟨g, rfl⟩)
    · intro a ha
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    · intro a _
      group
    · intro a _
      group
    · intro a _
      simp only [← MonoidHom.map_mul]
      congr 1
      group
  have hf : ∀ g : G, (Φ z) ∘ₗ V.ρ g = V.ρ g ∘ₗ (Φ z) := fun g => (hcomm g).symm
  let φ : V ⟶ V :=
    { hom := FGModuleCat.ofHom (Φ z)
      comm := fun g => by ext v; exact LinearMap.congr_fun (hf g) v }
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ φ
  have hΦz_scalar : Φ z = c • LinearMap.id := by
    have key : (FGModuleCat.ofHom (Φ z)).hom.hom = (c • 𝟙 V).hom.hom.hom :=
      congrArg (fun ψ : V ⟶ V => ψ.hom.hom.hom) hc.symm
    rw [show (FGModuleCat.ofHom (Φ z)).hom.hom = Φ z from rfl] at key
    rw [key, Action.smul_hom, Action.id_hom]
    rfl
  have htr : LinearMap.trace ℂ (V : Type) (Φ z) = (C.card : ℂ) * V.character g₀ := by
    rw [hΦz, map_sum]
    have hconst : ∀ x ∈ C, LinearMap.trace ℂ (V : Type) (V.ρ x) = V.character g₀ := by
      intro x hx
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h, rfl⟩ := isConj_iff.mp hx
      exact V.char_conj g₀ h
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have htr2 : LinearMap.trace ℂ (V : Type) (Φ z) = c * (finrank ℂ V : ℂ) := by
    rw [hΦz_scalar, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hcd : (C.card : ℂ) * V.character g₀ = c * (finrank ℂ V : ℂ) :=
    htr.symm.trans htr2
  have hcard : Nat.card {x // IsConj g₀ x} = C.card := by
    rw [Nat.card_eq_fintype_card, hC, Fintype.card_subtype]
  have hω :
      (Nat.card {x // IsConj g₀ x} : ℂ) * V.character g₀ / (finrank ℂ V : ℂ) = c := by
    rw [show ((Nat.card {x // IsConj g₀ x} : ℕ) : ℂ) = (C.card : ℂ) by rw [hcard]]
    rw [hcd, mul_div_assoc, div_self hfr0, mul_one]
  rw [hω]
  have hz_int : IsIntegral ℤ z := by
    haveI : Module.Finite ℤ (MonoidAlgebra ℤ G) :=
      Module.Finite.of_basis (MonoidAlgebra.basis G ℤ)
    exact IsIntegral.of_finite ℤ z
  have hΦz_int : IsIntegral ℤ (Φ z) := IsIntegral.map Φ hz_int
  rw [hΦz_scalar, ← Module.algebraMap_end_eq_smul_id] at hΦz_int
  have hinj : Function.Injective (algebraMap ℂ (Module.End ℂ (V : Type))) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hk := Module.ker_algebraMap_end ℂ (V : Type) r hr0
    rw [hr, LinearMap.ker_zero] at hk
    exact absurd hk top_ne_bot
  exact (isIntegral_algebraMap_iff hinj).mp hΦz_int

end

/-- The dimension of a simple complex representation of a finite group divides the order of the
group. -/
@[source_ref"Chapter2/Discussion_after_Theorem2.1.2/Derived4"(role:=primary)]
theorem finrank_dvd_card {G : Type*} [Group G] [Fintype G]
    (V : FDRep ℂ G) [Simple V] : Module.finrank ℂ V ∣ Fintype.card G := by
  classical
  haveI : Nonempty G := ⟨1⟩
  have hNne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  haveI hinv : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hNne
  set d : ℕ := Module.finrank ℂ V with hd_def
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      have hsub : Subsingleton V := Module.finrank_zero_iff.mp h0
      have hsub2 : Subsingleton (V ⟶ V) := by
        refine ⟨fun f g => ?_⟩
        exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
      have h1 : Module.finrank ℂ (V ⟶ V) = 1 := by
        rw [FDRep.finrank_hom_simple_simple]
        simp
      have h2 : Module.finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
      omega
    · exact h0
  have hdℂ : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hnorm : ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
    have hco :=
      RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple V V
    rw [if_pos ⟨Iso.refl V⟩] at hco
    have h2 : (Fintype.card G : ℂ) * (⅟(Fintype.card G : ℂ) •
        ∑ g : G, V.character g * V.character g⁻¹) = (Fintype.card G : ℂ) * (↑1 : ℂ) :=
      congrArg _ hco
    rw [smul_eq_mul, ← mul_assoc, mul_invOf_self, one_mul] at h2
    rw [h2]
    norm_num
  have hconj : ∀ {a b : G}, IsConj a b → V.character a = V.character b := by
    intro a b hab
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    rw [← hc]
    exact (FDRep.char_conj V a c).symm
  have hconj_inv : ∀ {a b : G}, IsConj a b → IsConj a⁻¹ b⁻¹ := by
    intro a b hab
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    exact isConj_iff.mpr ⟨c, by rw [← hc]; group⟩
  have hmaps : ∀ g ∈ (Finset.univ : Finset G),
      ConjClasses.mk g ∈ (Finset.univ : Finset (ConjClasses G)) :=
    fun g _ => Finset.mem_univ _
  have hreindex :
      ∑ g : G, V.character g * V.character g⁻¹ =
        ∑ C : ConjClasses G, ∑ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = C),
          V.character g * V.character g⁻¹ :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hinner : ∀ C : ConjClasses G,
      ∑ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = C),
        V.character g * V.character g⁻¹ =
          (Nat.card {x // IsConj (Quotient.out C) x} : ℂ) *
            (V.character (Quotient.out C) * V.character (Quotient.out C)⁻¹) := by
    intro C
    haveI : DecidablePred (fun g : G => IsConj (Quotient.out C) g) := Classical.decPred _
    have hmkout : ConjClasses.mk (Quotient.out C) = C := by
      rw [← ConjClasses.quotient_mk_eq_mk]
      exact Quotient.out_eq C
    have hmem : ∀ g : G, ConjClasses.mk g = C ↔ IsConj (Quotient.out C) g := by
      intro g
      constructor
      · intro hg
        rw [← hmkout, ConjClasses.mk_eq_mk_iff_isConj] at hg
        exact hg.symm
      · intro hg
        rw [← hmkout, ConjClasses.mk_eq_mk_iff_isConj]
        exact hg.symm
    have hconst : ∀ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = C),
        V.character g * V.character g⁻¹ =
          V.character (Quotient.out C) * V.character (Quotient.out C)⁻¹ := by
      intro g hg
      rw [Finset.mem_filter] at hg
      have hcg : IsConj (Quotient.out C) g := (hmem g).mp hg.2
      rw [← hconj hcg, ← hconj (hconj_inv hcg)]
    have hcard : (Finset.univ.filter (fun g => ConjClasses.mk g = C)).card =
        Nat.card {x // IsConj (Quotient.out C) x} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact congrArg Finset.card (Finset.filter_congr (fun g _ => hmem g))
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  have hclasssum : (Fintype.card G : ℂ) =
      ∑ C : ConjClasses G,
        (Nat.card {x // IsConj (Quotient.out C) x} : ℂ) *
          (V.character (Quotient.out C) * V.character (Quotient.out C)⁻¹) := by
    rw [← hnorm, hreindex]
    exact Finset.sum_congr rfl (fun C _ => hinner C)
  have hα_int : IsIntegral ℤ ((Fintype.card G : ℂ) / (d : ℂ)) := by
    rw [hclasssum, Finset.sum_div]
    apply IsIntegral.sum
    intro C _
    have hrw : (Nat.card {x // IsConj (Quotient.out C) x} : ℂ) *
          (V.character (Quotient.out C) * V.character (Quotient.out C)⁻¹) / (d : ℂ) =
        ((Nat.card {x // IsConj (Quotient.out C) x} : ℂ) * V.character (Quotient.out C) /
          (d : ℂ)) * V.character (Quotient.out C)⁻¹ := by
      rw [← mul_assoc, mul_div_right_comm]
    rw [hrw]
    exact (conjugacyClassCard_mul_character_div_finrank_isIntegral V (Quotient.out C)).mul
      (character_isIntegral V (Quotient.out C)⁻¹)
  have hqmap : (algebraMap ℚ ℂ) ((Fintype.card G : ℚ) / (d : ℚ)) =
      (Fintype.card G : ℂ) / (d : ℂ) := by
    rw [map_div₀, map_natCast, map_natCast]
  have hq_int : IsIntegral ℤ ((Fintype.card G : ℚ) / (d : ℚ)) := by
    have hinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
    apply (isIntegral_algebraMap_iff hinj).mp
    rw [hqmap]
    exact hα_int
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq_int
  have hdℚ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  rw [eq_div_iff hdℚ] at hn
  have hnn : (n : ℚ) * (d : ℚ) = (Fintype.card G : ℚ) := by
    simpa using hn
  have hZ : (n : ℤ) * (d : ℤ) = (Fintype.card G : ℤ) := by exact_mod_cast hnn
  have hdvd : (d : ℤ) ∣ (Fintype.card G : ℤ) := ⟨n, by rw [← hZ]; ring⟩
  exact Int.natCast_dvd_natCast.mp hdvd

end RepresentationTheory.FiniteGroupCharacterIntegrality

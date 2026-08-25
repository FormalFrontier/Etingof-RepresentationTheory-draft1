/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.NumberTheory.IntegralClosure.Rat
import RepresentationTheory.FiniteGroupCharacterArithmetic
import RepresentationTheory.Alignment.Attribute

/-! # Arithmetic of finite-group characters -/

namespace RepresentationTheory.FiniteGroup.CharacterArithmetic

open Finset

variable {G : Type*} [Group G]

/-- Raising elements of a group to an exponent coprime to its cardinality is bijective. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem pow_bijective_of_card_coprime {j : ℕ} (h : (Nat.card G).Coprime j) :
    Function.Bijective (fun g : G => g ^ j) :=
  Nat.Coprime.pow_left_bijective h

/-- For an exponent coprime to the group cardinality, an element has that power equal to one exactly when the element is one. -/
theorem pow_eq_one_iff_of_card_coprime {j : ℕ} (h : (Nat.card G).Coprime j) {g : G} :
    g ^ j = 1 ↔ g = 1 := by
  refine ⟨fun hg => (pow_bijective_of_card_coprime h).injective ?_, fun hg => by rw [hg, one_pow]⟩
  simpa using hg

/-- Composing a function with a coprime power map does not change its product over the nonidentity elements of a finite group. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem prod_nonidentity_comp_pow_eq {M : Type*} [CommMonoid M] [Fintype G] [DecidableEq G] {j : ℕ}
    (h : (Nat.card G).Coprime j) (f : G → M) :
    ∏ g ∈ univ.filter (· ≠ 1), f (g ^ j) = ∏ g ∈ univ.filter (· ≠ 1), f g := by
  refine Finset.prod_bij (fun g _ => g ^ j) ?_ ?_ ?_ ?_
  ·
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rwa [Ne, pow_eq_one_iff_of_card_coprime h]
  ·
    intro a₁ _ a₂ _ hab
    exact (pow_bijective_of_card_coprime h).injective hab
  ·
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    obtain ⟨a, ha⟩ := (pow_bijective_of_card_coprime h).surjective b
    refine ⟨a, ?_, ha⟩
    simp only [mem_filter, mem_univ, true_and]
    rintro rfl
    exact hb (by simpa using ha.symm)
  · intro a _; rfl

/-- A rational number whose complex image is integral over the integers cannot lie strictly between zero and one. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem rat_not_between_zero_one_of_complex_isIntegral {q : ℚ}
    (hint : IsIntegral ℤ (algebraMap ℚ ℂ q)) (h0 : 0 < q) (h1 : q < 1) : False := by
  obtain ⟨n, rfl⟩ := (RepresentationTheory.NumberTheory.IntegralClosure.Rat.Rat.isIntegral_complex_iff q).mp hint
  have hn0 : (0 : ℤ) < n := by exact_mod_cast h0
  have hn1 : n < 1 := by exact_mod_cast h1
  omega

open scoped ComplexConjugate

/-- Complex conjugation preserves integrality over the integers. -/
theorem isIntegral_star {z : ℂ} (hz : IsIntegral ℤ z) : IsIntegral ℤ (conj z) :=
  hz.map (Complex.conjAe.restrictScalars ℤ).toAlgHom

set_option linter.unusedFintypeInType false in

/-- The squared norm of every value of a finite group character is integral over the integers. -/
theorem character_normSq_isIntegral {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (g : G) :
    IsIntegral ℤ ((Complex.normSq (V.character g) : ℂ)) := by
  rw [← Complex.mul_conj]
  exact (RepresentationTheory.FiniteGroupCharacterArithmetic.character_isIntegral V g).mul (isIntegral_star (RepresentationTheory.FiniteGroupCharacterArithmetic.character_isIntegral V g))

set_option linter.unusedFintypeInType false in

/-- A finite product of squared norms of character values is integral over the integers. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem character_normSq_product_isIntegral {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (s : Finset G) :
    IsIntegral ℤ (∏ g ∈ s, (Complex.normSq (V.character g) : ℂ)) := by
  have h : (∏ g ∈ s, (Complex.normSq (V.character g) : ℂ)) ∈ integralClosure ℤ ℂ :=
    prod_mem (fun g _ => character_normSq_isIntegral V g)
  exact h

set_option linter.unusedFintypeInType false in

/-- A finite group character value is a sum of complex roots whose orders divide the group cardinality. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem character_eq_sum_of_card_roots {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (g : G) :
    ∃ s : Multiset ℂ, (∀ μ ∈ s, μ ^ Nat.card G = 1) ∧ V.character g = s.sum := by
  set f := V.ρ g with hf_def

  have hf_pow : f ^ orderOf g = 1 := by
    rw [hf_def, ← map_pow, pow_orderOf_eq_one, map_one]
  have hne : LinearMap.charpoly f ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
  refine ⟨(LinearMap.charpoly f).roots, ?_, ?_⟩
  ·

    intro μ hμ
    rw [Polynomial.mem_roots hne] at hμ
    have heig : Module.End.HasEigenvalue f μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hμ
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hpow_v : ∀ k : ℕ, (f ^ k) v = (μ ^ k) • v := by
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hv.apply_eq_smul,
          map_smul, ih, smul_smul, ← pow_succ']
    have h1 : v = (μ ^ orderOf g) • v := by rw [← hpow_v, hf_pow]; simp
    have h2 : (μ ^ orderOf g - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    have hμord : μ ^ orderOf g = 1 := by
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 hv.2
    obtain ⟨k, hk⟩ := orderOf_dvd_card (x := g)
    rw [Nat.card_eq_fintype_card, hk, pow_mul, hμord, one_pow]
  ·
    change LinearMap.trace ℂ V f = _
    set b := Module.finBasis ℂ V
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    have h1 : (LinearMap.toMatrix b b f).trace =
        (LinearMap.toMatrix b b f).charpoly.roots.sum :=
      Matrix.trace_eq_sum_roots_charpoly _
    simpa only [LinearMap.charpoly_toMatrix] using h1

/-- Every natural power of an endomorphism acts on a vector in an eigenspace by the corresponding power of the eigenvalue. -/
theorem apply_pow_eq_smul_pow_of_mem_eigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (μ : ℂ) {x : V} (hx : x ∈ Module.End.eigenspace f μ) (m : ℕ) :
    (f ^ m) x = μ ^ m • x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul,
        (Module.End.mem_eigenspace_iff.mp hx), smul_smul, ← pow_succ]

/-- Every eigenvalue of an endomorphism whose given power is the identity has that same power equal to one. -/
theorem eigenvalue_pow_eq_one_of_end_pow_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) {N : ℕ} (hf : f ^ N = 1) {μ : ℂ}
    (hμ : Module.End.eigenspace f μ ≠ ⊥) : μ ^ N = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hμ
  have hpow := apply_pow_eq_smul_pow_of_mem_eigenspace f μ hv N
  rw [hf, Module.End.one_apply] at hpow
  have hz : (μ ^ N - 1) • v = 0 := by rw [sub_smul, one_smul, ← hpow, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv0

open Polynomial in

/-- For a finite-dimensional endomorphism of finite order, the trace of each power is the sum of eigenvalue powers weighted by eigenspace dimensions. -/
theorem trace_pow_eq_sum_eigenvalue_pow_of_end_pow_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) {N : ℕ} (hN : 0 < N)
    (hf : f ^ N = 1) (k : ℕ)
    (hfin : {μ : ℂ | Module.End.eigenspace f μ ≠ ⊥}.Finite) :
    LinearMap.trace ℂ V (f ^ k) =
      ∑ μ ∈ hfin.toFinset, (Module.finrank ℂ (Module.End.eigenspace f μ) : ℂ) * μ ^ k := by

  have hsep : (X ^ N - 1 : ℂ[X]).Separable :=
    Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hN.ne')
  have haeval : (aeval f) (X ^ N - 1 : ℂ[X]) = 0 := by simp [map_sub, hf]
  have hss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval

  have hInternal : DirectSum.IsInternal (Module.End.eigenspace f) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨f.eigenspaces_iSupIndep, hss.iSup_eigenspace_eq_top⟩

  have hmaps : ∀ μ : ℂ, Set.MapsTo (f ^ k)
      (Module.End.eigenspace f μ) (Module.End.eigenspace f μ) := by
    intro μ x hx
    rw [apply_pow_eq_smul_pow_of_mem_eigenspace f μ hx k]
    exact (Module.End.eigenspace f μ).smul_mem _ hx
  classical
  rw [LinearMap.trace_eq_sum_trace_restrict' hInternal hfin hmaps]
  apply Finset.sum_congr rfl
  intro μ _

  have hrestrict : (f ^ k).restrict (hmaps μ) = (μ ^ k) • LinearMap.id := by
    ext x
    simp only [LinearMap.coe_restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.coe_smul]
    exact apply_pow_eq_smul_pow_of_mem_eigenspace f μ x.2 k
  rw [hrestrict, LinearMap.map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

set_option linter.unusedFintypeInType false in

/-- A complex ring endomorphism that acts as a fixed power on the relevant roots sends character values to values on the corresponding group powers. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem map_character_eq_character_pow {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (g : G) {j : ℕ} (σ : ℂ →+* ℂ)
    (hσ : ∀ μ : ℂ, μ ^ Nat.card G = 1 → σ μ = μ ^ j) :
    σ (V.character g) = V.character (g ^ j) := by
  classical
  set f := V.ρ g with hf_def
  have hN : 0 < Nat.card G := Nat.card_pos
  have hf : f ^ Nat.card G = 1 := by
    rw [hf_def, ← map_pow, Nat.card_eq_fintype_card, pow_card_eq_one, map_one]
  have hfin : {μ : ℂ | Module.End.eigenspace f μ ≠ ⊥}.Finite :=
    Module.End.finite_hasEigenvalue f
  have e1 := trace_pow_eq_sum_eigenvalue_pow_of_end_pow_eq_one f hN hf 1 hfin
  have ej := trace_pow_eq_sum_eigenvalue_pow_of_end_pow_eq_one f hN hf j hfin
  simp only [pow_one] at e1
  have hchar_g : V.character g = LinearMap.trace ℂ V f := rfl
  have hchar_gj : V.character (g ^ j) = LinearMap.trace ℂ V (f ^ j) := by
    rw [hf_def, ← map_pow]; rfl
  rw [hchar_g, hchar_gj, e1, ej, map_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  have hμmem : Module.End.eigenspace f μ ≠ ⊥ := (Set.Finite.mem_toFinset hfin).mp hμ
  rw [map_mul, map_natCast, hσ μ (eigenvalue_pow_eq_one_of_end_pow_eq_one f hf hμmem)]

/-- A ring endomorphism acting as a coprime power on the relevant roots fixes the character pairing product over nonidentity elements. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem map_character_pairing_product_eq_of_card_coprime {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) {j : ℕ} (hj : (Nat.card G).Coprime j) (σ : ℂ →+* ℂ)
    (hσ : ∀ μ : ℂ, μ ^ Nat.card G = 1 → σ μ = μ ^ j) :
    σ (∏ g ∈ univ.filter (· ≠ 1), V.character g * V.character g⁻¹)
      = ∏ g ∈ univ.filter (· ≠ 1), V.character g * V.character g⁻¹ := by
  rw [map_prod]
  have step : ∀ g : G, σ (V.character g * V.character g⁻¹)
      = V.character (g ^ j) * V.character (g ^ j)⁻¹ := by
    intro g
    rw [map_mul, map_character_eq_character_pow V g σ hσ, map_character_eq_character_pow V g⁻¹ σ hσ, inv_pow]
  simp_rw [step]
  exact prod_nonidentity_comp_pow_eq hj (fun g => V.character g * V.character g⁻¹)

set_option linter.unusedFintypeInType false in

/-- The product of character values over nonidentity elements, paired with their inverses, is rational. -/
@[source_ref "Chapter5/Remark5.2.8" (role := supporting)]
theorem character_pairing_product_is_rat {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) :
    ∃ q : ℚ, algebraMap ℚ ℂ q =
      ∏ g ∈ univ.filter (· ≠ 1), V.character g * V.character g⁻¹ := by
  classical
  set N := Nat.card G with hN_def
  have hNpos : 0 < N := Nat.card_pos
  haveI : NeZero N := ⟨hNpos.ne'⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / N), Complex.isPrimitiveRoot_exp N hNpos.ne'⟩
  set K := IntermediateField.adjoin ℚ ({ζ} : Set ℂ) with hK_def
  have hζK_mem : ζ ∈ K := IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)

  have halg : IsAlgebraic ℚ ζ := by
    have hmonic : (Polynomial.X ^ N - Polynomial.C (1 : ℚ)).Monic :=
      Polynomial.monic_X_pow_sub_C 1 hNpos.ne'
    refine ⟨Polynomial.X ^ N - 1, ?_, ?_⟩
    · have hCe : (Polynomial.X ^ N - Polynomial.C (1 : ℚ)) = Polynomial.X ^ N - 1 := by simp
      rw [← hCe]; exact hmonic.ne_zero
    · simp [hζ.pow_eq_one]
  haveI hcyc : IsCyclotomicExtension {N} ℚ K := by
    change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois (S := ({N} : Set ℕ)) (K := ℚ) (L := K)
  haveI : FiniteDimensional ℚ K :=
    IsCyclotomicExtension.finiteDimensional (S := ({N} : Set ℕ)) (K := ℚ) K

  set ζK : K := ⟨ζ, hζK_mem⟩ with hζK_def
  have hmapζK : algebraMap K ℂ ζK = ζ := rfl
  have hζK : IsPrimitiveRoot ζK N :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap K ℂ)
      (by rw [hmapζK]; exact hζ) (algebraMap K ℂ).injective

  have hrootK : ∀ μ : ℂ, μ ^ N = 1 → μ ∈ K := by
    intro μ hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    exact pow_mem hζK_mem i

  have hmem : ∀ g : G, ∃ x : K,
      algebraMap K ℂ x = V.character g ∧
      ∀ (j : ℕ) (φ : K ≃ₐ[ℚ] K), (∀ w : K, w ^ N = 1 → φ w = w ^ j) →
        algebraMap K ℂ (φ x) = V.character (g ^ j) := by
    intro g
    set f := V.ρ g with hf_def
    have hf : f ^ N = 1 := by
      rw [hf_def, ← map_pow, hN_def, Nat.card_eq_fintype_card, pow_card_eq_one, map_one]
    have hfin : {μ : ℂ | Module.End.eigenspace f μ ≠ ⊥}.Finite :=
      Module.End.finite_hasEigenvalue f
    set S := hfin.toFinset with hS_def
    set d : ℂ → ℕ := fun μ => Module.finrank ℂ (Module.End.eigenspace f μ) with hd_def
    have hSpow : ∀ μ ∈ S, μ ^ N = 1 := by
      intro μ hμ
      exact eigenvalue_pow_eq_one_of_end_pow_eq_one f hf ((Set.Finite.mem_toFinset hfin).mp hμ)
    have hmemμ : ∀ μ ∈ S, μ ∈ K := fun μ hμ => hrootK μ (hSpow μ hμ)
    have e1 : V.character g = ∑ μ ∈ S, (d μ : ℂ) * μ := by
      have hchar_g : V.character g = LinearMap.trace ℂ V f := rfl
      rw [hchar_g]
      simpa using trace_pow_eq_sum_eigenvalue_pow_of_end_pow_eq_one f hNpos hf 1 hfin
    have ej : ∀ j : ℕ, V.character (g ^ j) = ∑ μ ∈ S, (d μ : ℂ) * μ ^ j := by
      intro j
      have htr : V.character (g ^ j) = LinearMap.trace ℂ V (f ^ j) := by
        rw [hf_def, ← map_pow]; rfl
      rw [htr, trace_pow_eq_sum_eigenvalue_pow_of_end_pow_eq_one f hNpos hf j hfin]
    refine ⟨∑ μ ∈ S.attach, (d μ.1 : K) * ⟨μ.1, hmemμ μ.1 μ.2⟩, ?_, ?_⟩
    ·
      rw [map_sum]
      have hterm : ∀ μ : S, algebraMap K ℂ ((d μ.1 : K) * ⟨μ.1, hmemμ μ.1 μ.2⟩)
          = (d μ.1 : ℂ) * μ.1 := by
        intro μ; rw [map_mul, map_natCast]; rfl
      rw [Finset.sum_congr rfl (fun μ _ => hterm μ), Finset.sum_attach S (fun μ => (d μ : ℂ) * μ),
        ← e1]
    ·
      intro j φ hφ
      rw [map_sum, map_sum, ej j]
      have hterm : ∀ μ : S, algebraMap K ℂ (φ ((d μ.1 : K) * ⟨μ.1, hmemμ μ.1 μ.2⟩))
          = (d μ.1 : ℂ) * μ.1 ^ j := by
        intro μ
        have hwN : (⟨μ.1, hmemμ μ.1 μ.2⟩ : K) ^ N = 1 := by
          apply (algebraMap K ℂ).injective
          rw [map_pow, map_one]; exact hSpow μ.1 μ.2
        rw [map_mul, map_natCast, hφ _ hwN, map_mul, map_natCast, map_pow]; rfl
      rw [Finset.sum_congr rfl (fun μ _ => hterm μ),
        Finset.sum_attach S (fun μ => (d μ : ℂ) * μ ^ j)]
  choose x hx1 hx2 using hmem

  set βK : K := ∏ g ∈ univ.filter (· ≠ 1), x g * x g⁻¹ with hβK_def
  have hβ : algebraMap K ℂ βK
      = ∏ g ∈ univ.filter (· ≠ 1), V.character g * V.character g⁻¹ := by
    rw [hβK_def, map_prod]
    exact Finset.prod_congr rfl (fun g _ => by rw [map_mul, hx1, hx1])

  have hfix : ∀ φ : K ≃ₐ[ℚ] K, φ βK = βK := by
    intro φ
    set j := (hζK.autToPow ℚ φ : ZMod N).val with hj_def
    have hjcop : N.Coprime j := (ZMod.val_coe_unit_coprime (hζK.autToPow ℚ φ)).symm
    have hφpow : ∀ w : K, w ^ N = 1 → φ w = w ^ j := by
      intro w hw
      obtain ⟨m, -, rfl⟩ := hζK.eq_pow_of_pow_eq_one hw
      have hζj : φ ζK = ζK ^ j := (hζK.autToPow_spec ℚ φ).symm
      rw [map_pow, hζj, ← pow_mul, ← pow_mul, Nat.mul_comm]
    have hstep : ∀ g : G, φ (x g * x g⁻¹) = (fun g => x g * x g⁻¹) (g ^ j) := by
      intro g
      have h1 : φ (x g) = x (g ^ j) :=
        (algebraMap K ℂ).injective (by rw [hx2 g j φ hφpow, hx1])
      have h2 : φ (x g⁻¹) = x ((g ^ j)⁻¹) :=
        (algebraMap K ℂ).injective (by rw [hx2 g⁻¹ j φ hφpow, hx1, inv_pow])
      simp only [map_mul, h1, h2]
    rw [hβK_def, map_prod, Finset.prod_congr rfl (fun g _ => hstep g),
      prod_nonidentity_comp_pow_eq hjcop (fun g => x g * x g⁻¹)]

  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed βK).mpr hfix
  exact ⟨q, by rw [← hβ, ← hq, IsScalarTower.algebraMap_apply ℚ K ℂ q]⟩

set_option linter.unusedFintypeInType false in

/-- The product of character values paired with inverse group elements cannot be a rational number strictly between zero and one. -/
@[source_ref "Chapter5/Remark5.2.8" (role := primary)]
theorem character_pairing_product_not_rat_between_zero_one {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) {q : ℚ}
    (hq : algebraMap ℚ ℂ q =
      ∏ g ∈ univ.filter (· ≠ 1), V.character g * V.character g⁻¹)
    (h0 : 0 < q) (h1 : q < 1) : False := by
  refine rat_not_between_zero_one_of_complex_isIntegral ?_ h0 h1
  have hmem : (∏ g ∈ univ.filter (· ≠ 1), V.character g * V.character g⁻¹)
      ∈ integralClosure ℤ ℂ :=
    prod_mem fun g _ =>
      mul_mem (RepresentationTheory.FiniteGroupCharacterArithmetic.character_isIntegral V g) (RepresentationTheory.FiniteGroupCharacterArithmetic.character_isIntegral V g⁻¹)
  rw [hq]; exact hmem

end RepresentationTheory.FiniteGroup.CharacterArithmetic

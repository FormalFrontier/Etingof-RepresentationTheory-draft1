/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.FDRep.RegularRepresentationCharacter
import RepresentationTheory.FiniteGroupCharacterCoprimality
import RepresentationTheory.NumberTheory.IntegralClosure.Rat
import RepresentationTheory.Alignment.Attribute

open Representation CategoryTheory Finset
open RepresentationTheory.FDRep.GroupAlgebraDecomposition
open RepresentationTheory.FDRep.RegularRepresentationCharacter
open RepresentationTheory.FiniteGroupCharacterCoprimality

namespace RepresentationTheory.FiniteGroupNormalSubgroups

section Helpers

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
    refine is_simple_module_of_finrank_eq_one (K := ℂ) (A := MonoidAlgebra ℂ G)
      (V := (Representation.trivial ℂ G ℂ).asModule) ?_
    rw [(Representation.trivial ℂ G ℂ).asModuleEquiv.finrank_eq,
      Module.finrank_self]
  infer_instance

omit [Fintype G] [DecidableEq G] in
private lemma finrank_eq_one_of_all_action_scalar
    (V : FDRep ℂ G) [Representation.IsIrreducible V.ρ]
    (hall : ∀ h : G, ∃ d : ℂ, V.ρ h = d • LinearMap.id) :
    Module.finrank ℂ V = 1 := by
  have hnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation V.ρ)
      (Subrepresentation.toSubmodule_injective (by
        ext x
        simp [Subsingleton.elim x 0]))
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hspan_inv : ∀ (g : G) {w : V},
      w ∈ Submodule.span ℂ {v} → V.ρ g w ∈ Submodule.span ℂ {v} := by
    intro g w hw
    obtain ⟨d, hd⟩ := hall g
    rw [Submodule.mem_span_singleton] at hw ⊢
    obtain ⟨a, rfl⟩ := hw
    exact ⟨d * a, by rw [hd]; simp [smul_smul, mul_comm d a]⟩
  let σ : Subrepresentation V.ρ := ⟨Submodule.span ℂ {v}, hspan_inv⟩
  have hne_bot : σ ≠ ⊥ := by
    intro h
    have : v ∈ (⊥ : Subrepresentation V.ρ) :=
      h ▸ Submodule.subset_span (Set.mem_singleton v)
    exact hv (Submodule.mem_bot ℂ |>.mp this)
  have htop : σ = ⊤ := (eq_bot_or_eq_top σ).resolve_left hne_bot
  exact (finrank_eq_one_iff_of_nonzero v hv).mpr
    (congr_arg Subrepresentation.toSubmodule htop)

omit [Fintype G] [DecidableEq G] in
private lemma scalar_action_contradicts_simplicity [IsSimpleGroup G]
    (V : FDRep ℂ G) [Representation.IsIrreducible V.ρ]
    (hdim : 2 ≤ Module.finrank ℂ V)
    (g : G) (hg : g ≠ 1) (c : ℂ) (hsc : V.ρ g = c • LinearMap.id) :
    False := by
  rcases (MonoidHom.normal_ker V.ρ).eq_bot_or_eq_top with hbot | htop
  · have hinj : Function.Injective V.ρ := (MonoidHom.ker_eq_bot_iff V.ρ).mp hbot
    have hg_center : g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply hinj
      simp only [map_mul, hsc]
      ext
      simp
    have hcenter_ne_bot : Subgroup.center G ≠ ⊥ := by
      intro h
      exact hg (Subgroup.mem_bot.mp (h ▸ hg_center))
    have hcenter_top : Subgroup.center G = ⊤ :=
      (Subgroup.Normal.eq_bot_or_eq_top Subgroup.instNormalCenter).resolve_left
        hcenter_ne_bot
    haveI : IsMulCommutative G := ⟨⟨fun a b =>
      ((Subgroup.mem_center_iff.mp (hcenter_top ▸ Subgroup.mem_top a)) b).symm⟩⟩
    exact absurd (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative V.ρ)
      (by omega)
  · have hall : ∀ h : G, ∃ d : ℂ, V.ρ h = d • LinearMap.id := by
      intro h
      have hker : V.ρ h = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top h)
      exact ⟨1, by rw [one_smul]; exact hker⟩
    exact absurd (finrank_eq_one_of_all_action_scalar G V hall) (by omega)

omit [Fintype G] [DecidableEq G] in
private lemma exists_iso_trivialRepresentation_of_ker_eq_top
    (V : FDRep ℂ G) (hker : MonoidHom.ker V.ρ = ⊤)
    (hd : Module.finrank ℂ V = 1) :
    Nonempty (V ≅ FDRep.of (Representation.trivial ℂ G ℂ)) := by
  have hρ_triv : ∀ g : G, V.ρ g = LinearMap.id := fun g =>
    MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g)
  let e := LinearEquiv.ofFinrankEq V ℂ (by rw [hd, Module.finrank_self])
  exact ⟨Action.mkIso e.toFGModuleCatIso (fun g => by
    ext x
    simp [FDRep.hom_hom_action_ρ, hρ_triv g, Representation.trivial])⟩

omit [Fintype G] [DecidableEq G] in
private lemma finrank_ge_two_of_nontrivial_irreducible [IsSimpleGroup G]
    (V : FDRep ℂ G) [Representation.IsIrreducible V.ρ]
    (hntv : ¬ Nonempty (V ≅ FDRep.of (Representation.trivial ℂ G ℂ)))
    (hnoncomm : ¬ IsMulCommutative G) :
    2 ≤ Module.finrank ℂ V := by
  by_contra h
  push Not at h
  have hnt : Nontrivial V := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation V.ρ)
      (Subrepresentation.toSubmodule_injective (by
        ext x
        simp [Subsingleton.elim x 0]))
  have hd1 : Module.finrank ℂ V = 1 := by
    have := Module.finrank_pos (R := ℂ) (M := V)
    omega
  have hall : ∀ g : G,
      V.ρ g = ((V.ρ g).existsUnique_eq_smul_id_of_finrank_eq_one hd1).choose •
        LinearMap.id :=
    fun g => ((V.ρ g).existsUnique_eq_smul_id_of_finrank_eq_one hd1).choose_spec.1
  have hcomm : ∀ g h : G, V.ρ (g * h) = V.ρ (h * g) := by
    intro g h
    rw [map_mul, map_mul, hall g, hall h]
    ext
    simp [smul_smul, mul_comm]
  rcases (MonoidHom.normal_ker V.ρ).eq_bot_or_eq_top with hbot | htop
  · have hinj := (MonoidHom.ker_eq_bot_iff V.ρ).mp hbot
    exact hnoncomm ⟨⟨fun a b => hinj (hcomm a b)⟩⟩
  · exact hntv (exists_iso_trivialRepresentation_of_ker_eq_top G V htop hd1)

end Helpers

private lemma card_conjugacyClass_one
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Fintype.card { h : G // IsConj (1 : G) h } = 1 := by
  have : Unique { h : G // IsConj (1 : G) h } := by
    refine ⟨⟨⟨1, IsConj.refl 1⟩⟩, ?_⟩
    rintro ⟨h, hh⟩
    simp only [Subtype.mk.injEq]
    rwa [isConj_one_right] at hh
  exact Fintype.card_unique

private lemma IsSimpleGroup.no_prime_power_conjugacyClass
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    [IsSimpleGroup G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G) (hg_ne : g ≠ 1)
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    False := by
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
  have hcoprime_vanish : ∀ i : Fin D.count, i ≠ i₀ →
      ¬ (p ∣ D.dimension i) → (D.representation i).character g = 0 := by
    intro i hi hndvd
    haveI := D.simple_representation i
    have hcop : Nat.Coprime (Fintype.card { h : G // IsConj g h })
        (Module.finrank ℂ (D.representation i)) := by
      rw [hconj, D.finrank_representation]
      exact Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hndvd)
    rcases
        character_eq_zero_or_action_eq_smul_id_of_conjClassCard_coprime_finrank
          G (D.representation i) g hcop with hzero | ⟨c, hsc⟩
    · exact hzero
    · exfalso
      haveI : Representation.IsIrreducible (D.representation i).ρ :=
        (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
          (D.isSimpleModule_coordinateRepresentation i)
      have hntv :
          ¬ Nonempty (D.representation i ≅
            FDRep.of (Representation.trivial ℂ G ℂ)) :=
        fun ⟨f⟩ => hi (D.representation_index_eq_of_iso i i₀ ⟨f ≪≫ iso₀⟩)
      have hnoncomm : ¬ IsMulCommutative G := by
        intro ⟨⟨hc⟩⟩
        have hcard1 : Fintype.card { h : G // IsConj g h } = 1 := by
          have : Unique { h : G // IsConj g h } := by
            refine ⟨⟨⟨g, IsConj.refl g⟩⟩, ?_⟩
            rintro ⟨h, hh⟩
            simp only [Subtype.mk.injEq]
            obtain ⟨u, hu⟩ := isConj_iff.mp hh
            rw [hc u g, mul_inv_cancel_right] at hu
            exact hu.symm
          exact Fintype.card_unique
        rw [hconj] at hcard1
        have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
        omega
      exact scalar_action_contradicts_simplicity G (D.representation i)
        (finrank_ge_two_of_nontrivial_irreducible G (D.representation i) hntv hnoncomm)
        g hg_ne c hsc
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

/-- A finite group with a conjugacy class of positive prime-power size has a nontrivial proper
normal subgroup. -/
@[source_ref"Chapter5/Theorem5.4.6"(role:=primary),
  source_ref"Chapter5/Discussion_proof_of_Theorem5.4.6"(role:=supporting),
  source_ref"Chapter5/Discussion_proof_of_Theorem5.4.3"(role:=supporting)]
theorem exists_nontrivial_proper_normalSubgroup_of_conjClassCard_eq_prime_pow
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (g : G)
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  have hg_ne : g ≠ 1 := by
    intro heq
    subst heq
    rw [card_conjugacyClass_one] at hconj
    have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
    omega
  by_contra habs
  push Not at habs
  haveI : Nontrivial G := ⟨⟨g, 1, hg_ne⟩⟩
  haveI : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun H hH => by
        by_cases h : H = ⊥
        · exact Or.inl h
        · exact Or.inr (habs H hH h) }
  exact IsSimpleGroup.no_prime_power_conjugacyClass G p hp k hk g hg_ne hconj

end RepresentationTheory.FiniteGroupNormalSubgroups

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations

import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.AuxiliaryFiniteSetMembership

open RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations

private lemma decomp_all_pairwise_compl {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hA₁ : LinearMap.ker ρ.leafOneToCenter = ⊥) (hA₂ : LinearMap.ker ρ.leafTwoToCenter =
      ⊥)
    (hA₃ : LinearMap.ker ρ.leafThreeToCenter = ⊥)
    (hR : LinearMap.range ρ.leafOneToCenter ⊔ LinearMap.range ρ.leafTwoToCenter ⊔
      LinearMap.range ρ.leafThreeToCenter = ⊤)
    (hV : Module.finrank k ρ.center ≥ 3)
    (h₁₂ : LinearMap.range ρ.leafOneToCenter ⊓ LinearMap.range ρ.leafTwoToCenter = ⊥)
    (h₁₃ : LinearMap.range ρ.leafOneToCenter ⊓ LinearMap.range ρ.leafThreeToCenter = ⊥)
    (h₂₃ : LinearMap.range ρ.leafTwoToCenter ⊓ LinearMap.range ρ.leafThreeToCenter = ⊥)
    (hR1_le : LinearMap.range ρ.leafOneToCenter ≤ LinearMap.range ρ.leafTwoToCenter ⊔
      LinearMap.range ρ.leafThreeToCenter)
    (hR2_le : LinearMap.range ρ.leafTwoToCenter ≤ LinearMap.range ρ.leafOneToCenter ⊔
      LinearMap.range ρ.leafThreeToCenter)
    (hR3_le : LinearMap.range ρ.leafThreeToCenter ≤ LinearMap.range ρ.leafOneToCenter ⊔
      LinearMap.range ρ.leafTwoToCenter) :
    False := by
  set R₁ := LinearMap.range ρ.leafOneToCenter
  set R₂ := LinearMap.range ρ.leafTwoToCenter
  set R₃ := LinearMap.range ρ.leafThreeToCenter
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  have h12_top : R₁ ⊔ R₂ = ⊤ :=
    eq_top_iff.mpr (hR ▸ sup_le le_rfl (hR3_le.trans le_rfl))
  have hc12 : IsCompl R₁ R₂ := IsCompl.of_eq (disjoint_iff.mp (disjoint_iff.mpr h₁₂))
    h12_top
  have h13_top : R₁ ⊔ R₃ = ⊤ := by
    have h1 : R₁ ⊔ R₂ ≤ R₁ ⊔ R₃ := sup_le le_sup_left hR2_le
    exact eq_top_iff.mpr (hR ▸ (sup_le_sup_right h1 _).trans
      (by rw [sup_assoc, sup_idem] : (R₁ ⊔ R₃) ⊔ R₃ ≤ R₁ ⊔ R₃))
  have hc13 : IsCompl R₁ R₃ :=
    IsCompl.of_eq (disjoint_iff.mp (disjoint_iff.mpr h₁₃)) h13_top
  have h23_top : R₂ ⊔ R₃ = ⊤ := by
    have h1 : R₁ ⊔ R₂ ≤ R₂ ⊔ R₃ := sup_le hR1_le le_sup_left
    exact eq_top_iff.mpr (hR ▸ (sup_le_sup_right h1 _).trans
      (by rw [sup_assoc, sup_idem] : (R₂ ⊔ R₃) ⊔ R₃ ≤ R₂ ⊔ R₃))
  have hc23 : IsCompl R₂ R₃ :=
    IsCompl.of_eq (disjoint_iff.mp (disjoint_iff.mpr h₂₃)) h23_top
  have hdim12 := Submodule.finrank_add_eq_of_isCompl hc12
  have hdim13 := Submodule.finrank_add_eq_of_isCompl hc13
  have hdim23 := Submodule.finrank_add_eq_of_isCompl hc23
  have hfr₁ := LinearMap.finrank_range_of_inj hinj₁
  have hfr₂ := LinearMap.finrank_range_of_inj hinj₂
  have hfr₃ := LinearMap.finrank_range_of_inj hinj₃
  have hn_ge : Module.finrank k ↥R₁ ≥ 2 := by omega
  let π₁ := Submodule.projectionOnto R₁ R₂ hc12
  let π₂ := Submodule.projectionOnto R₂ R₁ hc12.symm
  have decomp_v : ∀ v : ρ.center,
      v = R₁.subtype (π₁ v) + R₂.subtype (π₂ v) :=
    fun v => (Submodule.projection_add_projection_eq_self hc12 v).symm
  have π₁_on_R₁ : ∀ (v : ↥R₁), π₁ (R₁.subtype v) = v :=
    Submodule.projectionOnto_apply_left hc12
  have π₂_on_R₁ : ∀ (v : ↥R₁), π₂ (R₁.subtype v) = 0 := fun v => by
    have : R₁.subtype v ∈ LinearMap.ker π₂ := by
      rw [Submodule.ker_projectionOnto hc12.symm]; exact v.2
    exact LinearMap.mem_ker.mp this
  have π₁_on_R₂ : ∀ (v : ↥R₂), π₁ (R₂.subtype v) = 0 := fun v => by
    have : R₂.subtype v ∈ LinearMap.ker π₁ := by
      rw [Submodule.ker_projectionOnto hc12]; exact v.2
    exact LinearMap.mem_ker.mp this
  have π₂_on_R₂ : ∀ (v : ↥R₂), π₂ (R₂.subtype v) = v :=
    Submodule.projectionOnto_apply_left hc12.symm
  have hπ₁ι₃_inj : Function.Injective (π₁.comp R₃.subtype) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    ext
    have h_diff_R3 : a - b ∈ R₃ := R₃.sub_mem ha hb
    have h_ker : a - b ∈ LinearMap.ker π₁ := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact heq
    rw [Submodule.ker_projectionOnto hc12] at h_ker
    have : a - b ∈ R₂ ⊓ R₃ := ⟨h_ker, h_diff_R3⟩
    rw [h₂₃] at this; exact sub_eq_zero.mp ((Submodule.mem_bot k).mp this)
  have hdim_eq3_1 : Module.finrank k ↥R₃ = Module.finrank k ↥R₁ := by omega
  let e₁ : ↥R₃ ≃ₗ[k] ↥R₁ := LinearEquiv.ofInjectiveOfFinrankEq
    (π₁.comp R₃.subtype) hπ₁ι₃_inj hdim_eq3_1
  have hπ₂ι₃_inj : Function.Injective (π₂.comp R₃.subtype) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    ext
    have h_diff_R3 : a - b ∈ R₃ := R₃.sub_mem ha hb
    have h_ker : a - b ∈ LinearMap.ker π₂ := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact heq
    rw [Submodule.ker_projectionOnto hc12.symm] at h_ker
    have : a - b ∈ R₁ ⊓ R₃ := ⟨h_ker, h_diff_R3⟩
    rw [h₁₃] at this; exact sub_eq_zero.mp ((Submodule.mem_bot k).mp this)
  have hdim_eq3_2 : Module.finrank k ↥R₃ = Module.finrank k ↥R₂ := by omega
  let e₂ : ↥R₃ ≃ₗ[k] ↥R₂ := LinearEquiv.ofInjectiveOfFinrankEq
    (π₂.comp R₃.subtype) hπ₂ι₃_inj hdim_eq3_2
  let A_iso : ↥R₁ ≃ₗ[k] ↥R₂ := e₁.symm.trans e₂
  have hR₁_ne : R₁ ≠ ⊥ := by intro h; rw [h, finrank_bot] at hn_ge; omega
  have hR₁_nt : Nontrivial ↥R₁ := by
    obtain ⟨v, hvm, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR₁_ne
    exact ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congr_arg Subtype.val h)⟩⟩
  obtain ⟨w, hw_ne⟩ := exists_ne (0 : ↥R₁)
  let W : Submodule k ↥R₁ := Submodule.span k {w}
  have hW_ne : W ≠ ⊥ := by
    intro h; exact hw_ne (Submodule.span_singleton_eq_bot.mp h)
  obtain ⟨W', hWc⟩ := Submodule.exists_isCompl W
  have hW'_ne : W' ≠ ⊥ := by
    intro h; have := Submodule.finrank_add_eq_of_isCompl hWc
    rw [h, finrank_bot, add_zero, finrank_span_singleton hw_ne] at this; omega
  let AW : Submodule k ↥R₂ := Submodule.map A_iso.toLinearMap W
  let AW' : Submodule k ↥R₂ := Submodule.map A_iso.toLinearMap W'
  have hAW_isCompl : IsCompl AW AW' := by
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro x ⟨hx1, hx2⟩
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx1
      obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hx2
      have hab : a = b := A_iso.injective (by exact_mod_cast heq.symm)
      subst hab
      have : a ∈ W ⊓ W' := ⟨ha, hb⟩
      rw [hWc.inf_eq_bot, Submodule.mem_bot] at this
      simp [this]
    · rw [codisjoint_iff, ← Submodule.map_sup, hWc.sup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top.mpr A_iso.surjective]
  have mem_p_of : ∀ v : ρ.center, π₁ v ∈ W → π₂ v ∈ AW → v ∈
      (Submodule.comap π₁ W ⊓ Submodule.comap π₂ AW : Submodule k ρ.center) :=
    fun v h1 h2 => ⟨Submodule.mem_comap.mpr h1, Submodule.mem_comap.mpr h2⟩
  have mem_q_of : ∀ v : ρ.center, π₁ v ∈ W' → π₂ v ∈ AW' → v ∈
      (Submodule.comap π₁ W' ⊓ Submodule.comap π₂ AW' : Submodule k ρ.center) :=
    fun v h1 h2 => ⟨Submodule.mem_comap.mpr h1, Submodule.mem_comap.mpr h2⟩
  let p := Submodule.comap π₁ W ⊓ Submodule.comap π₂ AW
  let q := Submodule.comap π₁ W' ⊓ Submodule.comap π₂ AW'
  have hp_ne : p ≠ ⊥ := by
    intro h
    have : R₁.subtype w ∈ p :=
      mem_p_of _ (by rw [π₁_on_R₁]; exact Submodule.mem_span_singleton_self w)
        (by rw [π₂_on_R₁]; exact AW.zero_mem)
    rw [h] at this
    exact hw_ne (by ext; exact (Submodule.mem_bot k).mp this)
  have hq_ne : q ≠ ⊥ := by
    intro h
    obtain ⟨w', hw'_mem, hw'_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'_ne
    have : R₁.subtype w' ∈ q :=
      mem_q_of _ (by rw [π₁_on_R₁]; exact hw'_mem) (by rw [π₂_on_R₁]; exact AW'.zero_mem)
    rw [h] at this
    exact hw'_ne (by ext; exact (Submodule.mem_bot k).mp this)
  have hpq : IsCompl p q := by
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro v hv
      have hvp := (Submodule.mem_inf.mp hv).1
      have hvq := (Submodule.mem_inf.mp hv).2
      have hv1 : π₁ v ∈ W := (Submodule.mem_inf.mp hvp).1
      have hv2 : π₂ v ∈ AW := (Submodule.mem_inf.mp hvp).2
      have hv3 : π₁ v ∈ W' := (Submodule.mem_inf.mp hvq).1
      have hv4 : π₂ v ∈ AW' := (Submodule.mem_inf.mp hvq).2
      have h1 : π₁ v ∈ W ⊓ W' := ⟨hv1, hv3⟩
      rw [hWc.inf_eq_bot, Submodule.mem_bot] at h1
      have h2 : π₂ v ∈ AW ⊓ AW' := ⟨hv2, hv4⟩
      rw [hAW_isCompl.inf_eq_bot, Submodule.mem_bot] at h2
      have := decomp_v v
      rw [h1, h2, map_zero, map_zero, add_zero] at this
      exact this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      obtain ⟨w₁, hw₁, w₁', hw₁', hww⟩ := Submodule.mem_sup.mp
        (show π₁ v ∈ W ⊔ W' from hWc.sup_eq_top ▸ Submodule.mem_top)
      obtain ⟨a₁, ha₁, a₁', ha₁', haa⟩ := Submodule.mem_sup.mp
        (show π₂ v ∈ AW ⊔ AW' from hAW_isCompl.sup_eq_top ▸ Submodule.mem_top)
      have hvp : R₁.subtype w₁ + R₂.subtype a₁ ∈ p :=
        mem_p_of _ (by rw [map_add, π₁_on_R₁, π₁_on_R₂, add_zero]; exact hw₁)
          (by rw [map_add, π₂_on_R₁, π₂_on_R₂, zero_add]; exact ha₁)
      have hvq : R₁.subtype w₁' + R₂.subtype a₁' ∈ q :=
        mem_q_of _ (by rw [map_add, π₁_on_R₁, π₁_on_R₂, add_zero]; exact hw₁')
          (by rw [map_add, π₂_on_R₁, π₂_on_R₂, zero_add]; exact ha₁')
      have hsum : R₁.subtype w₁ + R₂.subtype a₁ +
          (R₁.subtype w₁' + R₂.subtype a₁') = v := by
        rw [decomp_v v, ← hww, ← haa, map_add, map_add]; abel
      exact Submodule.mem_sup.mpr ⟨_, hvp, _, hvq, hsum⟩
  have range_split_R₁ : ∀ x ∈ R₁, ∃ a ∈ R₁, ∃ b ∈ R₁,
      a ∈ p ∧ b ∈ q ∧ a + b = x := by
    intro x hx
    obtain ⟨w₁, hw₁, w₁', hw₁', hww⟩ := Submodule.mem_sup.mp
      (show (⟨x, hx⟩ : ↥R₁) ∈ W ⊔ W' from hWc.sup_eq_top ▸ Submodule.mem_top)
    refine ⟨R₁.subtype w₁, w₁.2, R₁.subtype w₁', w₁'.2,
      mem_p_of _ (by rw [π₁_on_R₁]; exact hw₁) (by rw [π₂_on_R₁]; exact AW.zero_mem),
      mem_q_of _ (by rw [π₁_on_R₁]; exact hw₁') (by rw [π₂_on_R₁]; exact AW'.zero_mem),
        ?_⟩
    have heq : (⟨x, hx⟩ : ↥R₁) = w₁ + w₁' := by
      ext; simpa using (congr_arg Subtype.val hww).symm
    calc R₁.subtype w₁ + R₁.subtype w₁' = R₁.subtype (w₁ + w₁') := (map_add _ _
      _).symm
      _ = R₁.subtype ⟨x, hx⟩ := by rw [← heq]
      _ = x := rfl
  have range_split_R₂ : ∀ x ∈ R₂, ∃ a ∈ R₂, ∃ b ∈ R₂,
      a ∈ p ∧ b ∈ q ∧ a + b = x := by
    intro x hx
    obtain ⟨a₁, ha₁, a₁', ha₁', haa⟩ := Submodule.mem_sup.mp
      (show (⟨x, hx⟩ : ↥R₂) ∈ AW ⊔ AW' from hAW_isCompl.sup_eq_top ▸
        Submodule.mem_top)
    refine ⟨R₂.subtype a₁, a₁.2, R₂.subtype a₁', a₁'.2,
      mem_p_of _ (by rw [π₁_on_R₂]; exact W.zero_mem) (by rw [π₂_on_R₂]; exact ha₁),
      mem_q_of _ (by rw [π₁_on_R₂]; exact W'.zero_mem) (by rw [π₂_on_R₂]; exact ha₁'),
        ?_⟩
    have heq : (⟨x, hx⟩ : ↥R₂) = a₁ + a₁' := by
      ext; simpa using (congr_arg Subtype.val haa).symm
    calc R₂.subtype a₁ + R₂.subtype a₁' = R₂.subtype (a₁ + a₁') := (map_add _ _
      _).symm
      _ = R₂.subtype ⟨x, hx⟩ := by rw [← heq]
      _ = x := rfl
  have range_split_R₃ : ∀ x ∈ R₃, ∃ a ∈ R₃, ∃ b ∈ R₃,
      a ∈ p ∧ b ∈ q ∧ a + b = x := by
    intro x hx
    obtain ⟨w₁, hw₁, w₁', hw₁', hww⟩ := Submodule.mem_sup.mp
      (show π₁ x ∈ W ⊔ W' from hWc.sup_eq_top ▸ Submodule.mem_top)
    let v₁ := e₁.symm w₁
    let v₁' := e₁.symm w₁'
    have he₁_v₁ : (π₁.comp R₃.subtype) v₁ = w₁ := by
      change (π₁.comp R₃.subtype) (e₁.symm w₁) = w₁
      simp [e₁, LinearEquiv.ofInjectiveOfFinrankEq]
    have he₁_v₁' : (π₁.comp R₃.subtype) v₁' = w₁' := by
      change (π₁.comp R₃.subtype) (e₁.symm w₁') = w₁'
      simp [e₁, LinearEquiv.ofInjectiveOfFinrankEq]
    have hπ₂_v₁ : π₂ (R₃.subtype v₁) = A_iso w₁ := by
      change (π₂.comp R₃.subtype) (e₁.symm w₁) =
        (e₁.symm.trans e₂) w₁
      simp [e₁, e₂, LinearEquiv.ofInjectiveOfFinrankEq, LinearEquiv.trans_apply]
    have hπ₂_v₁' : π₂ (R₃.subtype v₁') = A_iso w₁' := by
      change (π₂.comp R₃.subtype) (e₁.symm w₁') =
        (e₁.symm.trans e₂) w₁'
      simp [e₁, e₂, LinearEquiv.ofInjectiveOfFinrankEq, LinearEquiv.trans_apply]
    have hv₁_p : (v₁ : ρ.center) ∈ p :=
      mem_p_of _ (by change (π₁.comp R₃.subtype) v₁ ∈ W; rw [he₁_v₁]; exact hw₁)
        (by change π₂ (R₃.subtype v₁) ∈ AW; rw [hπ₂_v₁]; exact
          Submodule.mem_map_of_mem hw₁)
    have hv₁'_q : (v₁' : ρ.center) ∈ q :=
      mem_q_of _ (by change (π₁.comp R₃.subtype) v₁' ∈ W'; rw [he₁_v₁']; exact hw₁')
        (by change π₂ (R₃.subtype v₁') ∈ AW'; rw [hπ₂_v₁']; exact
          Submodule.mem_map_of_mem hw₁')
    have hsum : (v₁ : ρ.center) + (v₁' : ρ.center) = x := by
      have key : v₁ + v₁' = (⟨x, hx⟩ : ↥R₃) := by
        apply hπ₁ι₃_inj
        show (π₁.comp R₃.subtype) (v₁ + v₁') = (π₁.comp R₃.subtype) ⟨x, hx⟩
        rw [map_add, he₁_v₁, he₁_v₁']
        ext; simpa using congr_arg Subtype.val hww
      exact congr_arg Subtype.val key
    exact ⟨v₁, v₁.2, v₁', v₁'.2, hv₁_p, hv₁'_q, hsum⟩
  obtain ⟨hc₁, hp₁, hq₁⟩ := isCompl_comap_of_range_decomposition p q hpq
    ρ.leafOneToCenter hinj₁ R₁ rfl range_split_R₁
  obtain ⟨hc₂, hp₂, hq₂⟩ := isCompl_comap_of_range_decomposition p q hpq
    ρ.leafTwoToCenter hinj₂ R₂ rfl range_split_R₂
  obtain ⟨hc₃, hp₃, hq₃⟩ := isCompl_comap_of_range_decomposition p q hpq
    ρ.leafThreeToCenter hinj₃ R₃ rfl range_split_R₃
  rcases hind.2 p q _ _ _ _ _ _ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
    with ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩
  · exact hp_ne h
  · exact hq_ne h

private lemma decomp_dim_ge_three {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hA₁ : LinearMap.ker ρ.leafOneToCenter = ⊥) (hA₂ : LinearMap.ker ρ.leafTwoToCenter =
      ⊥)
    (hA₃ : LinearMap.ker ρ.leafThreeToCenter = ⊥)
    (hR : LinearMap.range ρ.leafOneToCenter ⊔ LinearMap.range ρ.leafTwoToCenter ⊔
      LinearMap.range ρ.leafThreeToCenter = ⊤)
    (hV : Module.finrank k ρ.center ≥ 3) : False := by
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  haveI : Nontrivial ρ.center := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have mk_absurd : ∀ (p q : Submodule k ρ.center), IsCompl p q →
      p ≠ ⊥ → q ≠ ⊥ →
      (p ≤ LinearMap.range ρ.leafOneToCenter ∨ LinearMap.range ρ.leafOneToCenter ≤ q) →
      (p ≤ LinearMap.range ρ.leafTwoToCenter ∨ LinearMap.range ρ.leafTwoToCenter ≤ q) →
      (p ≤ LinearMap.range ρ.leafThreeToCenter ∨ LinearMap.range ρ.leafThreeToCenter ≤ q)
        →
      False := by
    intro p q hpq hp_ne hq_ne h1 h2 h3
    obtain ⟨p₁, q₁, hc₁, hp₁, hq₁⟩ := exists_isCompl_mappedInto_of_range_comparable
      ρ.leafOneToCenter hinj₁ p q hpq h1
    obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := exists_isCompl_mappedInto_of_range_comparable
      ρ.leafTwoToCenter hinj₂ p q hpq h2
    obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := exists_isCompl_mappedInto_of_range_comparable
      ρ.leafThreeToCenter hinj₃ p q hpq h3
    rcases hind.2 p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂
      hp₃ hq₃
      with ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩
    · exact hp_ne h
    · exact hq_ne h
  have span_absurd : ∀ (w : ρ.center) (_ : w ≠ 0) (q : Submodule k ρ.center)
      (hpq : IsCompl (Submodule.span k {w}) q),
      (Submodule.span k {w} ≤ LinearMap.range ρ.leafOneToCenter ∨ LinearMap.range
        ρ.leafOneToCenter ≤ q) →
      (Submodule.span k {w} ≤ LinearMap.range ρ.leafTwoToCenter ∨ LinearMap.range
        ρ.leafTwoToCenter ≤ q) →
      (Submodule.span k {w} ≤ LinearMap.range ρ.leafThreeToCenter ∨ LinearMap.range
        ρ.leafThreeToCenter ≤ q) →
      False := by
    intro w hw q hpq h1 h2 h3
    have hp_dim := finrank_span_singleton (K := k) hw
    have hp_ne : Submodule.span k {w} ≠ ⊥ := by
      intro h; exact hw (Submodule.span_singleton_eq_bot.mp h)
    have hq_ne : q ≠ ⊥ := by
      intro h; have := Submodule.finrank_add_eq_of_isCompl hpq
      rw [h, finrank_bot, add_zero, hp_dim] at this; omega
    exact mk_absurd _ q hpq hp_ne hq_ne h1 h2 h3
  set R₁ := LinearMap.range ρ.leafOneToCenter
  set R₂ := LinearMap.range ρ.leafTwoToCenter
  set R₃ := LinearMap.range ρ.leafThreeToCenter
  by_cases h_triple : R₁ ⊓ R₂ ⊓ R₃ ≠ ⊥
  · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_triple
    rw [Submodule.mem_inf, Submodule.mem_inf] at hw_mem
    obtain ⟨q, hpq⟩ := Submodule.exists_isCompl (Submodule.span k {w})
    exact span_absurd w hw_ne q hpq
      (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1.1)))
      (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1.2)))
      (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)))
  · push Not at h_triple
    by_cases h₁₂ : R₁ ⊓ R₂ ≠ ⊥
    · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁₂
      rw [Submodule.mem_inf] at hw_mem
      have hp1 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1)
      have hp2 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)
      have hdisj : Disjoint R₃ (Submodule.span k {w}) := by
        rw [disjoint_comm, disjoint_iff]
        exact le_bot_iff.mp (le_trans (inf_le_inf_right R₃ (le_inf hp1 hp2)) h_triple.le)
      obtain ⟨q, hpq, h3q⟩ := exists_isCompl_of_disjoint _ R₃ hdisj
      exact span_absurd w hw_ne q hpq (Or.inl hp1) (Or.inl hp2) (Or.inr h3q)
    · push Not at h₁₂
      by_cases h₁₃ : R₁ ⊓ R₃ ≠ ⊥
      · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁₃
        rw [Submodule.mem_inf] at hw_mem
        have hp1 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1)
        have hp3 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)
        have h132 : R₁ ⊓ R₃ ⊓ R₂ = ⊥ := by
          convert h_triple using 1; ac_rfl
        have hdisj : Disjoint R₂ (Submodule.span k {w}) := by
          rw [disjoint_comm, disjoint_iff]
          exact le_bot_iff.mp (le_trans (inf_le_inf_right R₂ (le_inf hp1 hp3)) h132.le)
        obtain ⟨q, hpq, h2q⟩ := exists_isCompl_of_disjoint _ R₂ hdisj
        exact span_absurd w hw_ne q hpq (Or.inl hp1) (Or.inr h2q) (Or.inl hp3)
      · push Not at h₁₃
        by_cases h₂₃ : R₂ ⊓ R₃ ≠ ⊥
        · obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂₃
          rw [Submodule.mem_inf] at hw_mem
          have hp2 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.1)
          have hp3 := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_mem.2)
          have h231 : R₂ ⊓ R₃ ⊓ R₁ = ⊥ := by
            convert h_triple using 1; ac_rfl
          have hdisj : Disjoint R₁ (Submodule.span k {w}) := by
            rw [disjoint_comm, disjoint_iff]
            exact le_bot_iff.mp (le_trans (inf_le_inf_right R₁ (le_inf hp2 hp3)) h231.le)
          obtain ⟨q, hpq, h1q⟩ := exists_isCompl_of_disjoint _ R₁ hdisj
          exact span_absurd w hw_ne q hpq (Or.inr h1q) (Or.inl hp2) (Or.inl hp3)
        · push Not at h₂₃
          have case3 : ∀ {Ra Rb Rc : Submodule k ρ.center},
              Disjoint Ra (Rb ⊔ Rc) → Ra ⊔ (Rb ⊔ Rc) = ⊤ →
              Rb ⊓ Rc = ⊥ →
              (∀ p q : Submodule k ρ.center, IsCompl p q → p ≠ ⊥ → q ≠ ⊥ →
                (p ≤ Ra ∨ Ra ≤ q) → (p ≤ Rb ∨ Rb ≤ q) →
                (p ≤ Rc ∨ Rc ≤ q) → False) →
              False := by
            intro Ra Rb Rc hdisj hcod hjk absurd_fn
            have hpq : IsCompl Ra (Rb ⊔ Rc) := ⟨hdisj, codisjoint_iff.mpr hcod⟩
            by_cases haz : Ra = ⊥
            · -- Ra = ⊥, Rb ⊔ Rc = ⊤
              have htop : Rb ⊔ Rc = ⊤ := by rwa [haz, bot_sup_eq] at hcod
              by_cases hbz : Rb = ⊥
              · -- Rb = ⊥, Rc = ⊤
                have hctop : Rc = ⊤ := by rwa [hbz, bot_sup_eq] at htop
                obtain ⟨v, hv⟩ := exists_ne (0 : ρ.center)
                obtain ⟨q, hpq'⟩ := Submodule.exists_isCompl (Submodule.span k {v})
                have hp_ne : Submodule.span k {v} ≠ ⊥ := by
                  intro h; exact hv (Submodule.span_singleton_eq_bot.mp h)
                have hq_ne : q ≠ ⊥ := by
                  intro h; have := Submodule.finrank_add_eq_of_isCompl hpq'
                  rw [h, finrank_bot, add_zero, finrank_span_singleton hv] at this; omega
                exact absurd_fn _ q hpq' hp_ne hq_ne
                  (Or.inr (haz ▸ bot_le)) (Or.inr (hbz ▸ bot_le))
                  (Or.inl (hctop ▸ le_top))
              · by_cases hcz : Rc = ⊥
                · -- Rc = ⊥, Rb = ⊤
                  have hbtop : Rb = ⊤ := by rwa [hcz, sup_bot_eq] at htop
                  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.center)
                  obtain ⟨q, hpq'⟩ := Submodule.exists_isCompl (Submodule.span k {v})
                  have hp_ne : Submodule.span k {v} ≠ ⊥ := by
                    intro h; exact hv (Submodule.span_singleton_eq_bot.mp h)
                  have hq_ne : q ≠ ⊥ := by
                    intro h; have := Submodule.finrank_add_eq_of_isCompl hpq'
                    rw [h, finrank_bot, add_zero, finrank_span_singleton hv] at this; omega
                  exact absurd_fn _ q hpq' hp_ne hq_ne
                    (Or.inr (haz ▸ bot_le)) (Or.inl (hbtop ▸ le_top))
                    (Or.inr (hcz ▸ bot_le))
                · -- Both Rb, Rc nontrivial. IsCompl Rb Rc.
                  have hbc : IsCompl Rb Rc :=
                    ⟨disjoint_iff.mpr hjk, codisjoint_iff.mpr htop⟩
                  exact absurd_fn Rb Rc hbc hbz hcz
                    (Or.inr (haz ▸ bot_le)) (Or.inl le_rfl) (Or.inr le_rfl)
            · -- Ra ≠ ⊥
              by_cases hqz : Rb ⊔ Rc = ⊥
              · -- Rb = Rc = ⊥, Ra = ⊤
                have hbz : Rb = ⊥ := le_bot_iff.mp (by rw [← hqz]; exact le_sup_left)
                have hcz : Rc = ⊥ := le_bot_iff.mp (by rw [← hqz]; exact le_sup_right)
                have hatop : Ra = ⊤ := by rwa [hqz, sup_bot_eq] at hcod
                obtain ⟨v, hv⟩ := exists_ne (0 : ρ.center)
                obtain ⟨q, hpq'⟩ := Submodule.exists_isCompl (Submodule.span k {v})
                have hp_ne : Submodule.span k {v} ≠ ⊥ := by
                  intro h; exact hv (Submodule.span_singleton_eq_bot.mp h)
                have hq_ne : q ≠ ⊥ := by
                  intro h; have := Submodule.finrank_add_eq_of_isCompl hpq'
                  rw [h, finrank_bot, add_zero, finrank_span_singleton hv] at this; omega
                exact absurd_fn _ q hpq' hp_ne hq_ne
                  (Or.inl (hatop ▸ le_top)) (Or.inr (hbz ▸ bot_le))
                  (Or.inr (hcz ▸ bot_le))
              · exact absurd_fn Ra (Rb ⊔ Rc) hpq haz hqz
                  (Or.inl le_rfl) (Or.inr le_sup_left) (Or.inr le_sup_right)
          by_cases hR₁_23 : Disjoint R₁ (R₂ ⊔ R₃)
          · have : R₁ ⊔ (R₂ ⊔ R₃) = ⊤ := by rw [← sup_assoc]; exact hR
            exact case3 hR₁_23 this h₂₃ mk_absurd
          · by_cases hR₂_13 : Disjoint R₂ (R₁ ⊔ R₃)
            · have : R₂ ⊔ (R₁ ⊔ R₃) = ⊤ := by
                have := hR; rw [show R₁ ⊔ R₂ ⊔ R₃ = R₂ ⊔ (R₁ ⊔ R₃) from by
                  simp only [sup_comm, sup_left_comm]] at this; exact this
              exact case3 hR₂_13 this h₁₃
                (fun p q hpq hp hq ha hb hc => mk_absurd p q hpq hp hq hb ha hc)
            · by_cases hR₃_12 : Disjoint R₃ (R₁ ⊔ R₂)
              · have : R₃ ⊔ (R₁ ⊔ R₂) = ⊤ := by
                  have := hR; rw [show R₁ ⊔ R₂ ⊔ R₃ = R₃ ⊔ (R₁ ⊔ R₂) from by
                    simp only [sup_comm, sup_left_comm]] at this; exact this
                exact case3 hR₃_12 this h₁₂
                  (fun p q hpq hp hq ha hb hc => mk_absurd p q hpq hp hq hb hc ha)
              · -- All Rᵢ ⊓ (Rⱼ ⊔ Rₖ) ≠ ⊥, all pairwise = ⊥.
                have not_le_absurd :
                    ∀ (Ra Rb Rc : Submodule k ρ.center),
                      ¬ Ra ≤ Rb ⊔ Rc →
                      (∀ (w : ρ.center), w ≠ 0 → ∀ (q : Submodule k ρ.center),
                        IsCompl (Submodule.span k {w}) q →
                        (Submodule.span k {w} ≤ Ra ∨ Ra ≤ q) →
                        (Submodule.span k {w} ≤ Rb ∨ Rb ≤ q) →
                        (Submodule.span k {w} ≤ Rc ∨ Rc ≤ q) →
                        False) →
                      False := by
                  intro Ra Rb Rc hle absurd_fn
                  have ⟨w, hw_in, hw_not⟩ : ∃ w, w ∈ Ra ∧ w ∉ (Rb ⊔ Rc : Submodule k
                    ρ.center) := by
                    by_contra h; push Not at h; exact hle h
                  have hw_ne : w ≠ 0 := fun h => hw_not (h ▸ (Rb ⊔ Rc).zero_mem)
                  have hdisj : Disjoint (Rb ⊔ Rc) (Submodule.span k {w}) :=
                    (Submodule.disjoint_span_singleton' hw_ne).mpr hw_not
                  obtain ⟨q, hpq, hle'⟩ := exists_isCompl_of_disjoint _ (Rb ⊔ Rc) hdisj
                  exact absurd_fn w hw_ne q hpq
                    (Or.inl (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw_in)))
                    (Or.inr (le_sup_left.trans hle'))
                    (Or.inr (le_sup_right.trans hle'))
                by_cases hR1_le : R₁ ≤ R₂ ⊔ R₃
                · by_cases hR2_le : R₂ ≤ R₁ ⊔ R₃
                  · by_cases hR3_le : R₃ ≤ R₁ ⊔ R₂
                    · -- SUBCASE B: all Rᵢ ≤ Rⱼ ⊔ Rₖ
                      exact decomp_all_pairwise_compl ρ hind hA₁ hA₂ hA₃ hR hV
                        h₁₂ h₁₃ h₂₃ hR1_le hR2_le hR3_le
                    · exact not_le_absurd R₃ R₁ R₂ hR3_le
                        (fun w hw q hpq h3 h1 h2 => span_absurd w hw q hpq h1 h2 h3)
                  · exact not_le_absurd R₂ R₁ R₃ hR2_le
                      (fun w hw q hpq h2 h1 h3 => span_absurd w hw q hpq h1 h2 h3)
                · exact not_le_absurd R₁ R₂ R₃ hR1_le
                    (fun w hw q hpq h1 h2 h3 => span_absurd w hw q hpq h1 h2 h3)

private lemma decomp_bijective_and_split {k : Type*} [Field k] (ρ : FourVertexStarRepresentation
  k)
    (hind : ρ.IsIndecomposable)
    (hA₁_inj : Function.Injective ρ.leafOneToCenter)
    (hA₁_surj : LinearMap.range ρ.leafOneToCenter = ⊤)
    (p q : Submodule k ρ.center) (hpq : IsCompl p q)
    (h₂ : LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range ρ.leafTwoToCenter ≤ q)
    (h₃ : LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range ρ.leafThreeToCenter ≤
      q) :
    p = ⊥ ∨ q = ⊥ := by
  have hc₁ := isCompl_comap_of_range_eq_top ρ.leafOneToCenter hA₁_inj hA₁_surj p q hpq
  have arm₂ : ∃ (p₂ q₂ : Submodule k ρ.leafTwo), IsCompl p₂ q₂ ∧
      (∀ x ∈ p₂, ρ.leafTwoToCenter x ∈ p) ∧ (∀ x ∈ q₂, ρ.leafTwoToCenter x ∈ q)
        := by
    rcases h₂ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₃ : ∃ (p₃ q₃ : Submodule k ρ.leafThree), IsCompl p₃ q₃ ∧
      (∀ x ∈ p₃, ρ.leafThreeToCenter x ∈ p) ∧ (∀ x ∈ q₃, ρ.leafThreeToCenter x
        ∈ q) := by
    rcases h₃ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q (Submodule.comap ρ.leafOneToCenter p) (Submodule.comap ρ.leafOneToCenter q)
    p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃
    (fun x hx => hx) (fun x hx => hx)
    hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

private lemma classification_injective_dim_bound {k : Type*} [Field k] (ρ :
  FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hA₁ : LinearMap.ker ρ.leafOneToCenter = ⊥) (hA₂ : LinearMap.ker ρ.leafTwoToCenter =
      ⊥)
    (hA₃ : LinearMap.ker ρ.leafThreeToCenter = ⊥)
    (hR : LinearMap.range ρ.leafOneToCenter ⊔ LinearMap.range ρ.leafTwoToCenter ⊔
      LinearMap.range ρ.leafThreeToCenter = ⊤)
    (hV : Module.finrank k ρ.center ≥ 2) :
    Module.finrank k ρ.center = 2 ∧ Module.finrank k ρ.leafOne = 1 ∧
    Module.finrank k ρ.leafTwo = 1 ∧ Module.finrank k ρ.leafThree = 1 := by
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  have hle₁ := LinearMap.finrank_le_finrank_of_injective hinj₁
  have hle₂ := LinearMap.finrank_le_finrank_of_injective hinj₂
  have hle₃ := LinearMap.finrank_le_finrank_of_injective hinj₃
  have hV_le : Module.finrank k ρ.center ≤ 2 := by
    by_contra h; push Not at h
    exact decomp_dim_ge_three ρ hind hA₁ hA₂ hA₃ hR (by omega)
  have hV_eq : Module.finrank k ρ.center = 2 := by omega
  have rt₁ : Module.finrank k ρ.leafOne = 2 → LinearMap.range ρ.leafOneToCenter = ⊤ :=
    fun h => (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank (by omega)).mp hA₁
  have rt₂ : Module.finrank k ρ.leafTwo = 2 → LinearMap.range ρ.leafTwoToCenter = ⊤ :=
    fun h => (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank (by omega)).mp hA₂
  have rt₃ : Module.finrank k ρ.leafThree = 2 → LinearMap.range ρ.leafThreeToCenter = ⊤ :=
    fun h => (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank (by omega)).mp hA₃
  have fr₁ := LinearMap.finrank_range_of_inj hinj₁
  have fr₂ := LinearMap.finrank_range_of_inj hinj₂
  have fr₃ := LinearMap.finrank_range_of_inj hinj₃
  have rb₁ : Module.finrank k ρ.leafOne = 0 → LinearMap.range ρ.leafOneToCenter = ⊥ :=
    fun h => Submodule.finrank_eq_zero.mp (by rw [fr₁]; exact h)
  have rb₂ : Module.finrank k ρ.leafTwo = 0 → LinearMap.range ρ.leafTwoToCenter = ⊥ :=
    fun h => Submodule.finrank_eq_zero.mp (by rw [fr₂]; exact h)
  have rb₃ : Module.finrank k ρ.leafThree = 0 → LinearMap.range ρ.leafThreeToCenter = ⊥ :=
    fun h => Submodule.finrank_eq_zero.mp (by rw [fr₃]; exact h)
  haveI : Nontrivial ρ.center := Module.nontrivial_of_finrank_eq_succ (n := 1) (by omega)
  have absurd_pq : ∀ (p q : Submodule k ρ.center), IsCompl p q →
      Module.finrank k p = 1 → Module.finrank k q = 1 →
      (LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range ρ.leafOneToCenter ≤ q) ∨
        (Function.Injective ρ.leafOneToCenter ∧ LinearMap.range ρ.leafOneToCenter = ⊤) →
      (LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range ρ.leafTwoToCenter ≤ q) ∨
        (Function.Injective ρ.leafTwoToCenter ∧ LinearMap.range ρ.leafTwoToCenter = ⊤) →
      (LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range ρ.leafThreeToCenter ≤ q)
        ∨
        (Function.Injective ρ.leafThreeToCenter ∧ LinearMap.range ρ.leafThreeToCenter = ⊤)
          →
      False := by
    intro p q hpq hp hq h₁ h₂ h₃
    rcases eq_bot_or_eq_bot_of_range_side_or_bijective ρ hind p q hpq h₁ h₂ h₃ with hp_bot |
      hq_bot
    · rw [hp_bot, finrank_bot] at hp; omega
    · rw [hq_bot, finrank_bot] at hq; omega
  refine ⟨hV_eq, ?_, ?_, ?_⟩
  all_goals by_contra hdim
  · have hd₁ : Module.finrank k ρ.leafOne = 0 ∨ Module.finrank k ρ.leafOne = 2 := by omega
    have get_line : ∃ (p : Submodule k ρ.center), Module.finrank k p = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : ρ.center)
      exact ⟨Submodule.span k {v}, finrank_span_singleton hv⟩
    have h₁_cond : ∀ (p q : Submodule k ρ.center), IsCompl p q →
        (LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range ρ.leafOneToCenter ≤ q) ∨
        (Function.Injective ρ.leafOneToCenter ∧ LinearMap.range ρ.leafOneToCenter = ⊤) := by
      intro p q _
      rcases hd₁ with h | h
      · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
      · exact Or.inr ⟨hinj₁, rt₁ h⟩
    by_cases hd₂ : Module.finrank k ρ.leafTwo = 1
    · -- range A₂ is a 1-dim line. Use it as p.
      set p := LinearMap.range ρ.leafTwoToCenter
      have hp : Module.finrank k p = 1 := by rw [fr₂, hd₂]
      by_cases hd₃ : Module.finrank k ρ.leafThree = 1
      · -- range A₃ is also 1-dim.
        by_cases heq : p = LinearMap.range ρ.leafThreeToCenter
        · -- Same line. Both ≤ p. Pick any complement q.
          obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
          have hq : Module.finrank k q = 1 := by
            have := Submodule.finrank_add_eq_of_isCompl hpq; omega
          exact absurd_pq p q hpq hp hq (h₁_cond p q hpq)
            (Or.inl (Or.inl le_rfl))
            (Or.inl (Or.inl (heq ▸ le_rfl)))
        · -- Different lines. IsCompl. Use p = range A₂, q = range A₃.
          have hq : Module.finrank k (LinearMap.range ρ.leafThreeToCenter) = 1 := by rw [fr₃,
            hd₃]
          have hpq := isCompl_of_finrank_eq_one_of_ne hV_eq p (LinearMap.range
            ρ.leafThreeToCenter) hp hq heq
          exact absurd_pq p (LinearMap.range ρ.leafThreeToCenter) hpq hp hq (h₁_cond p _ hpq)
            (Or.inl (Or.inl le_rfl))
            (Or.inl (Or.inr le_rfl))
      · -- dim V₃ ≠ 1, so dim V₃ = 0 or 2. range A₃ fits easily.
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₃_cond : (LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range
          ρ.leafThreeToCenter ≤ q) ∨
            (Function.Injective ρ.leafThreeToCenter ∧ LinearMap.range ρ.leafThreeToCenter =
              ⊤) := by
          have : Module.finrank k ρ.leafThree = 0 ∨ Module.finrank k ρ.leafThree = 2 := by
            omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq (h₁_cond p q hpq)
          (Or.inl (Or.inl le_rfl)) h₃_cond
    · -- dim V₂ ≠ 1. Check dim V₃.
      by_cases hd₃ : Module.finrank k ρ.leafThree = 1
      · -- range A₃ is 1-dim. Use it as p.
        set p := LinearMap.range ρ.leafThreeToCenter
        have hp : Module.finrank k p = 1 := by rw [fr₃, hd₃]
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₂_cond : (LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range
          ρ.leafTwoToCenter ≤ q) ∨
            (Function.Injective ρ.leafTwoToCenter ∧ LinearMap.range ρ.leafTwoToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafTwo = 0 ∨ Module.finrank k ρ.leafTwo = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        exact absurd_pq p q hpq hp hq (h₁_cond p q hpq) h₂_cond
          (Or.inl (Or.inl le_rfl))
      · -- Neither arm 2 nor arm 3 has dim 1. Both have dim 0 or 2.
        obtain ⟨p, hp⟩ := get_line
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₂_cond : (LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range
          ρ.leafTwoToCenter ≤ q) ∨
            (Function.Injective ρ.leafTwoToCenter ∧ LinearMap.range ρ.leafTwoToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafTwo = 0 ∨ Module.finrank k ρ.leafTwo = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        have h₃_cond : (LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range
          ρ.leafThreeToCenter ≤ q) ∨
            (Function.Injective ρ.leafThreeToCenter ∧ LinearMap.range ρ.leafThreeToCenter =
              ⊤) := by
          have : Module.finrank k ρ.leafThree = 0 ∨ Module.finrank k ρ.leafThree = 2 := by
            omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq (h₁_cond p q hpq) h₂_cond h₃_cond
  · have hd₂ : Module.finrank k ρ.leafTwo = 0 ∨ Module.finrank k ρ.leafTwo = 2 := by omega
    have h₂_cond : ∀ (p q : Submodule k ρ.center), IsCompl p q →
        (LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range ρ.leafTwoToCenter ≤ q) ∨
        (Function.Injective ρ.leafTwoToCenter ∧ LinearMap.range ρ.leafTwoToCenter = ⊤) := by
      intro p q _
      rcases hd₂ with h | h
      · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
      · exact Or.inr ⟨hinj₂, rt₂ h⟩
    have get_line : ∃ (p : Submodule k ρ.center), Module.finrank k p = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : ρ.center)
      exact ⟨Submodule.span k {v}, finrank_span_singleton hv⟩
    by_cases hd₁ : Module.finrank k ρ.leafOne = 1
    · set p := LinearMap.range ρ.leafOneToCenter
      have hp : Module.finrank k p = 1 := by rw [fr₁, hd₁]
      by_cases hd₃ : Module.finrank k ρ.leafThree = 1
      · by_cases heq : p = LinearMap.range ρ.leafThreeToCenter
        · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
          have hq : Module.finrank k q = 1 := by
            have := Submodule.finrank_add_eq_of_isCompl hpq; omega
          exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl)) (h₂_cond p q hpq)
            (Or.inl (Or.inl (heq ▸ le_rfl)))
        · have hq : Module.finrank k (LinearMap.range ρ.leafThreeToCenter) = 1 := by rw [fr₃,
          hd₃]
          have hpq := isCompl_of_finrank_eq_one_of_ne hV_eq p (LinearMap.range
            ρ.leafThreeToCenter) hp hq heq
          exact absurd_pq p (LinearMap.range ρ.leafThreeToCenter) hpq hp hq
            (Or.inl (Or.inl le_rfl)) (h₂_cond p _ hpq) (Or.inl (Or.inr le_rfl))
      · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₃_cond : (LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range
          ρ.leafThreeToCenter ≤ q) ∨
            (Function.Injective ρ.leafThreeToCenter ∧ LinearMap.range ρ.leafThreeToCenter =
              ⊤) := by
          have : Module.finrank k ρ.leafThree = 0 ∨ Module.finrank k ρ.leafThree = 2 := by
            omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl)) (h₂_cond p q hpq) h₃_cond
    · by_cases hd₃ : Module.finrank k ρ.leafThree = 1
      · set p := LinearMap.range ρ.leafThreeToCenter
        have hp : Module.finrank k p = 1 := by rw [fr₃, hd₃]
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range
          ρ.leafOneToCenter ≤ q) ∨
            (Function.Injective ρ.leafOneToCenter ∧ LinearMap.range ρ.leafOneToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafOne = 0 ∨ Module.finrank k ρ.leafOne = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond (h₂_cond p q hpq) (Or.inl (Or.inl le_rfl))
      · obtain ⟨p, hp⟩ := get_line
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range
          ρ.leafOneToCenter ≤ q) ∨
            (Function.Injective ρ.leafOneToCenter ∧ LinearMap.range ρ.leafOneToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafOne = 0 ∨ Module.finrank k ρ.leafOne = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        have h₃_cond : (LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range
          ρ.leafThreeToCenter ≤ q) ∨
            (Function.Injective ρ.leafThreeToCenter ∧ LinearMap.range ρ.leafThreeToCenter =
              ⊤) := by
          have : Module.finrank k ρ.leafThree = 0 ∨ Module.finrank k ρ.leafThree = 2 := by
            omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₃, rt₃ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond (h₂_cond p q hpq) h₃_cond
  · have hd₃ : Module.finrank k ρ.leafThree = 0 ∨ Module.finrank k ρ.leafThree = 2 := by
      omega
    have h₃_cond : ∀ (p q : Submodule k ρ.center), IsCompl p q →
        (LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range ρ.leafThreeToCenter ≤ q)
          ∨
        (Function.Injective ρ.leafThreeToCenter ∧ LinearMap.range ρ.leafThreeToCenter = ⊤) :=
          by
      intro p q _
      rcases hd₃ with h | h
      · exact Or.inl (Or.inl ((rb₃ h).symm ▸ bot_le))
      · exact Or.inr ⟨hinj₃, rt₃ h⟩
    have get_line : ∃ (p : Submodule k ρ.center), Module.finrank k p = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : ρ.center)
      exact ⟨Submodule.span k {v}, finrank_span_singleton hv⟩
    by_cases hd₁ : Module.finrank k ρ.leafOne = 1
    · set p := LinearMap.range ρ.leafOneToCenter
      have hp : Module.finrank k p = 1 := by rw [fr₁, hd₁]
      by_cases hd₂ : Module.finrank k ρ.leafTwo = 1
      · by_cases heq : p = LinearMap.range ρ.leafTwoToCenter
        · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
          have hq : Module.finrank k q = 1 := by
            have := Submodule.finrank_add_eq_of_isCompl hpq; omega
          exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl))
            (Or.inl (Or.inl (heq ▸ le_rfl))) (h₃_cond p q hpq)
        · have hq : Module.finrank k (LinearMap.range ρ.leafTwoToCenter) = 1 := by rw [fr₂,
          hd₂]
          have hpq := isCompl_of_finrank_eq_one_of_ne hV_eq p (LinearMap.range ρ.leafTwoToCenter)
            hp hq heq
          exact absurd_pq p (LinearMap.range ρ.leafTwoToCenter) hpq hp hq
            (Or.inl (Or.inl le_rfl)) (Or.inl (Or.inr le_rfl)) (h₃_cond p _ hpq)
      · obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₂_cond : (LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range
          ρ.leafTwoToCenter ≤ q) ∨
            (Function.Injective ρ.leafTwoToCenter ∧ LinearMap.range ρ.leafTwoToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafTwo = 0 ∨ Module.finrank k ρ.leafTwo = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        exact absurd_pq p q hpq hp hq (Or.inl (Or.inl le_rfl)) h₂_cond (h₃_cond p q hpq)
    · by_cases hd₂ : Module.finrank k ρ.leafTwo = 1
      · set p := LinearMap.range ρ.leafTwoToCenter
        have hp : Module.finrank k p = 1 := by rw [fr₂, hd₂]
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range
          ρ.leafOneToCenter ≤ q) ∨
            (Function.Injective ρ.leafOneToCenter ∧ LinearMap.range ρ.leafOneToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafOne = 0 ∨ Module.finrank k ρ.leafOne = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond (Or.inl (Or.inl le_rfl)) (h₃_cond p q hpq)
      · obtain ⟨p, hp⟩ := get_line
        obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
        have hq : Module.finrank k q = 1 := by
          have := Submodule.finrank_add_eq_of_isCompl hpq; omega
        have h₁_cond : (LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range
          ρ.leafOneToCenter ≤ q) ∨
            (Function.Injective ρ.leafOneToCenter ∧ LinearMap.range ρ.leafOneToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafOne = 0 ∨ Module.finrank k ρ.leafOne = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₁ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₁, rt₁ h⟩
        have h₂_cond : (LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range
          ρ.leafTwoToCenter ≤ q) ∨
            (Function.Injective ρ.leafTwoToCenter ∧ LinearMap.range ρ.leafTwoToCenter = ⊤) :=
              by
          have : Module.finrank k ρ.leafTwo = 0 ∨ Module.finrank k ρ.leafTwo = 2 := by omega
          rcases this with h | h
          · exact Or.inl (Or.inl ((rb₂ h).symm ▸ bot_le))
          · exact Or.inr ⟨hinj₂, rt₂ h⟩
        exact absurd_pq p q hpq hp hq h₁_cond h₂_cond (h₃_cond p q hpq)

private lemma classification_injective {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hA₁ : LinearMap.ker ρ.leafOneToCenter = ⊥) (hA₂ : LinearMap.ker ρ.leafTwoToCenter =
      ⊥)
    (hA₃ : LinearMap.ker ρ.leafThreeToCenter = ⊥) :
    ρ.dimension ∈ fourVertexDimensionTuples := by
  have hinj₁ := LinearMap.ker_eq_bot.mp hA₁
  have hinj₂ := LinearMap.ker_eq_bot.mp hA₂
  have hinj₃ := LinearMap.ker_eq_bot.mp hA₃
  have hle₁ := LinearMap.finrank_le_finrank_of_injective hinj₁
  have hle₂ := LinearMap.finrank_le_finrank_of_injective hinj₂
  have hle₃ := LinearMap.finrank_le_finrank_of_injective hinj₃
  rcases sup_ranges_eq_top_or_leaf_finrank_eq_zero ρ hind hA₁ hA₂ hA₃ with hR | ⟨h₁,
    h₂, h₃⟩
  · -- Range sum = ⊤ case
    have hV_pos : 0 < Module.finrank k ρ.center := by
      rcases hind.1 with h | h | h | h
      · exact h
      · exact Nat.lt_of_lt_of_le h hle₁
      · exact Nat.lt_of_lt_of_le h hle₂
      · exact Nat.lt_of_lt_of_le h hle₃
    by_cases hV2 : Module.finrank k ρ.center ≥ 2
    · -- dim V ≥ 2: use the dimension bound lemma
      obtain ⟨hd, hd₁, hd₂, hd₃⟩ := classification_injective_dim_bound ρ hind hA₁
        hA₂ hA₃ hR hV2
      unfold FourVertexStarRepresentation.dimension fourVertexDimensionTuples
      rw [hd, hd₁, hd₂, hd₃]
      simp [Finset.mem_insert]
    · -- dim V = 1: all dᵢ ∈ {0, 1}, membership is trivial
      push Not at hV2
      have hV1 : Module.finrank k ρ.center = 1 := by omega
      have h₁ : Module.finrank k ρ.leafOne ≤ 1 := by omega
      have h₂ : Module.finrank k ρ.leafTwo ≤ 1 := by omega
      have h₃ : Module.finrank k ρ.leafThree ≤ 1 := by omega
      simp only [FourVertexStarRepresentation.dimension, fourVertexDimensionTuples,
        Finset.mem_insert, Prod.mk.injEq]
      interval_cases (Module.finrank k ρ.leafOne) <;>
        interval_cases (Module.finrank k ρ.leafTwo) <;>
          interval_cases (Module.finrank k ρ.leafThree) <;> simp_all
  · -- All arms zero: dim V = 1, so dim vector is (1, 0, 0, 0)
    have hV := center_finrank_eq_one_of_leaf_finrank_eq_zero ρ hind h₁ h₂ h₃
    simp only [FourVertexStarRepresentation.dimension, fourVertexDimensionTuples,
      Finset.mem_insert, Prod.mk.injEq]
    right; right; right; left
    exact ⟨hV, h₁, h₂, h₃⟩

/-- The associated value of an object satisfying the auxiliary property belongs to the auxiliary
finite set. -/
@[source_ref "Chapter6/Example6.3.1" (role := supporting)]
theorem auxiliary_value_mem_finset_of_property (k : Type*) [Field k] (ρ :
  FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable) :
    ρ.dimension ∈ fourVertexDimensionTuples := by
  rcases leafOne_ker_eq_bot_or_other_finrank_eq_zero ρ hind with hA₁ | ⟨hV, hV₂, hV₃⟩
  · rcases leafTwo_ker_eq_bot_or_other_finrank_eq_zero ρ hind with hA₂ | ⟨hV, hV₁, hV₃⟩
    · rcases leafThree_ker_eq_bot_or_other_finrank_eq_zero ρ hind with hA₃ | ⟨hV, hV₁,
      hV₂⟩
      · -- All kernels trivial: triple of subspaces problem
        exact classification_injective ρ hind hA₁ hA₂ hA₃
      · -- ker A₃ ≠ ⊥, V = V₁ = V₂ = 0: dim V₃ = 1
        have hV₃ := leafThree_finrank_eq_one_of_other_finrank_eq_zero ρ hind hV hV₁ hV₂
        simp only [FourVertexStarRepresentation.dimension, fourVertexDimensionTuples,
          Finset.mem_insert,
          Prod.mk.injEq]
        right; right; left
        exact ⟨hV, hV₁, hV₂, hV₃⟩
    · -- ker A₂ ≠ ⊥, V = V₁ = V₃ = 0: dim V₂ = 1
      have hV₂ := leafTwo_finrank_eq_one_of_other_finrank_eq_zero ρ hind hV hV₁ hV₃
      simp only [FourVertexStarRepresentation.dimension, fourVertexDimensionTuples,
        Finset.mem_insert,
        Prod.mk.injEq]
      right; left
      exact ⟨hV, hV₁, hV₂, hV₃⟩
  · -- ker A₁ ≠ ⊥, V = V₂ = V₃ = 0: dim V₁ = 1
    have hV₁ := leafOne_finrank_eq_one_of_other_finrank_eq_zero ρ hind hV hV₂ hV₃
    simp only [FourVertexStarRepresentation.dimension, fourVertexDimensionTuples,
      Finset.mem_insert,
      Prod.mk.injEq]
    left
    exact ⟨hV, hV₁, hV₂, hV₃⟩

/-- The auxiliary finite set has cardinality twelve. -/
theorem auxiliary_finset_card_eq_twelve :
    fourVertexDimensionTuples.card = 12 := by
  decide

end RepresentationTheory.AuxiliaryFiniteSetMembership

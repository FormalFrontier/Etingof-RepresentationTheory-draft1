/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.FiniteGroupNormalSubgroups
import RepresentationTheory.Alignment.Attribute

open Fintype Subgroup
open RepresentationTheory.FiniteGroupNormalSubgroups

namespace RepresentationTheory.FiniteGroupSolvability

/-- A finite group whose order is a product of powers of two primes is solvable. -/
@[source_ref"Chapter2/Discussion_after_Theorem2.1.2/Derived5"(role:=primary),
  source_ref"Chapter5/Introduction_5.4"(role:=supporting),
  source_ref"Chapter5/Theorem5.4.3"(role:=primary),
  source_ref"Chapter5/Discussion_proof_of_Theorem5.4.3"(role:=supporting)]
theorem isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (G : Type) [Group G] [Fintype G]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (a b : ℕ) (hord : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  classical
  suffices key : ∀ n : ℕ, ∀ (H : Type) [Group H] [Fintype H] [DecidableEq H],
      Fintype.card H = n →
      (∀ r : ℕ, Nat.Prime r → r ∣ n → r = p ∨ r = q) →
      IsSolvable H by
    exact key _ G rfl (fun r hr hrd => by
      rw [hord] at hrd
      rcases hr.dvd_mul.mp hrd with h₁ | h₁
      · exact Or.inl ((hp.eq_one_or_self_of_dvd r (hr.dvd_of_dvd_pow h₁)).resolve_left
          hr.one_lt.ne')
      · exact Or.inr ((hq.eq_one_or_self_of_dvd r (hr.dvd_of_dvd_pow h₁)).resolve_left
          hr.one_lt.ne'))
  intro n
  induction n using Nat.strongRecOn with | ind n ih => ?_
  intro H _ _ _ hcard hdvd
  by_cases hn : n ≤ 1
  · have : Subsingleton H := by
      rwa [← Fintype.card_le_one_iff_subsingleton, hcard]
    exact @isSolvable_of_subsingleton H _ this
  push Not at hn
  haveI : Nontrivial H := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    omega
  by_cases hcomm : ∀ x y : H, x * y = y * x
  · exact isSolvable_of_comm hcomm
  push Not at hcomm
  have hcenter_ne_top : Subgroup.center H ≠ ⊤ := by
    intro h
    obtain ⟨x, y, hxy⟩ := hcomm
    exact hxy ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm)
  suffices ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ by
    obtain ⟨N, hN_normal, hN_bot, hN_top⟩ := this
    haveI := hN_normal
    have hN_dvd : Nat.card ↑N ∣ Nat.card H := card_subgroup_dvd_card N
    have hQ_dvd : Nat.card (H ⧸ N) ∣ Nat.card H := card_quotient_dvd_card N
    have hN_lt : Fintype.card ↑N < n := by
      have h1 : Nat.card ↑N ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos hN_dvd
      have h2 : Nat.card ↑N ≠ Nat.card H := fun h => hN_top (eq_top_of_card_eq N h)
      simp only [Nat.card_eq_fintype_card, hcard] at h1 h2
      omega
    have hQ_lt : Fintype.card (H ⧸ N) < n := by
      have h1 : Nat.card (H ⧸ N) ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos hQ_dvd
      have h2 : Nat.card (H ⧸ N) ≠ Nat.card H := by
        intro heq
        have hmul := card_eq_card_quotient_mul_card_subgroup N
        rw [heq] at hmul
        have hN_eq_1 : Nat.card ↑N = 1 := by
          have := Nat.card_pos (α := ↑N)
          have := Nat.card_pos (α := H)
          nlinarith [Nat.mul_le_mul_left (Nat.card H)
            (show 1 ≤ Nat.card ↑N by omega)]
        exact hN_bot (N.eq_bot_of_card_eq hN_eq_1)
      simp only [Nat.card_eq_fintype_card, hcard] at h1 h2
      omega
    have hN_dvd_ft : Fintype.card ↑N ∣ n := by
      rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hN_dvd
    have hQ_dvd_ft : Fintype.card (H ⧸ N) ∣ n := by
      rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hQ_dvd
    haveI : IsSolvable ↑N := ih _ hN_lt ↑N rfl fun r hr hrd =>
      hdvd r hr (dvd_trans hrd hN_dvd_ft)
    haveI : IsSolvable (H ⧸ N) := ih _ hQ_lt (H ⧸ N) rfl fun r hr hrd =>
      hdvd r hr (dvd_trans hrd hQ_dvd_ft)
    exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.subtype_range])
  by_cases hcenter_bot : Subgroup.center H = ⊥
  · have hcard_gt : 1 < Fintype.card H :=
      Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    obtain ⟨s, hs, hs_dvd⟩ : ∃ s, Nat.Prime s ∧ s ∣ Fintype.card H :=
      ⟨(Fintype.card H).minFac, Nat.minFac_prime (by omega),
        (Fintype.card H).minFac_dvd⟩
    haveI : Fact (Nat.Prime s) := ⟨hs⟩
    let S : Sylow s H := default
    have hs_dvd_nat : s ∣ Nat.card H := by
      rwa [Nat.card_eq_fintype_card]
    have hfact_pos : 0 < (Nat.card H).factorization s :=
      hs.factorization_pos_of_dvd
        (by rw [Nat.card_eq_fintype_card]; omega) hs_dvd_nat
    haveI : Nontrivial ↑S.1 := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card,
        S.card_eq_multiplicity]
      exact one_lt_pow₀ hs.one_lt hfact_pos.ne'
    haveI := IsPGroup.center_nontrivial S.isPGroup'
    obtain ⟨⟨⟨g_sub, hg_mem⟩, hg_center⟩, hg_ne⟩ :=
      exists_ne (1 : Subgroup.center S.1)
    set g : H := g_sub
    have hg1 : g ≠ 1 := fun h => hg_ne (Subtype.ext (Subtype.ext h))
    have hS_le_cent : S.1 ≤ Subgroup.centralizer ({g} : Set H) := by
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have := congr_arg Subtype.val
        (Subgroup.mem_center_iff.mp hg_center ⟨h, hh⟩)
      simpa using this.symm
    set cl := Fintype.card { h : H // IsConj g h }
    have hcl_gt : 1 < cl := by
      by_contra h
      push Not at h
      have hcl_pos : 0 < cl := @Fintype.card_pos _ _ ⟨⟨g, IsConj.refl g⟩⟩
      have hcl_one : cl = 1 := by omega
      have : g ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro y
        have : ∀ h : H, IsConj g h → h = g := by
          intro h hc
          have := Fintype.card_le_one_iff_subsingleton.mp (by omega : cl ≤ 1)
          exact Subtype.ext_iff.mp (this.allEq ⟨h, hc⟩ ⟨g, IsConj.refl g⟩)
        by_contra hne
        push Not at hne
        have hconj : IsConj g (y * g * y⁻¹) :=
          ⟨⟨y, y⁻¹, mul_inv_cancel y, inv_mul_cancel y⟩, by
            change y * g = y * g * y⁻¹ * y
            group⟩
        have heq := this _ hconj
        have : y * g = g * y := by
          have : y * g * y⁻¹ = g := heq
          calc
            y * g = y * g * y⁻¹ * y := by group
            _ = g * y := by rw [this]
        exact hne this
      rw [hcenter_bot] at this
      exact hg1 (Subgroup.mem_bot.mp this)
    have hcl_dvd : cl ∣ Fintype.card H := by
      have hcard_orb : cl = Fintype.card (MulAction.orbit (ConjAct H) g) := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquiv (Equiv.refl H) fun h =>
          ⟨fun hc => ConjAct.mem_orbit_conjAct.mpr hc.symm,
            fun hm => (ConjAct.mem_orbit_conjAct.mp hm).symm⟩
      rw [hcard_orb]
      have h_os :=
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct H) g
      change _ ∣ Fintype.card H
      exact ⟨Fintype.card ↑(MulAction.stabilizer (ConjAct H) g), h_os.symm⟩
    have hcl_coprime_s : ¬ (s ∣ cl) := by
      intro hs_dvd_cl
      have h_os :=
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct H) g
      have hcard_orb : Fintype.card (MulAction.orbit (ConjAct H) g) = cl :=
        (Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl H) fun h =>
          ⟨fun hc => ConjAct.mem_orbit_conjAct.mpr hc.symm,
            fun hm => (ConjAct.mem_orbit_conjAct.mp hm).symm⟩)).symm
      have hS_in_stab : ∀ x ∈ S.1,
          ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct H) g := by
        intro x hx
        rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def,
          ConjAct.ofConjAct_toConjAct]
        have := (Subgroup.mem_centralizer_iff.mp (hS_le_cent hx)) g
          (Set.mem_singleton g)
        exact mul_inv_eq_iff_eq_mul.mpr this.symm
      have hS_dvd_stab : Nat.card ↑S.1 ∣
          Nat.card ↑(MulAction.stabilizer (ConjAct H) g) :=
        Subgroup.card_dvd_of_injective
          { toFun := fun ⟨x, hx⟩ => ⟨ConjAct.toConjAct x, hS_in_stab x hx⟩
            map_one' := Subtype.ext (map_one ConjAct.toConjAct)
            map_mul' := fun ⟨a, _⟩ ⟨b, _⟩ =>
              Subtype.ext (map_mul ConjAct.toConjAct a b) }
          (fun ⟨a, _⟩ ⟨b, _⟩ h =>
            Subtype.ext (ConjAct.toConjAct.injective (Subtype.ext_iff.mp h)))
      have hcl_dvd_index : cl ∣ S.1.index := by
        rw [hcard_orb] at h_os
        have h_os' :
            cl * Nat.card ↑(MulAction.stabilizer (ConjAct H) g) = Nat.card H := by
          simp only [Nat.card_eq_fintype_card]
          exact h_os
        have h_lag := S.1.card_mul_index (G := H)
        obtain ⟨m, hm⟩ := hS_dvd_stab
        rw [hm, ← mul_assoc] at h_os'
        rw [← h_lag] at h_os'
        rw [mul_comm cl (Nat.card ↑S.1)] at h_os'
        rw [mul_assoc] at h_os'
        have hne : (Nat.card ↑S.1 : ℕ) ≠ 0 := Nat.card_pos.ne'
        exact ⟨m, (mul_left_cancel₀ hne h_os').symm⟩
      exact S.not_dvd_index (dvd_trans hs_dvd_cl hcl_dvd_index)
    have hcl_pos : cl ≠ 0 := by omega
    have hs_pq : s = p ∨ s = q := hdvd s hs (hcard ▸ hs_dvd)
    obtain ⟨t, ht, ht_dvd⟩ : ∃ t, Nat.Prime t ∧ t ∣ cl :=
      ⟨cl.minFac, Nat.minFac_prime (by omega), cl.minFac_dvd⟩
    have ht_ne_s : t ≠ s := fun h => hcl_coprime_s (h ▸ ht_dvd)
    have huniq : ∀ r, Nat.Prime r → r ∣ cl → r = t := by
      intro r hr hr_dvd
      have hr_dvd_H := dvd_trans hr_dvd hcl_dvd
      have hr_pq := hdvd r hr (hcard ▸ hr_dvd_H)
      have ht_pq := hdvd t ht (hcard ▸ dvd_trans ht_dvd hcl_dvd)
      have hr_ne_s : r ≠ s := fun h => hcl_coprime_s (h ▸ hr_dvd)
      rcases hr_pq with rfl | rfl <;> rcases ht_pq with rfl | rfl
      · rfl
      · rcases hs_pq with rfl | rfl
        · exact absurd rfl hr_ne_s
        · exact absurd rfl ht_ne_s
      · rcases hs_pq with rfl | rfl
        · exact absurd rfl ht_ne_s
        · exact absurd rfl hr_ne_s
      · rfl
    have hcl_eq := Nat.eq_prime_pow_of_unique_prime_dvd hcl_pos fun {d} hd hd_dvd =>
      huniq d hd hd_dvd
    set k := cl.primeFactorsList.length
    have hk_pos : 0 < k := by
      by_contra h
      push Not at h
      have hk0 : k = 0 := by omega
      rw [hcl_eq, hk0, pow_zero] at hcl_gt
      omega
    exact exists_nontrivial_proper_normalSubgroup_of_conjClassCard_eq_prime_pow
      H t ht k hk_pos g hcl_eq
  · exact ⟨Subgroup.center H, inferInstance, hcenter_bot, hcenter_ne_top⟩

end RepresentationTheory.FiniteGroupSolvability

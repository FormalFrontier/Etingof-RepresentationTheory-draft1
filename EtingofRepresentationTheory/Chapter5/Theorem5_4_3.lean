import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_4_6

/-!
# Theorem 5.4.3: Burnside's Theorem

Any group of order p^a · q^b, where p, q are primes and a, b ≥ 0, is solvable.

The proof uses representation theory: specifically Theorem 5.4.6 (conjugacy classes
of prime power size force normal subgroups) combined with induction on the order of G.
-/

open Fintype Subgroup

/-- Burnside's theorem: any group of order p^a · q^b (p, q prime) is solvable.
(Etingof Theorem 5.4.3) -/
theorem Etingof.Theorem5_4_3
    (G : Type) [Group G] [Fintype G]
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (a b : ℕ) (hord : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  classical
  -- Strong induction on |G| via a prime-divisor reformulation
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
  -- Base: trivial group
  by_cases hn : n ≤ 1
  · have : Subsingleton H := by rwa [← Fintype.card_le_one_iff_subsingleton, hcard]
    exact @isSolvable_of_subsingleton H _ this
  push_neg at hn
  haveI : Nontrivial H := by
    rw [← Fintype.one_lt_card_iff_nontrivial]; omega
  -- Abelian → solvable
  by_cases hcomm : ∀ x y : H, x * y = y * x
  · exact isSolvable_of_comm hcomm
  push_neg at hcomm
  -- Non-abelian: find proper nontrivial normal subgroup
  -- Center is not all of H
  have hcenter_ne_top : Subgroup.center H ≠ ⊤ := by
    intro h
    obtain ⟨x, y, hxy⟩ := hcomm
    exact hxy ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm)
  -- Either center works, or we need Sylow + Theorem 5.4.6
  suffices ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ by
    -- Extension: N and H/N solvable by IH ⟹ H solvable
    obtain ⟨N, hN_normal, hN_bot, hN_top⟩ := this
    haveI := hN_normal
    have hN_dvd : Nat.card ↥N ∣ Nat.card H := card_subgroup_dvd_card N
    have hQ_dvd : Nat.card (H ⧸ N) ∣ Nat.card H := card_quotient_dvd_card N
    have hN_lt : Fintype.card ↥N < n := by
      have h1 : Nat.card ↥N ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos hN_dvd
      have h2 : Nat.card ↥N ≠ Nat.card H := fun h => hN_top (eq_top_of_card_eq N h)
      simp only [Nat.card_eq_fintype_card, hcard] at h1 h2; omega
    have hQ_lt : Fintype.card (H ⧸ N) < n := by
      have h1 : Nat.card (H ⧸ N) ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos hQ_dvd
      have h2 : Nat.card (H ⧸ N) ≠ Nat.card H := by
        intro heq
        have hmul := card_eq_card_quotient_mul_card_subgroup N
        rw [heq] at hmul
        -- hmul : Nat.card H = Nat.card H * Nat.card ↥N
        have hN_eq_1 : Nat.card ↥N = 1 := by
          have := Nat.card_pos (α := ↥N)
          have := Nat.card_pos (α := H)
          nlinarith [Nat.mul_le_mul_left (Nat.card H) (show 1 ≤ Nat.card ↥N by omega)]
        exact hN_bot (N.eq_bot_of_card_eq hN_eq_1)
      simp only [Nat.card_eq_fintype_card, hcard] at h1 h2; omega
    have hN_dvd_ft : Fintype.card ↥N ∣ n := by
      rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hN_dvd
    have hQ_dvd_ft : Fintype.card (H ⧸ N) ∣ n := by
      rw [← hcard, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hQ_dvd
    haveI : IsSolvable ↥N := ih _ hN_lt ↥N rfl fun r hr hrd =>
      hdvd r hr (dvd_trans hrd hN_dvd_ft)
    haveI : IsSolvable (H ⧸ N) := ih _ hQ_lt (H ⧸ N) rfl fun r hr hrd =>
      hdvd r hr (dvd_trans hrd hQ_dvd_ft)
    exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.subtype_range])
  -- Find proper nontrivial normal subgroup
  by_cases hcenter_bot : Subgroup.center H = ⊥
  · -- Center trivial ⟹ use Sylow + Theorem 5.4.6
    -- Pick a prime s dividing |H|
    have hcard_gt : 1 < Fintype.card H := Fintype.one_lt_card_iff_nontrivial.mpr ‹_›
    obtain ⟨s, hs, hs_dvd⟩ : ∃ s, Nat.Prime s ∧ s ∣ Fintype.card H :=
      ⟨(Fintype.card H).minFac, Nat.minFac_prime (by omega), (Fintype.card H).minFac_dvd⟩
    haveI : Fact (Nat.Prime s) := ⟨hs⟩
    -- Sylow s-subgroup
    let S : Sylow s H := default
    -- S is nontrivial (s | |H| ⟹ |S| = s^k with k ≥ 1)
    have hs_dvd_nat : s ∣ Nat.card H := by rwa [Nat.card_eq_fintype_card]
    have hfact_pos : 0 < (Nat.card H).factorization s :=
      hs.factorization_pos_of_dvd (by rw [Nat.card_eq_fintype_card]; omega) hs_dvd_nat
    haveI : Nontrivial ↥S.1 := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card,
          S.card_eq_multiplicity]
      exact one_lt_pow₀ hs.one_lt hfact_pos.ne'
    -- Z(S) is nontrivial (S is a p-group)
    haveI := IsPGroup.center_nontrivial S.isPGroup'
    -- Pick g ∈ Z(S), g ≠ 1
    obtain ⟨⟨⟨g_sub, hg_mem⟩, hg_center⟩, hg_ne⟩ := exists_ne (1 : Subgroup.center S.1)
    set g : H := g_sub
    have hg1 : g ≠ 1 := fun h => hg_ne (Subtype.ext (Subtype.ext h))
    -- g commutes with all of S, so S.1 ≤ centralizer {g}
    have hS_le_cent : S.1 ≤ Subgroup.centralizer ({g} : Set H) := by
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
      have := congr_arg Subtype.val (Subgroup.mem_center_iff.mp hg_center ⟨h, hh⟩)
      simpa using this.symm
    -- Conjugacy class size
    set cl := Fintype.card { h : H // IsConj g h }
    -- cl > 1 (g ∉ center since center is trivial)
    have hcl_gt : 1 < cl := by
      by_contra h; push_neg at h
      have hcl_pos : 0 < cl := @Fintype.card_pos _ _ ⟨⟨g, IsConj.refl g⟩⟩
      have hcl_one : cl = 1 := by omega
      -- If conjugacy class has size 1, g is in the center
      have : g ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]; intro y
        have : ∀ h : H, IsConj g h → h = g := by
          intro h hc
          have := Fintype.card_le_one_iff_subsingleton.mp (by omega : cl ≤ 1)
          exact Subtype.ext_iff.mp (this.allEq ⟨h, hc⟩ ⟨g, IsConj.refl g⟩)
        by_contra hne; push_neg at hne
        have hconj : IsConj g (y * g * y⁻¹) :=
          ⟨⟨y, y⁻¹, mul_inv_cancel y, inv_mul_cancel y⟩, by
            show y * g = y * g * y⁻¹ * y; group⟩
        have heq := this _ hconj
        have : y * g = g * y := by
          have : y * g * y⁻¹ = g := heq
          calc y * g = y * g * y⁻¹ * y := by group
            _ = g * y := by rw [this]
        exact hne this
      rw [hcenter_bot] at this
      exact hg1 (Subgroup.mem_bot.mp this)
    -- cl divides |H| (orbit-stabilizer via ConjAct)
    have hcl_dvd : cl ∣ Fintype.card H := by
      have hcard_orb : cl = Fintype.card (MulAction.orbit (ConjAct H) g) := by
        apply Fintype.card_congr
        exact Equiv.subtypeEquiv (Equiv.refl H) fun h =>
          ⟨fun hc => ConjAct.mem_orbit_conjAct.mpr hc.symm,
           fun hm => (ConjAct.mem_orbit_conjAct.mp hm).symm⟩
      rw [hcard_orb]
      have h_os := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct H) g
      -- h_os : card orbit * card stab = card (ConjAct H), but ConjAct H = H as types
      change _ ∣ Fintype.card H
      exact ⟨Fintype.card ↥(MulAction.stabilizer (ConjAct H) g), h_os.symm⟩
    -- cl is coprime to s (because S ≤ centralizer, so cl divides [H:S] which is coprime to s)
    have hcl_coprime_s : ¬(s ∣ cl) := by
      intro hs_dvd_cl
      -- Orbit-stabilizer: card(orbit) * card(stab) = card(ConjAct H) = card(H)
      have h_os := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct H) g
      have hcard_orb : Fintype.card (MulAction.orbit (ConjAct H) g) = cl :=
        (Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl H) fun h =>
          ⟨fun hc => ConjAct.mem_orbit_conjAct.mpr hc.symm,
           fun hm => (ConjAct.mem_orbit_conjAct.mp hm).symm⟩)).symm
      -- S maps into the stabilizer via ConjAct.toConjAct
      have hS_in_stab : ∀ x ∈ S.1,
          ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct H) g := by
        intro x hx
        rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
        have := (Subgroup.mem_centralizer_iff.mp (hS_le_cent hx)) g (Set.mem_singleton g)
        -- this : g * x = x * g, need: x * g * x⁻¹ = g
        exact mul_inv_eq_iff_eq_mul.mpr this.symm
      -- card(S) ∣ card(stabilizer) via injective hom
      have hS_dvd_stab : Nat.card ↥S.1 ∣
          Nat.card ↥(MulAction.stabilizer (ConjAct H) g) :=
        Subgroup.card_dvd_of_injective
          { toFun := fun ⟨x, hx⟩ => ⟨ConjAct.toConjAct x, hS_in_stab x hx⟩,
            map_one' := Subtype.ext (map_one ConjAct.toConjAct),
            map_mul' := fun ⟨a, _⟩ ⟨b, _⟩ => Subtype.ext (map_mul ConjAct.toConjAct a b) }
          (fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (ConjAct.toConjAct.injective (Subtype.ext_iff.mp h)))
      -- Arithmetic: cl * card_stab = card_H, card_S ∣ card_stab, card_S * index = card_H
      -- So cl ∣ S.1.index
      have hcl_dvd_index : cl ∣ S.1.index := by
        -- Convert orbit-stabilizer to Nat.card
        rw [hcard_orb] at h_os
        -- h_os : cl * Fintype.card (stabilizer) = Fintype.card (ConjAct H)
        have h_os' : cl * Nat.card ↥(MulAction.stabilizer (ConjAct H) g) = Nat.card H := by
          simp only [Nat.card_eq_fintype_card]; exact h_os
        -- Lagrange: card(S) * index(S) = card(H)
        have h_lag := S.1.card_mul_index (G := H)
        -- card(S) ∣ card(stab), so stab = card(S) * m
        obtain ⟨m, hm⟩ := hS_dvd_stab
        -- cl * (card_S * m) = card_S * index
        rw [hm, ← mul_assoc] at h_os'
        rw [← h_lag] at h_os'
        -- h_os' : cl * Nat.card S.1 * m = Nat.card S.1 * S.1.index
        rw [mul_comm cl (Nat.card ↥S.1)] at h_os'
        -- h_os' : Nat.card S.1 * cl * m = Nat.card S.1 * S.1.index
        rw [mul_assoc] at h_os'
        have hne : (Nat.card ↥S.1 : ℕ) ≠ 0 := Nat.card_pos.ne'
        exact ⟨m, (mul_left_cancel₀ hne h_os').symm⟩
      exact S.not_dvd_index (dvd_trans hs_dvd_cl hcl_dvd_index)
    -- All prime divisors of cl divide |H| and are ≠ s, hence = the other prime
    have hcl_pos : cl ≠ 0 := by omega
    -- s ∈ {p, q} (s is a prime dividing |H|)
    have hs_pq : s = p ∨ s = q := hdvd s hs (hcard ▸ hs_dvd)
    -- Get the "other" prime t from any prime divisor of cl
    obtain ⟨t, ht, ht_dvd⟩ : ∃ t, Nat.Prime t ∧ t ∣ cl :=
      ⟨cl.minFac, Nat.minFac_prime (by omega), cl.minFac_dvd⟩
    have ht_ne_s : t ≠ s := fun h => hcl_coprime_s (h ▸ ht_dvd)
    -- All prime divisors of cl equal t
    have huniq : ∀ r, Nat.Prime r → r ∣ cl → r = t := by
      intro r hr hr_dvd
      have hr_dvd_H := dvd_trans hr_dvd hcl_dvd
      have hr_pq := hdvd r hr (hcard ▸ hr_dvd_H)
      have ht_pq := hdvd t ht (hcard ▸ dvd_trans ht_dvd hcl_dvd)
      have hr_ne_s : r ≠ s := fun h => hcl_coprime_s (h ▸ hr_dvd)
      rcases hr_pq with rfl | rfl <;> rcases ht_pq with rfl | rfl
      · rfl
      · -- r = p, t = q; s must equal one of them, giving contradiction
        rcases hs_pq with rfl | rfl
        · exact absurd rfl hr_ne_s
        · exact absurd rfl ht_ne_s
      · rcases hs_pq with rfl | rfl
        · exact absurd rfl ht_ne_s
        · exact absurd rfl hr_ne_s
      · rfl
    -- cl = t^k
    have hcl_eq := Nat.eq_prime_pow_of_unique_prime_dvd hcl_pos fun {d} hd hd_dvd =>
      huniq d hd hd_dvd
    set k := cl.primeFactorsList.length
    have hk_pos : 0 < k := by
      by_contra h; push_neg at h
      have hk0 : k = 0 := by omega
      rw [hcl_eq, hk0, pow_zero] at hcl_gt
      omega
    -- Apply Theorem 5.4.6
    exact Etingof.Theorem5_4_6 H t ht k hk_pos g hcl_eq
  · -- Center nontrivial ⟹ use center
    exact ⟨Subgroup.center H, inferInstance, hcenter_bot, hcenter_ne_top⟩

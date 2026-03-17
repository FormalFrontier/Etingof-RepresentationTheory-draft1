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
    sorry
  · -- Center nontrivial ⟹ use center
    exact ⟨Subgroup.center H, inferInstance, hcenter_bot, hcenter_ne_top⟩

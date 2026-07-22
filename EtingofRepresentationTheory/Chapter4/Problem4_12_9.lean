import Mathlib
import EtingofRepresentationTheory.Chapter4.Problem4_12_2

/-!
# Problem 4.12.9: characters and tensor products for the Heisenberg group

**Problem 4.12.9.** Find the characters and tensor products of irreducible complex
representations of the Heisenberg group from Problem 4.12.2.

## Formalization

We reuse the Heisenberg group `Heisenberg p` and its generators from Problem 4.12.2. Recall
(4.12.2) that the irreducibles are the `p²` one-dimensional characters and, for each `p`-th
root of unity `z ≠ 1`, a `p`-dimensional representation `R_z` on `V = ZMod p → ℂ` determined by
`(ρ xGen f)(t) = f(t-1)`, `(ρ yGen f)(t) = z^t · f(t)`. The predicate `IsRz z ρ` records that
`ρ` realizes `R_z`.

A short computation with the two generators shows `ρ(⟨0,0,1⟩) = z⁻¹ · id` (the central
character), so:

* `character_Rz`: the character of `R_z` (`z ≠ 1`) vanishes off the center and equals
  `p · z^{-c}` on a central element `⟨0,0,c⟩`:
  `tr ρ(⟨a,b,c⟩) = if a = 0 ∧ b = 0 then p · (z⁻¹)^c else 0`.
* `tensor_character_mul` (tensor products): since the character of a tensor product is the
  product of characters, for `p`-th roots `z, w` with `z, w ≠ 1`:
  - if `z·w ≠ 1`, then `χ_{R_z}·χ_{R_w} = p · χ_{R_{zw}}`, i.e. `R_z ⊗ R_w ≅ p · R_{zw}`
    (`tensor_character_nonone`);
  - if `z·w = 1`, then `χ_{R_z}·χ_{R_w}` equals `p²` on the center and `0` elsewhere: the
    character of `⨁` of all `p²` one-dimensional representations, each occurring once
    (`tensor_character_inv`).

The one-dimensional characters (there are `p²` of them) are classified in Problem 4.12.2
(`one_dim_reps_card`); the tensor product of a character with any irreducible just twists it.
-/

noncomputable section

open Etingof.Problem4_12_2 Etingof.Problem4_12_2.Heisenberg

namespace Etingof.Problem4_12_9

variable {p : ℕ}

/-- `IsRz z ρ` says the representation `ρ` on `V = ZMod p → ℂ` realizes `R_z`: it acts on the
generators by the shift and the multiplication-by-`z^t` operators. -/
def IsRz (z : ℂ) (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) : Prop :=
  (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (xGen p) f) t = f (t - 1)) ∧
  (∀ (f : ZMod p → ℂ) (t : ZMod p), (ρ (yGen p) f) t = z ^ t.val * f t)

/-- Any `ρ` realizing `R_z` is *the* representation `rhoHom z hz` of Problem 4.12.2, by the
uniqueness half of `exists_unique_rep`. -/
theorem isRz_eq_rhoHom [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (hρ : IsRz z ρ) :
    ρ = rhoHom z hz := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨w, _hw, huniq⟩ := exists_unique_rep z hz
  rw [huniq ρ hρ,
    huniq (rhoHom z hz) ⟨fun f t => rhoHom_xGen z hz f t, fun f t => rhoHom_yGen z hz f t⟩]

/-- For a nontrivial `p`-th root of unity `z`, the geometric sum `∑_{u ∈ ZMod p} z^{u.val}`
vanishes: multiplying by `z` permutes the summands (`u ↦ u+1`), so the sum is `z`-invariant,
hence `(z-1)·S = 0` and `S = 0`. -/
theorem sum_zpow_val_eq_zero [Fact p.Prime] {z : ℂ} (hz : z ^ p = 1) (hz1 : z ≠ 1) :
    ∑ u : ZMod p, z ^ u.val = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have step : ∀ u : ZMod p, z * z ^ u.val = z ^ (u + 1).val := by
    intro u
    rw [← pow_succ', ZMod.val_add, ZMod.val_one, zpow_mod hz]
  have key : z * (∑ u : ZMod p, z ^ u.val) = ∑ u : ZMod p, z ^ u.val :=
    calc z * (∑ u : ZMod p, z ^ u.val)
        = ∑ u : ZMod p, z * z ^ u.val := by rw [Finset.mul_sum]
      _ = ∑ u : ZMod p, z ^ (u + 1).val := Finset.sum_congr rfl (fun u _ => step u)
      _ = ∑ v : ZMod p, z ^ v.val :=
            Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _ (fun _ => rfl)
  have h0 : (z - 1) * (∑ u : ZMod p, z ^ u.val) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hz1
  · exact h

/-- `z^{(-c).val} = (z⁻¹)^{c.val}` for a `p`-th root of unity `z`: the exponents `(-c).val` and
`c.val` sum to `0` modulo `p`, so `z^{(-c).val}·z^{c.val} = 1`. -/
theorem zpow_neg_val [NeZero p] {z : ℂ} (hz : z ^ p = 1) (c : ZMod p) :
    z ^ ((-c).val) = (z⁻¹) ^ c.val := by
  have hmod : ((-c).val + c.val) % p = 0 := by
    have h := ZMod.val_add (-c) c
    rw [neg_add_cancel, ZMod.val_zero] at h
    exact h.symm
  have hmul : z ^ ((-c).val) * z ^ c.val = 1 := by
    rw [← pow_add, ← zpow_mod hz ((-c).val + c.val), hmod, pow_zero]
  rw [inv_pow, eq_comm]
  exact inv_eq_of_mul_eq_one_left hmul

/-- The trace of the operator `rhoLin z g` on `V = ZMod p → ℂ`. Only the diagonal survives, and
it is nonzero only when `g.a = 0`; then the geometric sum over the fibre kills it unless also
`g.b = 0`, in which case the operator is the scalar `z^{-g.c}` on a `p`-dimensional space. -/
theorem trace_rhoLin [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (g : Heisenberg p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (rhoLin z g) =
      if g.a = 0 ∧ g.b = 0 then (p : ℂ) * (z⁻¹) ^ g.c.val else 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ZMod p))]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_repr, Pi.basisFun_apply, rhoLin_apply, Pi.single_apply, sub_eq_self]
  rw [← Finset.sum_mul]
  by_cases ha : g.a = 0
  · rw [if_pos ha, mul_one]
    by_cases hb : g.b = 0
    · rw [if_pos ⟨ha, hb⟩, hb]
      simp only [zero_mul, zero_sub]
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, zpow_neg_val hz g.c]
    · rw [if_neg (fun h => hb h.2),
        Fintype.sum_equiv ((Equiv.mulLeft₀ g.b hb).trans (Equiv.subRight g.c))
          (fun i => z ^ (g.b * i - g.c).val) (fun u => z ^ u.val) (fun _ => rfl)]
      exact sum_zpow_val_eq_zero hz hz1
  · rw [if_neg ha, mul_zero, if_neg (fun h => ha h.1)]

/-- **Character of `R_z`.** For a `p`-th root of unity `z ≠ 1`, the character of `R_z`
vanishes off the center and takes the value `p · z^{-c}` on the central element `⟨0,0,c⟩`. -/
theorem character_Rz [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (hρ : IsRz z ρ)
    (a b c : ZMod p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) =
      if a = 0 ∧ b = 0 then (p : ℂ) * (z⁻¹) ^ c.val else 0 := by
  rw [isRz_eq_rhoHom z hz ρ hρ, rhoHom_apply]
  exact trace_rhoLin z hz hz1 ⟨a, b, c⟩

/-- **Tensor product `R_z ⊗ R_w`, generic case (`z·w ≠ 1`).** The character of the tensor
product (the pointwise product of characters) equals `p` times the character of `R_{zw}`,
i.e. `R_z ⊗ R_w ≅ p · R_{zw}`. -/
theorem tensor_character_nonone [Fact p.Prime]
    (z w : ℂ) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w ≠ 1)
    (ρz ρw ρzw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw) (hρzw : IsRz (z * w) ρzw)
    (g : Heisenberg p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρz g) *
        LinearMap.trace ℂ (ZMod p → ℂ) (ρw g) =
      (p : ℂ) * LinearMap.trace ℂ (ZMod p → ℂ) (ρzw g) := by
  obtain ⟨a, b, c⟩ := g
  rw [character_Rz z hz hz1 ρz hρz a b c,
      character_Rz w hw hw1 ρw hρw a b c,
      character_Rz (z * w) (by rw [mul_pow, hz, hw, mul_one]) hzw ρzw hρzw a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    rw [mul_inv, mul_pow]; ring
  · simp only [if_neg h, mul_zero]

/-- **Tensor product `R_z ⊗ R_{z⁻¹}` (`z·w = 1`).** The character of the tensor product equals
`p²` on the center and `0` elsewhere: this is the character of the direct sum of all `p²`
one-dimensional representations, each occurring exactly once. -/
theorem tensor_character_inv [Fact p.Prime]
    (z w : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z * w = 1)
    (ρz ρw : Representation ℂ (Heisenberg p) (ZMod p → ℂ))
    (hρz : IsRz z ρz) (hρw : IsRz w ρw)
    (a b c : ZMod p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρz ⟨a, b, c⟩) *
        LinearMap.trace ℂ (ZMod p → ℂ) (ρw ⟨a, b, c⟩) =
      if a = 0 ∧ b = 0 then (p : ℂ) ^ 2 else 0 := by
  have hw : w ^ p = 1 := by
    have hzwp : (z * w) ^ p = 1 := by rw [hzw, one_pow]
    rw [mul_pow, hz, one_mul] at hzwp; exact hzwp
  rw [character_Rz z hz hz1 ρz hρz a b c,
      character_Rz w hw hw1 ρw hρw a b c]
  by_cases h : a = 0 ∧ b = 0
  · simp only [if_pos h]
    have hone : (z⁻¹) ^ c.val * (w⁻¹) ^ c.val = 1 := by
      rw [← mul_pow, ← mul_inv, hzw, inv_one, one_pow]
    rw [show ((p : ℂ) * (z⁻¹) ^ c.val) * ((p : ℂ) * (w⁻¹) ^ c.val)
          = (p : ℂ) ^ 2 * ((z⁻¹) ^ c.val * (w⁻¹) ^ c.val) from by ring, hone, mul_one]
  · simp only [if_neg h, mul_zero]

end Etingof.Problem4_12_9

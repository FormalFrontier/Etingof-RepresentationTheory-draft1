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
  - if `z·w = 1`, then `χ_{R_z}·χ_{R_w}` equals `p²` on the center and `0` elsewhere — the
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

/-- **Character of `R_z`.** For a `p`-th root of unity `z ≠ 1`, the character of `R_z`
vanishes off the center and takes the value `p · z^{-c}` on the central element `⟨0,0,c⟩`. -/
theorem character_Rz [Fact p.Prime] (z : ℂ) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (ρ : Representation ℂ (Heisenberg p) (ZMod p → ℂ)) (hρ : IsRz z ρ)
    (a b c : ZMod p) :
    LinearMap.trace ℂ (ZMod p → ℂ) (ρ ⟨a, b, c⟩) =
      if a = 0 ∧ b = 0 then (p : ℂ) * (z⁻¹) ^ c.val else 0 := by
  sorry

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
  sorry

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
  sorry

end Etingof.Problem4_12_9

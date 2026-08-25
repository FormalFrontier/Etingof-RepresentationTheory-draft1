import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1
import EtingofRepresentationTheory.Chapter5.Remark5_8_3

/-!
# Theorem 5.9.1: coset-representative form of the Frobenius formula

`Etingof.Theorem5_9_1` proves the Frobenius formula in its *averaged* form, a sum over all of `G`
divided by `|H|`:

  `χ_{Ind V}(g) = (1/|H|) · Σ_{x ∈ G : x g x⁻¹ ∈ H} χ_V(x g x⁻¹)`.

Etingof's Theorem 5.9.1 states the formula in its *source* form, a sum over the right cosets
`H \ G` using a chosen representative `x_σ` of each coset:

  `χ_{Ind V}(g) = Σ_{σ ∈ H\G : x_σ g x_σ⁻¹ ∈ H} χ_V(x_σ g x_σ⁻¹)`.

This file supplies the missing source form and the proved bridge between the two.

## Contents

* `Etingof.frobeniusSummand_smul_left`: the summand `x ↦ [x g x⁻¹ ∈ H] · χ_V(x g x⁻¹)` is
  unchanged when `x` is left-multiplied by an element of `H`. This is the class-function /
  conjugation-invariance fact underlying representative-independence.
* `Etingof.frobeniusSummand_congr`: consequently the summand depends only on the right `H`-coset of
  `x`, so any choice of coset representative gives the same value.
* `Etingof.frobenius_coset_bridge`: for any function `F` constant on right `H`-cosets,
  `(1/|H|) · Σ_{x ∈ G} F x = Σ_{σ ∈ H\G} F x_σ` (representatives via `Quotient.out`). This is the
  purely combinatorial coset-counting identity.
* `Etingof.Theorem5_9_1_coset`: the Frobenius formula in the source's sum-over-`H\G` form,
  obtained by applying the bridge to `Etingof.Theorem5_9_1`.

Right cosets are modelled by `Quotient (QuotientGroup.rightRel H)`, and coset representatives by
`Quotient.out`, exactly as in `Etingof.Remark5_8_3` (whose `cosetTwist` is reused here).
-/

open Representation

namespace Etingof

variable {G : Type*} [Group G] [Fintype G]
  (H : Subgroup G) [DecidablePred (· ∈ H)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
  (ρ : Representation ℂ H V)

omit [Fintype G] [Module.Finite ℂ V] in
/-- **Frobenius summand is `H`-left-invariant.** The Frobenius summand
`x ↦ [x g x⁻¹ ∈ H] · χ_V(x g x⁻¹)` is unchanged when `x` is replaced by `h₀ · x` for `h₀ ∈ H`.

Both the membership condition and the character value are preserved: conjugating `x g x⁻¹` by
`h₀ ∈ H` stays in `H`, and `χ_V` is a class function on `H`. This is the content that makes the
summand independent of the choice of right-coset representative. -/
theorem frobeniusSummand_smul_left (g : G) (h₀ : H) (x : G) :
    (if h : (↑h₀ * x) * g * (↑h₀ * x)⁻¹ ∈ H then
        LinearMap.trace ℂ V (ρ ⟨(↑h₀ * x) * g * (↑h₀ * x)⁻¹, h⟩) else 0)
      = (if h : x * g * x⁻¹ ∈ H then
        LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩) else 0) := by
  have hconj : (↑h₀ * x) * g * (↑h₀ * x)⁻¹ = ↑h₀ * (x * g * x⁻¹) * (↑h₀ : G)⁻¹ := by group
  have hiff : (↑h₀ * x) * g * (↑h₀ * x)⁻¹ ∈ H ↔ x * g * x⁻¹ ∈ H := by
    rw [hconj]
    constructor
    · intro hc
      have h1 : (↑h₀ : G)⁻¹ * (↑h₀ * (x * g * x⁻¹) * (↑h₀ : G)⁻¹) * ↑h₀ = x * g * x⁻¹ := by group
      rw [← h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem h₀.2) hc) h₀.2
    · intro hx
      exact H.mul_mem (H.mul_mem h₀.2 hx) (H.inv_mem h₀.2)
  by_cases hx : x * g * x⁻¹ ∈ H
  · rw [dif_pos (hiff.mpr hx), dif_pos hx]
    set a : H := ⟨x * g * x⁻¹, hx⟩ with ha
    have hsub : (⟨(↑h₀ * x) * g * (↑h₀ * x)⁻¹, hiff.mpr hx⟩ : H) = h₀ * a * h₀⁻¹ := by
      apply Subtype.ext
      change (↑h₀ * x) * g * (↑h₀ * x)⁻¹ = ↑h₀ * (x * g * x⁻¹) * (↑h₀ : G)⁻¹
      exact hconj
    rw [hsub, map_mul ρ (h₀ * a) h₀⁻¹, map_mul ρ h₀ a, LinearMap.trace_mul_cycle,
      ← map_mul ρ h₀⁻¹ h₀, inv_mul_cancel, map_one, one_mul]
  · rw [dif_neg (fun hc => hx (hiff.mp hc)), dif_neg hx]

omit [Fintype G] [Module.Finite ℂ V] in
/-- **The Frobenius summand depends only on the right `H`-coset.** If `x` and `y` lie in the same
right coset `H \ G`, then the Frobenius summands at `x` and `y` agree. In particular the
sum-over-`H\G` form of the Frobenius formula is independent of the chosen coset representatives. -/
theorem frobeniusSummand_congr (g : G) {x y : G}
    (hxy : (Quotient.mk'' x : Quotient (QuotientGroup.rightRel H)) = Quotient.mk'' y) :
    (if h : x * g * x⁻¹ ∈ H then LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩) else 0)
      = (if h : y * g * y⁻¹ ∈ H then LinearMap.trace ℂ V (ρ ⟨y * g * y⁻¹, h⟩) else 0) := by
  have hrel : y * x⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.eq''.mp hxy)
  have hyx : ((⟨y * x⁻¹, hrel⟩ : H) : G) * x = y := by
    change (y * x⁻¹) * x = y
    group
  rw [← hyx, frobeniusSummand_smul_left]

/-- **Coset-counting bridge.** For any `F : G → ℂ` that is constant on right `H`-cosets (i.e.
`F (h₀ · x) = F x` for `h₀ ∈ H`), averaging `F` over `G` equals summing `F` over a set of
right-coset representatives (chosen as `Quotient.out`):

  `(1/|H|) · Σ_{x ∈ G} F x = Σ_{σ ∈ H\G} F x_σ`.

Each right coset has exactly `|H|` elements on which `F` is constant, so the sum over `G` counts
each coset's value `|H|` times. -/
theorem frobenius_coset_bridge [Fintype (Quotient (QuotientGroup.rightRel H))]
    (F : G → ℂ) (hF : ∀ (h₀ : H) (x : G), F (↑h₀ * x) = F x) :
    (Fintype.card H : ℂ)⁻¹ * ∑ x : G, F x
      = ∑ q : Quotient (QuotientGroup.rightRel H), F q.out := by
  classical
  have hbij : Function.Bijective
      (fun p : H × Quotient (QuotientGroup.rightRel H) => (↑p.1 * p.2.out : G)) := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x => (cosetTwist H x, Quotient.mk'' x), ?_, ?_⟩
    · rintro ⟨h, q⟩
      have hmk : (Quotient.mk'' (↑h * q.out) : Quotient (QuotientGroup.rightRel H)) = q := by
        have hrel : (Quotient.mk'' (↑h * q.out) : Quotient (QuotientGroup.rightRel H))
            = Quotient.mk'' q.out :=
          Quotient.eq''.mpr (QuotientGroup.rightRel_apply.mpr (by
            have hs : q.out * (↑h * q.out)⁻¹ = ((↑h : G))⁻¹ := by group
            rw [hs]; exact inv_mem h.2))
        rw [hrel, Quotient.out_eq']
      have htw : cosetTwist H (↑h * q.out) = h := by
        apply Subtype.ext
        rw [cosetTwist_coe, show (Quotient.mk'' (↑h * q.out)
            : Quotient (QuotientGroup.rightRel H)).out = q.out from by rw [hmk]]
        group
      change (cosetTwist H (↑h * q.out), Quotient.mk'' (↑h * q.out)) = (h, q)
      rw [Prod.mk.injEq]
      exact ⟨htw, hmk⟩
    · intro x
      change (↑(cosetTwist H x) : G) * (Quotient.mk'' x).out = x
      rw [cosetTwist_coe]; group
  have hsum : ∑ x : G, F x
      = ∑ p : H × Quotient (QuotientGroup.rightRel H), F (↑p.1 * p.2.out) :=
    (Fintype.sum_bijective _ hbij (fun p => F (↑p.1 * p.2.out)) F (fun _ => rfl)).symm
  rw [hsum, Fintype.sum_prod_type]
  simp_rw [hF]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := H)).ne'), one_mul]

set_option linter.unusedFintypeInType false in
/-- **Frobenius formula, source (coset-representative) form** (Etingof Theorem 5.9.1).

The character of the induced representation `Ind_H^G V` at `g` is a sum over the right cosets
`H \ G`, using a representative `x_σ = σ.out` of each coset:

  `χ_{Ind V}(g) = Σ_{σ ∈ H\G : x_σ g x_σ⁻¹ ∈ H} χ_V(x_σ g x_σ⁻¹)`.

By `Etingof.frobeniusSummand_congr` the summand is independent of the choice of representative, so
this is Etingof's displayed formula. It is proved equal to the averaged form
`Etingof.Theorem5_9_1` via the coset-counting bridge `Etingof.frobenius_coset_bridge`. -/
theorem Theorem5_9_1_coset [Fintype (Quotient (QuotientGroup.rightRel H))] (g : G) :
    LinearMap.trace ℂ (Representation.IndV H.subtype ρ)
        (Etingof.Definition5_8_1 H ρ g)
      = ∑ q : Quotient (QuotientGroup.rightRel H),
          if h : q.out * g * q.out⁻¹ ∈ H then
            LinearMap.trace ℂ V (ρ ⟨q.out * g * q.out⁻¹, h⟩)
          else 0 := by
  rw [Etingof.Theorem5_9_1 H ρ g]
  exact frobenius_coset_bridge H
    (fun x => if h : x * g * x⁻¹ ∈ H then LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩) else 0)
    (fun h₀ x => frobeniusSummand_smul_left H ρ g h₀ x)

end Etingof

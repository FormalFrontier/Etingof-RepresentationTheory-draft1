import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.TraceCoinvariants

/-!
# Theorem 5.9.1: Frobenius Formula for Induced Characters

For `H ⊆ G`, a representation `V` of `H`, and `g ∈ G`, the character of the
induced representation `Ind_H^G V` is

  `χ_{Ind_H^G V}(g) = Σ_{σ ∈ H\G : x_σ g x_σ⁻¹ ∈ H} χ_V(x_σ g x_σ⁻¹)`,

where `{x_σ}` is a set of right-coset representatives for `H \ G`. This is the
**Frobenius formula** (Etingof Theorem 5.9.1).

## Statement used here: the averaged form

Picking a transversal of `H \ G` is awkward to formalize and the choice is
immaterial. We use the equivalent *averaged* form, which sums over **all** of
`G` and divides by `|H|`:

  `χ_{Ind_H^G V}(g) = (1/|H|) · Σ_{x ∈ G : x g x⁻¹ ∈ H} χ_V(x g x⁻¹)`.

This is provably equal to Etingof's coset-representative formula: every right
coset `H x_σ` contains exactly `|H|` elements `h x_σ` (`h ∈ H`), and for each
such element

* `(h x_σ) g (h x_σ)⁻¹ = h (x_σ g x_σ⁻¹) h⁻¹ ∈ H ⇔ x_σ g x_σ⁻¹ ∈ H`, and
* `χ_V(h (x_σ g x_σ⁻¹) h⁻¹) = χ_V(x_σ g x_σ⁻¹)` since `χ_V` is a class function
  on `H`.

So the sum over `G` counts each coset's contribution `|H|` times; dividing by
`|H|` recovers the sum over cosets. The averaged form needs no choice of
representatives and is the standard Lean-friendly phrasing of the Frobenius
formula.

## Mathlib correspondence

The character is `LinearMap.trace ℂ _ (ρ g)`, following the convention used
throughout Chapter 5. The induced representation is `Etingof.Definition5_8_1`,
i.e. Mathlib's `Representation.ind H.subtype ρ` on `Representation.IndV`.
Frobenius reciprocity (the induction/restriction adjunction) is not yet in
Mathlib, so the block-trace computation underlying this formula is proved
directly here (currently `sorry`).
-/

open Representation
open scoped TensorProduct

set_option maxHeartbeats 800000 in
-- reason: composing `TensorProduct.map` rewrites and the tensor-trace factorisation over the
-- large module `(G →₀ ℂ) ⊗ V` exceeds the default heartbeat budget.
/-- **Frobenius formula** (Etingof Theorem 5.9.1, averaged form).

The character of the induced representation `Ind_H^G V` at `g` equals the
average over `x ∈ G` (with `x g x⁻¹ ∈ H`) of `χ_V(x g x⁻¹)`:

  `χ_{Ind V}(g) = (1/|H|) · Σ_{x : x g x⁻¹ ∈ H} χ_V(x g x⁻¹)`.

See the module docstring for why this averaged form is equivalent to Etingof's
sum over coset representatives `σ ∈ H \ G`. -/
theorem Etingof.Theorem5_9_1
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H V)
    (g : G) :
    LinearMap.trace ℂ (Representation.IndV H.subtype ρ)
        (Etingof.Definition5_8_1 H ρ g)
      = (Fintype.card H : ℂ)⁻¹ *
          ∑ x : G,
            if h : x * g * x⁻¹ ∈ H then
              LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩)
            else 0 := by
  -- We use the averaged form directly, via the abstract trace-on-coinvariants identity
  -- `Etingof.trace_coinvariantsMap`. The induced representation is `Coinvariants τ` for
  -- `τ = (left regular on ℂ[G]) ⊗ ρ` restricted to `H`, and `Ind_H^G ρ g` is the descent of
  -- the right-shift `Ψ : single x ⊗ v ↦ single (x g⁻¹) ⊗ v` on `ℂ[G] ⊗ V`. The crux lemma gives
  --   `χ(g) = (1/|H|) Σ_{h∈H} tr_{ℂ[G]⊗V}(τ(h) ∘ Ψ)`.
  -- Each summand factors as a tensor trace: `τ(h) ∘ Ψ = (single x ↦ single (h x g⁻¹)) ⊗ ρ(h)`,
  -- whose ℂ[G]-trace counts `{x : h x g⁻¹ = x} = {x : x g x⁻¹ = h}`. Summing over `h ∈ H` and
  -- swapping the order of summation collapses each `x` to the single eigenvalue `tr_V ρ(x g x⁻¹)`
  -- (when `x g x⁻¹ ∈ H`), giving the averaged Frobenius formula.
  classical
  haveI : Invertible (Fintype.card H : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Fintype.card_pos (α := H)).ne')
  -- `Ind_H^G ρ g` is the descent of the right-shift `Ψ` to the coinvariants `Coinvariants τ`,
  -- so the crux lemma applies.
  rw [show Etingof.Definition5_8_1 H ρ g = Representation.ind H.subtype ρ g from rfl,
    Representation.ind_apply, Etingof.trace_coinvariantsMap]
  congr 1
  set τ : Representation ℂ H ((G →₀ ℂ) ⊗[ℂ] V) :=
    Representation.tprod ((Representation.leftRegular ℂ G).comp H.subtype) ρ with hτ
  -- `τ h` as a tensor product of the (left-regular shift, `ρ h`).
  have hτh : ∀ h : H,
      τ h = TensorProduct.map (Representation.leftRegular ℂ G (↑h : G)) (ρ h) := by
    intro h; rw [hτ, Representation.tprod_apply]; rfl
  -- The shift on `ℂ[G]` commutes with left-translation by `↑h`.
  have hshift : ∀ h : H,
      Representation.leftRegular ℂ G (↑h : G) ∘ₗ Finsupp.lmapDomain ℂ ℂ (· * g⁻¹)
        = Finsupp.lmapDomain ℂ ℂ (fun x => (↑h : G) * x * g⁻¹) := by
    intro h
    refine Finsupp.lhom_ext fun y r => ?_
    simp [Representation.leftRegular, Representation.ofMulAction_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, mul_assoc]
  -- Compute each twisted trace as a tensor trace.
  have hper : ∀ h : H,
      LinearMap.trace ℂ ((G →₀ ℂ) ⊗[ℂ] V)
          (τ h ∘ₗ (Finsupp.lmapDomain ℂ ℂ (· * g⁻¹)).rTensor V)
        = (∑ x : G, if (↑h : G) * x * g⁻¹ = x then (1 : ℂ) else 0)
            * LinearMap.trace ℂ V (ρ h) := by
    intro h
    have hmap : τ h ∘ₗ (Finsupp.lmapDomain ℂ ℂ (· * g⁻¹)).rTensor V
        = TensorProduct.map (Finsupp.lmapDomain ℂ ℂ (fun x => (↑h : G) * x * g⁻¹)) (ρ h) := by
      rw [hτh h, LinearMap.rTensor_def, ← TensorProduct.map_comp, hshift h, LinearMap.comp_id]
    rw [hmap, LinearMap.trace_tensorProduct', Etingof.trace_lmapDomain]
  rw [Finset.sum_congr rfl (fun h _ => hper h)]
  -- Distribute, swap the order of summation, and collapse each fibre.
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcollapse : ∀ h : H,
      (if (↑h : G) * x * g⁻¹ = x then (1 : ℂ) else 0) * LinearMap.trace ℂ V (ρ h)
        = if (↑h : G) = x * g * x⁻¹ then LinearMap.trace ℂ V (ρ h) else 0 := by
    intro h
    have hiff : ((↑h : G) * x * g⁻¹ = x) ↔ ((↑h : G) = x * g * x⁻¹) := by
      rw [mul_inv_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq]
    by_cases hc : (↑h : G) = x * g * x⁻¹
    · rw [if_pos (hiff.mpr hc), if_pos hc, one_mul]
    · rw [if_neg (fun hh => hc (hiff.mp hh)), if_neg hc, zero_mul]
  rw [Finset.sum_congr rfl (fun h _ => hcollapse h),
    Etingof.sum_subtype_ite_coe H (x * g * x⁻¹) (fun h => LinearMap.trace ℂ V (ρ h))]

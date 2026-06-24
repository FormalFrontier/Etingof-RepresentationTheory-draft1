import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1

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
  -- Proof strategy (Etingof, Discussion proof of Theorem 5.9.1):
  --   Decompose `Ind_H^G V = ⨁_σ V_σ` over right cosets `σ ∈ H\G`, where
  --   `V_σ = {f ∈ Ind V | f(g) = 0 ∀ g ∉ σ}`. Then `χ(g) = Σ_σ χ_σ(g)`, the
  --   sum of diagonal block traces. A coset summand contributes `0` unless
  --   `σ g = σ`; when `σ g = σ`, writing `x_σ g = h x_σ` with
  --   `h = x_σ g x_σ⁻¹ ∈ H`, the map `α : V_σ → V`, `α(f) = f(x_σ)` is an
  --   isomorphism intertwining `g` on `V_σ` with `ρ(h)` on `V`, so
  --   `χ_σ(g) = χ_V(x_σ g x_σ⁻¹)`. Summing and averaging over the `|H|`
  --   elements of each coset yields the stated formula.
  sorry

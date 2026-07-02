import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1

/-!
# Remark 5.9.2: The averaged form of the Frobenius formula

Etingof's Remark 5.9.2 observes that when the characteristic of the ground field `k` is
relatively prime to `|H|`, the Frobenius formula for the character of an induced representation
(Theorem 5.9.1) can be rewritten as an average over **all** of `G`:

  `χ(g) = (1/|H|) · Σ_{x ∈ G : x g x⁻¹ ∈ H} χ_V(x g x⁻¹)`.

## Relation to Theorem 5.9.1

The book's Theorem 5.9.1 is stated as a sum over coset representatives `σ ∈ H \ G`, and this
remark converts it to the averaged form. In this formalization the *averaged form is the primary
statement*: choosing a transversal of `H \ G` is awkward to formalize, so `Etingof.Theorem5_9_1`
was proved directly in the averaged phrasing (see the module docstring of `Theorem5_9_1.lean`).

Consequently the content of this remark — the averaged Frobenius character formula — is exactly
the statement of `Etingof.Theorem5_9_1`, and `Etingof.Remark_5_9_2` below records it under the
name of the book item. We work over `k = ℂ` (characteristic `0`), so the hypothesis "`char k`
coprime to `|H|`" holds automatically and `(|H| : ℂ)⁻¹` is a genuine inverse.

(Etingof Remark 5.9.2)
-/

open Representation
open scoped TensorProduct

/-- **Remark 5.9.2** (averaged form of the Frobenius formula).

When the characteristic of the ground field is coprime to `|H|` (here `k = ℂ`, characteristic
`0`), the character of the induced representation `Ind_H^G V` at `g` is the average over all
`x ∈ G` with `x g x⁻¹ ∈ H` of `χ_V(x g x⁻¹)`:

  `χ_{Ind V}(g) = (1/|H|) · Σ_{x ∈ G : x g x⁻¹ ∈ H} χ_V(x g x⁻¹)`.

This is Etingof's Remark 5.9.2, the averaged reformulation of the Frobenius formula
(Theorem 5.9.1). In this development the averaged form is exactly how `Etingof.Theorem5_9_1`
is phrased, so the remark is a direct restatement of that theorem. -/
theorem Etingof.Remark_5_9_2
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
            else 0 :=
  Etingof.Theorem5_9_1 H ρ g

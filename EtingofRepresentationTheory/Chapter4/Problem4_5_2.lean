import Mathlib

/-!
# Problem 4.5.2: the primitive central idempotents of `ℂ[G]`

**Problem 4.5.2.** Let `G` be a finite group. Let `Vᵢ` be the irreducible complex
representations of `G`. For every `i`, let
`ψᵢ = (dim Vᵢ / |G|) · ∑_{g ∈ G} χ_{Vᵢ}(g) · g⁻¹ ∈ ℂ[G]`.

(i) Prove that `ψᵢ` acts on `Vⱼ` as the identity if `j = i`, and as the null map if
`j ≠ i`.

(ii) Prove that the `ψᵢ` are **idempotents**: `ψᵢ² = ψᵢ` for every `i`, and `ψᵢ ψⱼ = 0`
for `i ≠ j`.

*Hint.* In (i), `ψᵢ` commutes with every element of `ℂ[G]` and thus acts on `Vⱼ` as an
intertwining operator; Schur's lemma (Corollary 2.3.10) forces it to act as a scalar,
which is computed by taking the trace in `Vⱼ`.

## Formalization

We formalize the family indexed by the actual irreducible representations: an element
`ψ V ∈ ℂ[G]` is attached to each finite-dimensional complex representation `V`, and the
statements quantify over simple `V, W : FDRep ℂ G`. Non-isomorphism `Vⱼ ≇ Vᵢ` is
expressed as `IsEmpty (W ≅ V)`.

The action of `ψ V` on a representation `W` is via the group-algebra action
`Representation.asAlgebraHom W.ρ : ℂ[G] →ₐ[ℂ] End ℂ W`.

This is a statement-pass formalization: the statements are fixed faithfully and the
proofs are deferred (`sorry`).
-/

open CategoryTheory MonoidAlgebra

namespace Etingof

variable {G : Type*} [Group G] [Fintype G]

/-- The element `ψ_V = (dim V / |G|) · ∑_{g ∈ G} χ_V(g) · g⁻¹ ∈ ℂ[G]` associated to a
finite-dimensional complex representation `V`, as in Problem 4.5.2. -/
noncomputable def psi (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) •
    ∑ g : G, V.character g • MonoidAlgebra.single g⁻¹ (1 : ℂ)

/-- **Problem 4.5.2(i), diagonal case.** `ψ_V` acts on `V` itself as the identity. -/
theorem psi_acts_self (V : FDRep ℂ G) [Simple V] :
    Representation.asAlgebraHom V.ρ (psi V) = LinearMap.id := by
  sorry

/-- **Problem 4.5.2(i), off-diagonal case.** If `W` and `V` are non-isomorphic simple
representations, then `ψ_V` acts on `W` as the null map. -/
theorem psi_acts_other (V W : FDRep ℂ G) [Simple V] [Simple W] (h : IsEmpty (W ≅ V)) :
    Representation.asAlgebraHom W.ρ (psi V) = 0 := by
  sorry

/-- **Problem 4.5.2(ii), idempotence.** Each `ψ_V` is an idempotent of `ℂ[G]`. -/
theorem psi_idempotent (V : FDRep ℂ G) [Simple V] :
    psi V * psi V = psi V := by
  sorry

/-- **Problem 4.5.2(ii), orthogonality.** For non-isomorphic simple representations `V`
and `W`, the idempotents `ψ_V` and `ψ_W` are orthogonal. -/
theorem psi_orthogonal (V W : FDRep ℂ G) [Simple V] [Simple W] (h : IsEmpty (W ≅ V)) :
    psi W * psi V = 0 := by
  sorry

end Etingof

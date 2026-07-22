import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1

/-!
# Exercise 5.8.5: `Ind_K^G ℂ_χ ≅ ℂ[G] e_χ`

**Exercise 5.8.5.** Let `K ⊂ G` be finite groups, and let `χ : K → ℂ*` be a homomorphism.
Let `ℂ_χ` be the corresponding 1-dimensional representation of `K`. Let

  `e_χ = (1/|K|) ∑_{g ∈ K} χ(g)⁻¹ g ∈ ℂ[K]`

be the idempotent corresponding to `χ`. Show that the `G`-representation `Ind_K^G ℂ_χ` is
naturally isomorphic to `ℂ[G] e_χ` (with `G` acting by left multiplication).

## Formalization

* `chiRep χ : Representation ℂ K ℂ` is the 1-dimensional representation `ℂ_χ` where `k` acts
  by the scalar `χ k`.
* `idempotentOfChar χ : ℂ[G]` is `e_χ = |K|⁻¹ ∑_{g ∈ K} χ(g)⁻¹ · g` (the elements of `K` are
  included into `G`).
* `charLeftIdeal χ : Submodule ℂ[G] ℂ[G]` is the left ideal `ℂ[G] · e_χ`, on which `G` acts by
  left multiplication `g · x = of(g) * x`.

The induced representation is `Etingof.Definition5_8_1 K (chiRep χ)`. The claim is a
`G`-equivariant `ℂ`-linear isomorphism `e` between its carrier and the left ideal `ℂ[G] e_χ`,
expressed by the intertwining identity `↑(e (ρ_ind g x)) = of(g) * ↑(e x)` in `ℂ[G]`.

Statement pass: the proof is left as `sorry`.
-/

namespace Etingof

open scoped Classical

variable {G : Type*} [Group G] [Fintype G] (K : Subgroup G)

/-- The 1-dimensional representation `ℂ_χ` of `K` attached to a character `χ : K → ℂ*`:
`k` acts on `ℂ` by multiplication by the scalar `χ k`. -/
noncomputable def chiRep (χ : K →* ℂˣ) : Representation ℂ K ℂ where
  toFun k := ((χ k : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' k₁ k₂ := by
    apply LinearMap.ext; intro z
    change ((χ (k₁ * k₂) : ℂˣ) : ℂ) * z = ((χ k₁ : ℂˣ) : ℂ) * (((χ k₂ : ℂˣ) : ℂ) * z)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The idempotent `e_χ = |K|⁻¹ ∑_{g ∈ K} χ(g)⁻¹ · g ∈ ℂ[G]` attached to `χ`. -/
noncomputable def idempotentOfChar (χ : K →* ℂˣ) : MonoidAlgebra ℂ G :=
  (Nat.card K : ℂ)⁻¹ •
    ∑ g : K, ((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G)

/-- The left ideal `ℂ[G] · e_χ`, with `G` acting by left multiplication. -/
noncomputable def charLeftIdeal (χ : K →* ℂˣ) : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
  Submodule.span (MonoidAlgebra ℂ G) {idempotentOfChar K χ}

/-- Exercise 5.8.5. The induced representation `Ind_K^G ℂ_χ` is `G`-equivariantly isomorphic
to the left ideal `ℂ[G] e_χ` (with `G` acting by left multiplication). The intertwining is
recorded via the coercion to `ℂ[G]`: `↑(e (ρ_ind g x)) = of(g) * ↑(e x)`. -/
theorem ind_chiRep_iso_charLeftIdeal (χ : K →* ℂˣ) :
    ∃ e : Representation.IndV K.subtype (chiRep K χ) ≃ₗ[ℂ] ↥(charLeftIdeal K χ),
      ∀ (g : G) x,
        (e (Etingof.Definition5_8_1 K (chiRep K χ) g x) : MonoidAlgebra ℂ G)
          = MonoidAlgebra.of ℂ G g * (e x : MonoidAlgebra ℂ G) := by
  sorry

end Etingof

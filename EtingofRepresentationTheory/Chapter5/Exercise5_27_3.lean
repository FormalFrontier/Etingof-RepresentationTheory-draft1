import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1

/-!
# Exercise 5.27.3: deduce parts (i)–(iii) of Theorem 5.27.1 from part (iv)

**Exercise 5.27.3.** Deduce parts (i)—(iii) of Theorem 5.27.1 from part (iv).

Theorem 5.27.1 classifies the irreducible representations of a semidirect product `A ⋊[φ] G`
(with `A` abelian) by the orbit method. Writing `Â = (A →* ℂˣ)` for the character group with the
dual `G`-action `(g · χ)(a) = χ(φ(g⁻¹)(a))`, `G_χ = stab χ` for the stabilizer of `χ`, and
`V(χ, U) = Ind_{G_χ ⋉ A}^{G ⋉ A}(U ⊗ ℂ_χ)` for the induced representation attached to a
representative `χ` of a `G`-orbit and an irreducible `U` of `G_χ`, the four parts are:

* **(i)** `V(χ, U)` is irreducible;
* **(ii)** the `V(χ, U)` are pairwise non-isomorphic (an isomorphism `V(χ₁, U₁) ≅ V(χ₂, U₂)`
  forces `χ₂ = g · χ₁` for some `g` and `U₂ ≅ g(U₁)`);
* **(iii)** every irreducible of `A ⋊[φ] G` arises as some `V(χ, U)`;
* **(iv)** the explicit character formula
  `χ_{V(χ,U)}(a, g) = |G_χ|⁻¹ Σ_{h : hgh⁻¹ ∈ G_χ} χ(φ(h)(a)) · χ_U(hgh⁻¹)`.

The exercise asks to derive (i)–(iii) *from* the character formula (iv) using character theory:
(i) because `⟨χ_{V(χ,U)}, χ_{V(χ,U)}⟩ = 1`, (ii) because distinct orbit data give orthogonal
characters, and (iii) by the sum-of-squares count `Σ dim V(χ, U)² = |A ⋊[φ] G|`.

## Formalization

Because the constructions in `Theorem5_27_1.lean` (`dualSmulAux`, `stabAux`, `inducedRepV`, …)
are `private`, we phrase the exercise abstractly over the same data that Theorem 5.27.1 exhibits:
a dual action `dualSmul`, a stabilizer assignment `stab`, the construction `V`, and the transport
map `transport`, characterised by the same defining identities. The hypothesis is exactly part
**(iv)** — the character formula — and the conclusion is the conjunction of parts **(i)**, **(ii)**,
and **(iii)**, stated with the identical expressions used in `Etingof.Theorem5_27_1`.

Statement pass: the deduction is left as `sorry`.
-/

noncomputable section

open CategoryTheory

namespace Etingof

open Classical in
/-- Exercise 5.27.3. Given the semidirect-product setup of Theorem 5.27.1 — the dual `G`-action
`dualSmul` on `Â`, the stabilizer subgroups `stab χ`, the construction `V χ U`, and the transport
map `transport` — together with the character formula **(iv)**, the classification properties
**(i)** (irreducibility), **(ii)** (pairwise non-isomorphism), and **(iii)** (completeness) all
follow. -/
theorem Exercise5_27_3
    (G A : Type) [Group G] [CommGroup A] [Fintype G] [Fintype A]
    (φ : G →* MulAut A)
    (dualSmul : G → (A →* ℂˣ) → (A →* ℂˣ))
    (_hdual : ∀ g χ a, dualSmul g χ a = χ ((φ g⁻¹ : MulAut A) a))
    (stab : (A →* ℂˣ) → Subgroup G)
    (_hstab : ∀ χ g, g ∈ stab χ ↔ dualSmul g χ = χ)
    (V : (χ : A →* ℂˣ) → FDRep ℂ ↥(stab χ) → FDRep ℂ (A ⋊[φ] G))
    (transport : (g : G) → (χ₁ χ₂ : A →* ℂˣ) → dualSmul g χ₁ = χ₂ →
      FDRep ℂ ↥(stab χ₁) → FDRep ℂ ↥(stab χ₂))
    -- Hypothesis: part (iv), the character formula.
    (character_formula :
      ∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)), Simple U →
        ∀ (a : A) (g : G),
          (V χ U).character ⟨a, g⟩ =
            (Fintype.card ↥(stab χ) : ℂ)⁻¹ *
              ∑ h : G, if hh : h * g * h⁻¹ ∈ stab χ
                then (χ ((φ h : MulAut A) a) : ℂ) *
                  U.character ⟨h * g * h⁻¹, hh⟩
                else 0) :
    -- (i) V(χ, U) is irreducible when U is irreducible.
    (∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
        Simple U → Simple (V χ U)) ∧
    -- (ii) The V(χ, U) are pairwise non-isomorphic.
    (∀ (χ₁ χ₂ : A →* ℂˣ)
        (U₁ : FDRep ℂ ↥(stab χ₁)) (U₂ : FDRep ℂ ↥(stab χ₂)),
        Simple U₁ → Simple U₂ →
        Nonempty (V χ₁ U₁ ≅ V χ₂ U₂) →
        ∃ (g : G) (hg : dualSmul g χ₁ = χ₂),
          Nonempty (U₂ ≅ transport g χ₁ χ₂ hg U₁)) ∧
    -- (iii) Every irreducible of A ⋊[φ] G arises as some V(χ, U).
    (∀ (W : FDRep ℂ (A ⋊[φ] G)), Simple W →
        ∃ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)),
          Simple U ∧ Nonempty (W ≅ V χ U)) := by
  sorry

end Etingof

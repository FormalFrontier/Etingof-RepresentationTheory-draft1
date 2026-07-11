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

The hypothesis `_htransport` characterizes the otherwise-free `transport` map by the character
identity `χ_{g(U)}(s) = χ_U(g⁻¹ s g)` (mirroring `transportRep_ρ_apply`/`conjStabHom_coe` in
`Theorem5_27_1.lean`). Without it the theorem is refutable, since a universally quantified free
`transport` admits the adversarial choice `transport _ _ _ _ U := U ⊞ U`.

Proof pass: the three parts are split into labeled `sorry` goals for follow-up. Parts (i)/(ii)
go through character orthogonality; part (iii) through the sum-of-squares dimension count.
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
    -- Characterizing hypothesis for `transport`, mirroring `transportRep` in
    -- `Theorem5_27_1.lean` (`transportRep_ρ_apply` / `conjStabHom_coe`): the transported
    -- representation `g(U)` acts by `ρ_{g(U)}(s) = ρ_U(g⁻¹ s g)`, so its character at `s` is
    -- the character of `U` at the conjugate `g⁻¹ s g ∈ G_{χ₁}`. Without this the theorem is
    -- refutable, since `transport` would otherwise be a free, unconstrained function (see #6383).
    (_htransport : ∀ (g : G) (χ₁ χ₂ : A →* ℂˣ) (hg : dualSmul g χ₁ = χ₂)
        (U : FDRep ℂ ↥(stab χ₁)) (s : ↥(stab χ₂)) (hs : g⁻¹ * (s : G) * g ∈ stab χ₁),
        (transport g χ₁ χ₂ hg U).character s = U.character ⟨g⁻¹ * (s : G) * g, hs⟩)
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
  refine ⟨?_, ?_, ?_⟩
  · -- Part (i): irreducibility of `V χ U`.
    -- Strategy (character orthogonality): from the character formula (iv), compute
    -- `⟨χ_{V χ U}, χ_{V χ U}⟩ = 1` (an induced-character inner product that collapses,
    -- by Frobenius reciprocity / Mackey, to `⟨χ_U, χ_U⟩ = 1` since `U` is simple), then
    -- apply the converse orthonormality criterion `⟨χ_W, χ_W⟩ = 1 ⇒ Simple W` (Maschke +
    -- linear independence of irreducible characters over ℂ). Tracked in the (i)+(ii) sub-issue.
    sorry
  · -- Part (ii): pairwise non-isomorphism.
    -- Strategy: an isomorphism `V χ₁ U₁ ≅ V χ₂ U₂` forces equal characters; feeding the
    -- character formula (iv) into `⟨χ_{V χ₁ U₁}, χ_{V χ₂ U₂}⟩ ≠ 0` forces the orbit data to
    -- match, i.e. `dualSmul g χ₁ = χ₂` for some `g` and, via `_htransport`, `U₂ ≅ g(U₁)`.
    -- Tracked in the (i)+(ii) sub-issue.
    sorry
  · -- Part (iii): completeness — every simple `W` is some `V χ U`.
    -- Strategy: the sum-of-squares count `Σ_{χ,U} dim(V χ U)² = |A ⋊[φ] G|` (from (iv) and the
    -- orbit decomposition) exhausts the regular representation, so no simple is missed.
    -- Tracked in the (iii) sub-issue.
    sorry

end Etingof

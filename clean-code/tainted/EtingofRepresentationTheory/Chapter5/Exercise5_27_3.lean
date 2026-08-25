import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_27_1
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Infrastructure.CompletenessCriterion
import EtingofRepresentationTheory.Infrastructure.CharacterOrthogonalityCompat

/-!
# Exercise 5.27.3: deduce parts (i)–(iii) of Theorem 5.27.1 from part (iv)

**Exercise 5.27.3.** Deduce parts (i)–(iii) of Theorem 5.27.1 from part (iv).

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

The exercise asks to derive (i)–(iii) from the character formula (iv) using character theory:
(i) because `⟨χ_{V(χ,U)}, χ_{V(χ,U)}⟩ = 1`, (ii) because distinct orbit data give orthogonal
characters, and (iii) by the sum-of-squares count `Σ dim V(χ, U)² = |A ⋊[φ] G|`.

## Formalization

Because the constructions in `Theorem5_27_1.lean` (`dualSmulAux`, `stabAux`, `inducedRepV`, …)
are `private`, we phrase the exercise abstractly over the same data that Theorem 5.27.1 exhibits:
a dual action `dualSmul`, a stabilizer assignment `stab`, the construction `V`, and the transport
map `transport`, characterised by the same defining identities. The hypothesis is exactly part
**(iv)**, the character formula, and the conclusion is the conjunction of parts **(i)**, **(ii)**,
and **(iii)**, stated with the identical expressions used in `Etingof.Theorem5_27_1`.

The hypothesis `_htransport` characterizes the otherwise-free `transport` map by the character
identity `χ_{g(U)}(s) = χ_U(g⁻¹ s g)` (mirroring `transportRep_ρ_apply`/`conjStabHom_coe` in
`Theorem5_27_1.lean`). Without it the theorem is refutable, since a universally quantified free
`transport` admits the adversarial choice `transport _ _ _ _ U := U ⊞ U`.

Proof. Parts (i) and (ii) are proven via character orthogonality: (i) by the induced-character
norm being one, (ii) by a mixed off-diagonal Mackey computation (existence of the intertwining
element `g` from a nonzero cross inner product) followed by a same-orbit Mackey reduction and
`FDRep.char_orthonormal` for the `U₂ ≅ transport g χ₁ χ₂ hg U₁` conclusion. Part (iii)
(completeness) is proven via the sum-of-squares dimension count: the orbit-method family
`{V(χ, U) : χ an orbit representative of the dual `G`-action on `Â`, U an irreducible of
`stab χ`}` consists of pairwise non-isomorphic simples (parts (i), (ii)), and its squared
dimensions sum to `|A ⋊[φ] G|`. The dimension of `V(χ, U)` is `[G : stab χ] · dim U`
(character formula (iv) at the identity), `Σ_U (dim U)² = |stab χ|` for each stabilizer
(`IrrepDecomp.sum_finrank_sq_eq_card`), and the class formula for the dual action together with
`|Â| = |A|` collapses the total to `|G| · |A| = |A ⋊[φ] G|`. Matching the Artin-Wedderburn total
forces exhaustiveness (`FDRep.complete_of_sum_finrank_sq_eq_card`), so every simple is some
`V(χ, U)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Etingof

/-- Character orthogonality for a finite abelian group `A`: the sum over `A` of a character
`ψ : A →* ℂˣ` is `|A|` if `ψ` is trivial and `0` otherwise. Specialization of
`sum_hom_units_eq_zero` composed with the coercion `ℂˣ →* ℂ`. -/
private lemma sum_monoidHom_units_cast_eq {A : Type} [CommGroup A] [Fintype A]
    (ψ : A →* ℂˣ) [Decidable (ψ = 1)] :
    ∑ a : A, (ψ a : ℂ) = if ψ = 1 then (Fintype.card A : ℂ) else 0 := by
  split
  · rename_i h
    subst h
    simp only [MonoidHom.one_apply, Units.val_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  · rename_i h
    have hne : (Units.coeHom ℂ).comp ψ ≠ 1 := by
      intro habs
      apply h
      ext a
      have h1 : (↑(ψ a) : ℂ) = 1 := DFunLike.congr_fun habs a
      rw [MonoidHom.one_apply, Units.val_one]
      exact h1
    have := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp ψ) hne
    rw [← this]
    rfl

/-- Pointwise cancellation for multiplicative characters, stated with the precise
`MonoidHom` group structure used in this file. -/
private lemma monoidHom_mul_inv_eq_one {A : Type} [Monoid A] (α β : A →* ℂˣ) :
    α * β⁻¹ = 1 ↔ α = β := by
  constructor
  · intro h
    ext a
    have ha := DFunLike.congr_fun h a
    change α a * (β a)⁻¹ = 1 at ha
    exact congrArg Units.val ((mul_inv_eq_one (a := α a) (b := β a)).mp ha)
  · rintro rfl
    ext a
    simp

open Classical in
/-- Exercise 5.27.3. Given the semidirect-product setup of Theorem 5.27.1 (the dual `G`-action
`dualSmul` on `Â`, the stabilizer subgroups `stab χ`, the construction `V χ U`, and the transport
map `transport`) together with the character formula **(iv)**, the classification properties
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
    -- refutable, since `transport` would otherwise be a free, unconstrained function.
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
  -- Part (i): irreducibility of `V χ U`, hoisted as `hVsimple` so parts (i) and (ii) share it.
  -- Strategy (character orthogonality): from the character formula (iv), compute the norm
  -- `∑_{x ∈ A ⋊ G} χ_{V χ U}(x) χ_{V χ U}(x⁻¹) = |A ⋊ G|`. Two conjugation reindexings of
  -- the internal `G`-sums collapse the induced-character norm to `|G|·|G_χ|·⟨χ_U, χ_U⟩`,
  -- which is `|G|·|G_χ|·|G_χ|` since `U` is simple (`simple_iff_char_is_norm_one`). Combined
  -- with the `|A|` from character orthogonality on `A` and the `|G_χ|⁻²` prefactor, the norm
  -- is exactly `|A|·|G| = |A ⋊ G|`; the converse `simple_iff_char_is_norm_one` gives `Simple`.
  have hVsimple : ∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)), Simple U → Simple (V χ U) := by
    intro χ U hU
    classical
    haveI : Fintype (A ⋊[φ] G) :=
      Fintype.ofEquiv (A × G) (SemidirectProduct.equivProd (φ := φ)).symm
    -- Extend the character of `U` (defined on the stabilizer subgroup) to a class function on `G`,
    -- zero outside `stab χ`.
    set Uc : G → ℂ := fun y => if h : y ∈ stab χ then U.character ⟨y, h⟩ else 0 with hUc_def
    -- Reformulated character formula (iv): pull the character factor through the `dite`.
    have hcf : ∀ (a : A) (g : G),
        (V χ U).character ⟨a, g⟩
          = (Fintype.card ↥(stab χ) : ℂ)⁻¹ * ∑ h : G, (χ ((φ h : MulAut A) a) : ℂ) * Uc (h * g * h⁻¹) := by
      intro a g
      rw [character_formula χ U hU a g]
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : h * g * h⁻¹ ∈ stab χ
      · rw [dif_pos hh, hUc_def]
        simp only [dif_pos hh]
      · rw [dif_neg hh, hUc_def]
        simp only [dif_neg hh, mul_zero]
    -- Inverse in the semidirect product.
    have hinv : ∀ (a : A) (g : G),
        (⟨a, g⟩ : A ⋊[φ] G)⁻¹ = ⟨(φ g⁻¹ : MulAut A) a⁻¹, g⁻¹⟩ := by
      intro a g
      apply SemidirectProduct.ext
      · exact SemidirectProduct.inv_left _
      · exact SemidirectProduct.inv_right _
    -- `dualSmul` is a left action (it equals `χ ∘ φ(·⁻¹)`).
    have hds_mul : ∀ (p q : G) (ν : A →* ℂˣ), dualSmul p (dualSmul q ν) = dualSmul (p * q) ν := by
      intro p q ν
      ext a
      rw [_hdual, _hdual, _hdual]
      congr 1
      have : (φ (p * q)⁻¹ : MulAut A) a = (φ q⁻¹ : MulAut A) ((φ p⁻¹ : MulAut A) a) := by
        rw [mul_inv_rev, map_mul]; rfl
      rw [this]
    have hds_one : ∀ (ν : A →* ℂˣ), dualSmul 1 ν = ν := by
      intro ν
      ext a
      rw [_hdual]
      simp
    -- `χ ∘ φ h = dualSmul h⁻¹ χ` as characters of `A`.
    have hcomp_eq : ∀ (h : G) (a : A), (χ ((φ h : MulAut A) a) : ℂˣ) = dualSmul h⁻¹ χ a := by
      intro h a
      rw [_hdual]
      simp
    -- The `a`-orthogonality: summing the two character factors over `A`.
    have hasum : ∀ (g h h' : G),
        (∑ a : A, (χ ((φ h : MulAut A) a) : ℂ) *
            (χ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ))
          = if h * g * h'⁻¹ ∈ stab χ then (Fintype.card A : ℂ) else 0 := by
      intro g h h'
      -- Assemble the product of the two characters as the value of a single character `ψ : A →* ℂˣ`.
      set ψ : A →* ℂˣ :=
        (χ.comp (φ h : MulAut A).toMonoidHom) * (χ.comp (φ (h' * g⁻¹) : MulAut A).toMonoidHom)⁻¹
        with hψ_def
      have hψ_val : ∀ a : A, ((ψ a : ℂˣ) : ℂ) =
          (χ ((φ h : MulAut A) a) : ℂ) *
            (χ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ) := by
        intro a
        have hfac : (φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)
            = ((φ (h' * g⁻¹) : MulAut A) a)⁻¹ := by
          rw [map_mul]
          simp
        rw [hfac, hψ_def]
        simp
      have hsum_eq : (∑ a : A, (χ ((φ h : MulAut A) a) : ℂ) *
            (χ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ))
          = ∑ a : A, ((ψ a : ℂˣ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hψ_val a]
      rw [hsum_eq, sum_monoidHom_units_cast_eq ψ]
      -- Identify `ψ = 1 ↔ h * g * h'⁻¹ ∈ stab χ`.
      have hiff : ψ = 1 ↔ h * g * h'⁻¹ ∈ stab χ := by
        rw [hψ_def]
        have e1 : (χ.comp (φ h : MulAut A).toMonoidHom) = dualSmul h⁻¹ χ := by
          refine MonoidHom.ext fun a => ?_
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
          exact hcomp_eq h a
        have e2 : (χ.comp (φ (h' * g⁻¹) : MulAut A).toMonoidHom) = dualSmul (g * h'⁻¹) χ := by
          refine MonoidHom.ext fun a => ?_
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
          rw [hcomp_eq (h' * g⁻¹) a]
          congr 2
          group
        rw [e1, e2, monoidHom_mul_inv_eq_one, _hstab]
        constructor
        · intro H
          have hkey := congrArg (dualSmul h) H
          rw [hds_mul, hds_mul, mul_inv_cancel, hds_one] at hkey
          rw [← mul_assoc] at hkey
          exact hkey.symm
        · intro H
          have hkey := congrArg (dualSmul h⁻¹) H
          rw [hds_mul, show h⁻¹ * (h * g * h'⁻¹) = g * h'⁻¹ from by group] at hkey
          exact hkey.symm
      by_cases hmem : h * g * h'⁻¹ ∈ stab χ
      · rw [if_pos hmem, if_pos (hiff.mpr hmem)]
      · rw [if_neg hmem, if_neg (fun hc => hmem (hiff.mp hc))]
    -- Conjugation invariance of the extended class function `Uc` by stabilizer elements.
    have hUc_conj : ∀ (k y : G), k ∈ stab χ → Uc (k * y * k⁻¹) = Uc y := by
      intro k y hk
      by_cases hy : y ∈ stab χ
      · have hconj : k * y * k⁻¹ ∈ stab χ :=
          (stab χ).mul_mem ((stab χ).mul_mem hk hy) ((stab χ).inv_mem hk)
        simp only [hUc_def, dif_pos hconj, dif_pos hy]
        have hval : (⟨k * y * k⁻¹, hconj⟩ : ↥(stab χ))
            = ⟨k, hk⟩ * ⟨y, hy⟩ * ⟨k, hk⟩⁻¹ := by
          apply Subtype.ext; rfl
        rw [hval, FDRep.char_conj]
      · have hconj : k * y * k⁻¹ ∉ stab χ := by
          intro hc
          apply hy
          have hrw : y = k⁻¹ * (k * y * k⁻¹) * k := by group
          rw [hrw]
          exact (stab χ).mul_mem ((stab χ).mul_mem ((stab χ).inv_mem hk) hc) hk
        simp only [hUc_def, dif_neg hconj, dif_neg hy]
    -- The `U`-norm: `∑_{y : G} Uc y · Uc y⁻¹ = |G_χ|` (character norm of the simple `U`).
    have hUnorm : ∑ y : G, Uc y * Uc y⁻¹ = (Fintype.card ↥(stab χ) : ℂ) := by
      have hfilter : ∑ y : G, Uc y * Uc y⁻¹
          = ∑ y ∈ Finset.univ.filter (· ∈ stab χ), Uc y * Uc y⁻¹ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ stab χ
        · rw [if_pos hy]
        · rw [if_neg hy]
          simp only [hUc_def, dif_neg hy, zero_mul]
      rw [hfilter,
        Finset.sum_subtype (p := (· ∈ stab χ)) (Finset.univ.filter (· ∈ stab χ))
          (fun x => by simp [Finset.mem_filter]) (fun y => Uc y * Uc y⁻¹),
        ← Nat.card_eq_fintype_card, ← (FDRep.simple_iff_char_is_norm_one U).mp hU]
      refine Finset.sum_congr rfl fun u _ => ?_
      have h1 : Uc ↑u = U.character u := by
        simp only [hUc_def, dif_pos u.2, Subtype.coe_eta]
      have h2 : Uc (↑u : G)⁻¹ = U.character u⁻¹ := by
        have huinv : ((u : G))⁻¹ ∈ stab χ := (stab χ).inv_mem u.2
        simp only [hUc_def, dif_pos huinv]
        exact congrArg U.character (Subtype.ext rfl)
      rw [h1, h2]
    -- The Mackey reindexing at fixed `h`: two conjugation change-of-variables
    -- `g ↦ h g h⁻¹`, `h' ↦ h h'⁻¹` on the pair `(g, h')`.
    have hstep_h : ∀ h : G,
        (∑ g : G, ∑ h' : G,
          (if h * g * h'⁻¹ ∈ stab χ then (1 : ℂ) else 0) * Uc (h * g * h⁻¹)
            * Uc (h' * g⁻¹ * h'⁻¹))
        = ∑ u : G, ∑ t : G,
          (if u * t ∈ stab χ then (1 : ℂ) else 0) * Uc u * Uc (t⁻¹ * u⁻¹ * t) := by
      intro h
      let Φ : (G × G) ≃ (G × G) :=
        { toFun := fun p => (h * p.1 * h⁻¹, h * p.2⁻¹)
          invFun := fun q => (h⁻¹ * q.1 * h, q.2⁻¹ * h)
          left_inv := by rintro ⟨g, h'⟩; refine Prod.ext ?_ ?_ <;> · simp only []; group
          right_inv := by rintro ⟨u, t⟩; refine Prod.ext ?_ ?_ <;> · simp only []; group }
      rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
      refine Fintype.sum_equiv Φ _ _ ?_
      rintro ⟨g, h'⟩
      change (if h * g * h'⁻¹ ∈ stab χ then (1 : ℂ) else 0) * Uc (h * g * h⁻¹)
            * Uc (h' * g⁻¹ * h'⁻¹)
          = (if h * g * h⁻¹ * (h * h'⁻¹) ∈ stab χ then (1 : ℂ) else 0) * Uc (h * g * h⁻¹)
            * Uc ((h * h'⁻¹)⁻¹ * (h * g * h⁻¹)⁻¹ * (h * h'⁻¹))
      rw [show h * g * h⁻¹ * (h * h'⁻¹) = h * g * h'⁻¹ from by group,
          show (h * h'⁻¹)⁻¹ * (h * g * h⁻¹)⁻¹ * (h * h'⁻¹) = h' * g⁻¹ * h'⁻¹ from by group]
    -- The inner collapse: the conditional double sum equals `|G_χ| · ∑_u Uc u · Uc u⁻¹`.
    have hinner : (∑ u : G, ∑ t : G,
          (if u * t ∈ stab χ then (1 : ℂ) else 0) * Uc u * Uc (t⁻¹ * u⁻¹ * t))
        = (Fintype.card ↥(stab χ) : ℂ) * ∑ u : G, Uc u * Uc u⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u ∈ stab χ
      · have hkey : ∀ t : G, (if u * t ∈ stab χ then (1 : ℂ) else 0) * Uc (t⁻¹ * u⁻¹ * t)
            = if t ∈ stab χ then Uc u⁻¹ else 0 := by
          intro t
          by_cases ht : t ∈ stab χ
          · have hut : u * t ∈ stab χ := (stab χ).mul_mem hu ht
            rw [if_pos hut, if_pos ht, one_mul]
            have hc := hUc_conj t⁻¹ u⁻¹ ((stab χ).inv_mem ht)
            rw [inv_inv] at hc
            exact hc
          · have hut : u * t ∉ stab χ := by
              intro hcc; apply ht
              have htt : t = u⁻¹ * (u * t) := by group
              rw [htt]; exact (stab χ).mul_mem ((stab χ).inv_mem hu) hcc
            rw [if_neg hut, if_neg ht, zero_mul]
        have hrw : ∀ t : G,
            (if u * t ∈ stab χ then (1 : ℂ) else 0) * Uc u * Uc (t⁻¹ * u⁻¹ * t)
            = Uc u * ((if u * t ∈ stab χ then (1 : ℂ) else 0) * Uc (t⁻¹ * u⁻¹ * t)) := by
          intro t; ring
        rw [Finset.sum_congr rfl (fun t _ => hrw t), ← Finset.mul_sum,
            Finset.sum_congr rfl (fun t _ => hkey t), ← Finset.sum_filter, Finset.sum_const,
            ← Fintype.card_subtype (· ∈ stab χ), nsmul_eq_mul]
        ring
      · have h0 : Uc u = 0 := by simp only [hUc_def, dif_neg hu]
        simp only [h0, zero_mul, mul_zero, Finset.sum_const_zero]
    -- Assemble the reindexed triple sum.
    have hreindex : (∑ g : G, ∑ h : G, ∑ h' : G,
          (if h * g * h'⁻¹ ∈ stab χ then (1 : ℂ) else 0) * Uc (h * g * h⁻¹)
            * Uc (h' * g⁻¹ * h'⁻¹))
        = (Fintype.card G : ℂ) * (Fintype.card ↥(stab χ) : ℂ) * ∑ u : G, Uc u * Uc u⁻¹ := by
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun h _ => hstep_h h), Finset.sum_const,
          Finset.card_univ, hinner, nsmul_eq_mul]
      ring
    -- Per-`g` reduction of the `A`-sum via character orthogonality on `A` (`hasum`).
    have hg_eq : ∀ g : G,
        (∑ a : A, (V χ U).character ⟨a, g⟩ * (V χ U).character ⟨a, g⟩⁻¹)
        = (Fintype.card ↥(stab χ) : ℂ)⁻¹ * (Fintype.card ↥(stab χ) : ℂ)⁻¹ *
            ∑ h : G, ∑ h' : G,
              (if h * g * h'⁻¹ ∈ stab χ then (Fintype.card A : ℂ) else 0)
                * Uc (h * g * h⁻¹) * Uc (h' * g⁻¹ * h'⁻¹) := by
      intro g
      have hstep : ∀ a : A,
          (V χ U).character ⟨a, g⟩ * (V χ U).character ⟨a, g⟩⁻¹
          = (Fintype.card ↥(stab χ) : ℂ)⁻¹ * (Fintype.card ↥(stab χ) : ℂ)⁻¹ *
              ∑ h : G, ∑ h' : G,
                (χ ((φ h : MulAut A) a) : ℂ) * (χ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ)
                  * (Uc (h * g * h⁻¹) * Uc (h' * g⁻¹ * h'⁻¹)) := by
        intro a
        rw [hcf a g, hinv a g, hcf ((φ g⁻¹ : MulAut A) a⁻¹) g⁻¹, mul_mul_mul_comm,
            Finset.sum_mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun h _ => ?_
        refine Finset.sum_congr rfl fun h' _ => ?_
        ring
      rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum]
      congr 1
      -- pull the `∑ a` inside past `∑ h, ∑ h'` and apply `hasum`.
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h' _ => ?_
      rw [← Finset.sum_mul, hasum g h h']
      ring
    -- Final norm computation.
    have hconv : (∑ x : A ⋊[φ] G, (V χ U).character x * (V χ U).character x⁻¹)
        = ∑ a : A, ∑ g : G, (V χ U).character ⟨a, g⟩ * (V χ U).character ⟨a, g⟩⁻¹ := by
      rw [← Equiv.sum_comp (SemidirectProduct.equivProd (φ := φ)).symm, Fintype.sum_prod_type]
      rfl
    rw [FDRep.simple_iff_char_is_norm_one, hconv, Finset.sum_comm,
        Finset.sum_congr rfl (fun g _ => hg_eq g)]
    -- `∑ g, s⁻² ∑h∑h' (if .. cardA)·Uc·Uc`; factor out constants and `cardA`.
    rw [← Finset.mul_sum]
    have hcardA : ∀ g : G, (∑ h : G, ∑ h' : G,
        (if h * g * h'⁻¹ ∈ stab χ then (Fintype.card A : ℂ) else 0)
          * Uc (h * g * h⁻¹) * Uc (h' * g⁻¹ * h'⁻¹))
        = (Fintype.card A : ℂ) * ∑ h : G, ∑ h' : G,
            (if h * g * h'⁻¹ ∈ stab χ then (1 : ℂ) else 0)
              * Uc (h * g * h⁻¹) * Uc (h' * g⁻¹ * h'⁻¹) := by
      intro g
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h' _ => ?_
      by_cases hmem : h * g * h'⁻¹ ∈ stab χ
      · rw [if_pos hmem, if_pos hmem]; ring
      · rw [if_neg hmem, if_neg hmem]; ring
    rw [Finset.sum_congr rfl (fun g _ => hcardA g), ← Finset.mul_sum, hreindex, hUnorm]
    -- Now the scalar identity `s⁻² · cardA · (cardG · s · s) = cardA · cardG = card (A⋊G)`.
    have hs_ne : (Fintype.card ↥(stab χ) : ℂ) ≠ 0 := by
      have : Fintype.card ↥(stab χ) ≠ 0 := Fintype.card_ne_zero
      exact_mod_cast this
    have hcard : (Nat.card (A ⋊[φ] G) : ℂ) = (Fintype.card A : ℂ) * (Fintype.card G : ℂ) := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_congr (SemidirectProduct.equivProd (φ := φ)), Fintype.card_prod]
      push_cast
      ring
    rw [hcard]
    field_simp
  -- Part (ii): pairwise non-isomorphism (hoisted as `hclassify` so part (iii) can reuse it).
  have hclassify :
      ∀ (χ₁ χ₂ : A →* ℂˣ)
        (U₁ : FDRep ℂ ↥(stab χ₁)) (U₂ : FDRep ℂ ↥(stab χ₂)),
        Simple U₁ → Simple U₂ →
        Nonempty (V χ₁ U₁ ≅ V χ₂ U₂) →
        ∃ (g : G) (hg : dualSmul g χ₁ = χ₂),
          Nonempty (U₂ ≅ transport g χ₁ χ₂ hg U₁) := by
    -- Part (ii): pairwise non-isomorphism.
    -- Strategy: an isomorphism `V χ₁ U₁ ≅ V χ₂ U₂` forces equal characters; feeding the
    -- character formula (iv) into the (unnormalized) inner product
    -- `∑_x χ_{V χ₁ U₁}(x) χ_{V χ₂ U₂}(x⁻¹) ≠ 0` forces the orbit data to match, i.e.
    -- `dualSmul g χ₁ = χ₂` for some `g`, and then (via `_htransport` + a same-orbit Mackey
    -- computation and `char_orthonormal`) `U₂ ≅ g(U₁) = transport g χ₁ χ₂ hg U₁`.
    intro χ₁ χ₂ U₁ U₂ hU₁ hU₂ hiso
    classical
    obtain ⟨e⟩ := hiso
    haveI : Fintype (A ⋊[φ] G) :=
      Fintype.ofEquiv (A × G) (SemidirectProduct.equivProd (φ := φ)).symm
    -- Generic helpers (independent of the specific χ, U), mirroring Part (i).
    have hinv : ∀ (a : A) (g : G),
        (⟨a, g⟩ : A ⋊[φ] G)⁻¹ = ⟨(φ g⁻¹ : MulAut A) a⁻¹, g⁻¹⟩ := by
      intro a g
      apply SemidirectProduct.ext
      · exact SemidirectProduct.inv_left _
      · exact SemidirectProduct.inv_right _
    have hds_mul : ∀ (p q : G) (ν : A →* ℂˣ), dualSmul p (dualSmul q ν) = dualSmul (p * q) ν := by
      intro p q ν
      ext a
      rw [_hdual, _hdual, _hdual]
      congr 1
      have : (φ (p * q)⁻¹ : MulAut A) a = (φ q⁻¹ : MulAut A) ((φ p⁻¹ : MulAut A) a) := by
        rw [mul_inv_rev, map_mul]; rfl
      rw [this]
    have hds_one : ∀ (ν : A →* ℂˣ), dualSmul 1 ν = ν := by
      intro ν; ext a; rw [_hdual]; simp
    have hcomp_eq : ∀ (ν : A →* ℂˣ) (h : G) (a : A),
        (ν ((φ h : MulAut A) a) : ℂˣ) = dualSmul h⁻¹ ν a := by
      intro ν h a; rw [_hdual]; simp
    -- Extended class function: `U.character` on the stabilizer, zero elsewhere.
    set Uc : (ξ : A →* ℂˣ) → FDRep ℂ ↥(stab ξ) → G → ℂ :=
      (fun ξ W y => if h : y ∈ stab ξ then W.character ⟨y, h⟩ else 0) with hUc_def
    have hUc_app : ∀ (ξ : A →* ℂˣ) (W : FDRep ℂ ↥(stab ξ)) (y : G),
        Uc ξ W y = if h : y ∈ stab ξ then W.character ⟨y, h⟩ else 0 := by
      intro ξ W y; rw [hUc_def]
    -- Reformulated character formula (iv), generic in `(ξ, W)`.
    have hcf : ∀ (ξ : A →* ℂˣ) (W : FDRep ℂ ↥(stab ξ)), Simple W → ∀ (a : A) (g : G),
        (V ξ W).character ⟨a, g⟩
          = (Fintype.card ↥(stab ξ) : ℂ)⁻¹ *
              ∑ h : G, (ξ ((φ h : MulAut A) a) : ℂ) * Uc ξ W (h * g * h⁻¹) := by
      intro ξ W hW a g
      rw [character_formula ξ W hW a g]
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : h * g * h⁻¹ ∈ stab ξ
      · rw [dif_pos hh, hUc_app]; simp only [dif_pos hh]
      · rw [dif_neg hh, hUc_app]; simp only [dif_neg hh, mul_zero]
    -- Mixed `A`-orthogonality: the two character factors sum over `A` to `|A|` exactly when the
    -- two orbit conditions coincide, i.e. `dualSmul h⁻¹ ξ₁ = dualSmul (g h'⁻¹) ξ₂`.
    have hasum : ∀ (ξ₁ ξ₂ : A →* ℂˣ) (g h h' : G),
        (∑ a : A, (ξ₁ ((φ h : MulAut A) a) : ℂ) *
            (ξ₂ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ))
          = if dualSmul h⁻¹ ξ₁ = dualSmul (g * h'⁻¹) ξ₂ then (Fintype.card A : ℂ) else 0 := by
      intro ξ₁ ξ₂ g h h'
      set ψ : A →* ℂˣ :=
        (ξ₁.comp (φ h : MulAut A).toMonoidHom) * (ξ₂.comp (φ (h' * g⁻¹) : MulAut A).toMonoidHom)⁻¹
        with hψ_def
      have hψ_val : ∀ a : A, ((ψ a : ℂˣ) : ℂ) =
          (ξ₁ ((φ h : MulAut A) a) : ℂ) *
            (ξ₂ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ) := by
        intro a
        have hfac : (φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)
            = ((φ (h' * g⁻¹) : MulAut A) a)⁻¹ := by
          rw [map_mul]; simp
        rw [hfac, hψ_def]; simp
      have hsum_eq : (∑ a : A, (ξ₁ ((φ h : MulAut A) a) : ℂ) *
            (ξ₂ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ))
          = ∑ a : A, ((ψ a : ℂˣ) : ℂ) := by
        apply Finset.sum_congr rfl; intro a _; rw [hψ_val a]
      rw [hsum_eq, sum_monoidHom_units_cast_eq ψ]
      have hiff : ψ = 1 ↔ dualSmul h⁻¹ ξ₁ = dualSmul (g * h'⁻¹) ξ₂ := by
        rw [hψ_def]
        have e1 : (ξ₁.comp (φ h : MulAut A).toMonoidHom) = dualSmul h⁻¹ ξ₁ := by
          refine MonoidHom.ext fun a => ?_
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
          exact hcomp_eq ξ₁ h a
        have e2 : (ξ₂.comp (φ (h' * g⁻¹) : MulAut A).toMonoidHom) = dualSmul (g * h'⁻¹) ξ₂ := by
          refine MonoidHom.ext fun a => ?_
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
          rw [hcomp_eq ξ₂ (h' * g⁻¹) a]
          congr 2
          group
        rw [e1, e2, monoidHom_mul_inv_eq_one]
      by_cases hc : dualSmul h⁻¹ ξ₁ = dualSmul (g * h'⁻¹) ξ₂
      · rw [if_pos hc, if_pos (hiff.mpr hc)]
      · rw [if_neg hc, if_neg (fun hcc => hc (hiff.mp hcc))]
    -- Semidirect-product sum splits as a product over `A × G`.
    have hconv : ∀ (ξ₁ ξ₂ : A →* ℂˣ) (W₁ : FDRep ℂ ↥(stab ξ₁)) (W₂ : FDRep ℂ ↥(stab ξ₂)),
        (∑ x : A ⋊[φ] G, (V ξ₁ W₁).character x * (V ξ₂ W₂).character x⁻¹)
          = ∑ a : A, ∑ g : G, (V ξ₁ W₁).character ⟨a, g⟩ * (V ξ₂ W₂).character ⟨a, g⟩⁻¹ := by
      intro ξ₁ ξ₂ W₁ W₂
      rw [← Equiv.sum_comp (SemidirectProduct.equivProd (φ := φ)).symm, Fintype.sum_prod_type]
      rfl
    -- The half-reduced mixed inner product: `A`-orthogonality applied, `G`-sums not yet collapsed.
    have hcross : ∀ (ξ₁ ξ₂ : A →* ℂˣ) (W₁ : FDRep ℂ ↥(stab ξ₁)) (W₂ : FDRep ℂ ↥(stab ξ₂)),
        Simple W₁ → Simple W₂ →
        (∑ x : A ⋊[φ] G, (V ξ₁ W₁).character x * (V ξ₂ W₂).character x⁻¹)
          = (Fintype.card ↥(stab ξ₁) : ℂ)⁻¹ * (Fintype.card ↥(stab ξ₂) : ℂ)⁻¹ *
              ∑ g : G, ∑ h : G, ∑ h' : G,
                (if dualSmul h⁻¹ ξ₁ = dualSmul (g * h'⁻¹) ξ₂ then (Fintype.card A : ℂ) else 0)
                  * Uc ξ₁ W₁ (h * g * h⁻¹) * Uc ξ₂ W₂ (h' * g⁻¹ * h'⁻¹) := by
      intro ξ₁ ξ₂ W₁ W₂ hW₁ hW₂
      have hgeq : ∀ g : G,
          (∑ a : A, (V ξ₁ W₁).character ⟨a, g⟩ * (V ξ₂ W₂).character ⟨a, g⟩⁻¹)
          = (Fintype.card ↥(stab ξ₁) : ℂ)⁻¹ * (Fintype.card ↥(stab ξ₂) : ℂ)⁻¹ *
              ∑ h : G, ∑ h' : G,
                (if dualSmul h⁻¹ ξ₁ = dualSmul (g * h'⁻¹) ξ₂ then (Fintype.card A : ℂ) else 0)
                  * Uc ξ₁ W₁ (h * g * h⁻¹) * Uc ξ₂ W₂ (h' * g⁻¹ * h'⁻¹) := by
        intro g
        have hstep : ∀ a : A,
            (V ξ₁ W₁).character ⟨a, g⟩ * (V ξ₂ W₂).character ⟨a, g⟩⁻¹
            = (Fintype.card ↥(stab ξ₁) : ℂ)⁻¹ * (Fintype.card ↥(stab ξ₂) : ℂ)⁻¹ *
                ∑ h : G, ∑ h' : G,
                  (ξ₁ ((φ h : MulAut A) a) : ℂ) *
                    (ξ₂ ((φ h' : MulAut A) ((φ g⁻¹ : MulAut A) a⁻¹)) : ℂ)
                    * (Uc ξ₁ W₁ (h * g * h⁻¹) * Uc ξ₂ W₂ (h' * g⁻¹ * h'⁻¹)) := by
          intro a
          rw [hcf ξ₁ W₁ hW₁ a g, hinv a g, hcf ξ₂ W₂ hW₂ ((φ g⁻¹ : MulAut A) a⁻¹) g⁻¹,
              mul_mul_mul_comm, Finset.sum_mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun h _ => ?_
          refine Finset.sum_congr rfl fun h' _ => ?_
          ring
        rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h' _ => ?_
        rw [← Finset.sum_mul, hasum ξ₁ ξ₂ g h h']
        ring
      rw [hconv ξ₁ ξ₂ W₁ W₂, Finset.sum_comm,
        Finset.sum_congr rfl (fun g _ => hgeq g), ← Finset.mul_sum]
    -- The cross inner product is nonzero, because the isomorphism `e` equates the characters and
    -- `V χ₁ U₁` is simple (norm one).
    have hV1simple : Simple (V χ₁ U₁) := hVsimple χ₁ U₁ hU₁
    have hchar_eq : (V χ₁ U₁).character = (V χ₂ U₂).character := FDRep.char_iso e
    have hcross_ne :
        (∑ x : A ⋊[φ] G, (V χ₁ U₁).character x * (V χ₂ U₂).character x⁻¹) ≠ 0 := by
      have hrw : (∑ x : A ⋊[φ] G, (V χ₁ U₁).character x * (V χ₂ U₂).character x⁻¹)
          = ∑ x : A ⋊[φ] G, (V χ₁ U₁).character x * (V χ₁ U₁).character x⁻¹ := by
        refine Finset.sum_congr rfl fun x _ => ?_; rw [← hchar_eq]
      rw [hrw, (FDRep.simple_iff_char_is_norm_one (V χ₁ U₁)).mp hV1simple]
      have hpos : 0 < Nat.card (A ⋊[φ] G) := Nat.card_pos
      exact_mod_cast hpos.ne'
    -- Existence of the intertwining element `g`: if no `g` had `dualSmul g χ₁ = χ₂`, then every
    -- orbit condition would be false, forcing the cross inner product to vanish, a contradiction.
    have hgexists : ∃ g : G, dualSmul g χ₁ = χ₂ := by
      by_contra hng
      apply hcross_ne
      rw [hcross χ₁ χ₂ U₁ U₂ hU₁ hU₂]
      have hsum0 : (∑ g : G, ∑ h : G, ∑ h' : G,
          (if dualSmul h⁻¹ χ₁ = dualSmul (g * h'⁻¹) χ₂ then (Fintype.card A : ℂ) else 0)
            * Uc χ₁ U₁ (h * g * h⁻¹) * Uc χ₂ U₂ (h' * g⁻¹ * h'⁻¹)) = 0 := by
        refine Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun h _ =>
          Finset.sum_eq_zero fun h' _ => ?_
        have hcondfalse : ¬ (dualSmul h⁻¹ χ₁ = dualSmul (g * h'⁻¹) χ₂) := by
          intro hcond
          have hh := congrArg (dualSmul (h' * g⁻¹)) hcond
          rw [hds_mul, hds_mul, show h' * g⁻¹ * (g * h'⁻¹) = 1 from by group, hds_one] at hh
          exact hng ⟨h' * g⁻¹ * h⁻¹, hh⟩
        rw [if_neg hcondfalse, zero_mul, zero_mul]
      rw [hsum0, mul_zero]
    obtain ⟨g, hg⟩ := hgexists
    refine ⟨g, hg, ?_⟩
    set W := transport g χ₁ χ₂ hg U₁ with hW_def
    -- Conjugation by `g` is a bijection `stab χ₂ ≃ stab χ₁` (`s ↦ g⁻¹ s g`), since `χ₂ = g · χ₁`.
    have hconj_mem : ∀ s : G, s ∈ stab χ₂ ↔ g⁻¹ * s * g ∈ stab χ₁ := by
      intro s
      rw [_hstab, _hstab, ← hg, hds_mul]
      constructor
      · intro H
        have hH := congrArg (dualSmul g⁻¹) H
        rw [hds_mul, hds_mul, show g⁻¹ * (s * g) = g⁻¹ * s * g from by group,
          inv_mul_cancel, hds_one] at hH
        exact hH
      · intro H
        have hH := congrArg (dualSmul g) H
        rw [hds_mul, show g * (g⁻¹ * s * g) = s * g from by group] at hH
        exact hH
    let cj : ↥(stab χ₂) ≃ ↥(stab χ₁) :=
      { toFun := fun s => ⟨g⁻¹ * (s : G) * g, (hconj_mem s).mp s.2⟩
        invFun := fun t => ⟨g * (t : G) * g⁻¹, by
          rw [hconj_mem]; convert t.2 using 2; group⟩
        left_inv := by
          intro s; apply Subtype.ext; change g * (g⁻¹ * (s : G) * g) * g⁻¹ = (s : G); group
        right_inv := by
          intro t; apply Subtype.ext; change g⁻¹ * (g * (t : G) * g⁻¹) * g = (t : G); group }
    have hcj_coe : ∀ s : ↥(stab χ₂), (cj s : G) = g⁻¹ * (s : G) * g := fun _ => rfl
    have hcj_inv : ∀ s : ↥(stab χ₂), cj (s⁻¹) = (cj s)⁻¹ := fun s => by
      apply Subtype.ext
      simp only [hcj_coe, Subgroup.coe_inv]; group
    have hcard_stab : (Fintype.card ↥(stab χ₂) : ℂ) = (Fintype.card ↥(stab χ₁) : ℂ) := by
      exact_mod_cast Fintype.card_congr cj
    -- `W = g(U₁)` has character `χ_W(s) = χ_{U₁}(g⁻¹ s g)` on `stab χ₂` (characterising hypothesis).
    have hWchar : ∀ s : ↥(stab χ₂), W.character s = U₁.character (cj s) := by
      intro s
      rw [hW_def, _htransport g χ₁ χ₂ hg U₁ s ((hconj_mem (s : G)).mp s.2)]
      exact congrArg U₁.character (Subtype.ext rfl)
    -- Step A: `W` is simple (its character has norm one, via the conjugation bijection + `U₁` simple).
    have hWsimple : Simple W := by
      rw [FDRep.simple_iff_char_is_norm_one]
      have hbij : (∑ s : ↥(stab χ₂), W.character s * W.character s⁻¹)
          = ∑ t : ↥(stab χ₁), U₁.character t * U₁.character t⁻¹ := by
        rw [← Equiv.sum_comp cj (fun t => U₁.character t * U₁.character t⁻¹)]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hWchar s, hWchar (s⁻¹), hcj_inv s]
      rw [hbij, (FDRep.simple_iff_char_is_norm_one U₁).mp hU₁]
      exact_mod_cast Nat.card_congr cj.symm
    -- Step B: `V χ₂ W` and `V χ₁ U₁` have equal characters (basepoint independence of induction).
    have hcharVeq : (V χ₂ W).character = (V χ₁ U₁).character := by
      funext x
      obtain ⟨a, g'⟩ := x
      rw [hcf χ₂ W hWsimple a g', hcf χ₁ U₁ hU₁ a g', hcard_stab]
      congr 1
      rw [← Equiv.sum_comp (Equiv.mulLeft g)
        (fun h => (χ₂ ((φ h : MulAut A) a) : ℂ) * Uc χ₂ W (h * g' * h⁻¹))]
      refine Finset.sum_congr rfl fun h _ => ?_
      change (χ₂ ((φ (g * h) : MulAut A) a) : ℂ) * Uc χ₂ W ((g * h) * g' * (g * h)⁻¹)
          = (χ₁ ((φ h : MulAut A) a) : ℂ) * Uc χ₁ U₁ (h * g' * h⁻¹)
      -- Character factor: `χ₂((φ(g h))a) = χ₁((φ h)a)` since `dualSmul (g h)⁻¹ χ₂ = dualSmul h⁻¹ χ₁`.
      have hchi : (χ₂ ((φ (g * h) : MulAut A) a) : ℂ) = (χ₁ ((φ h : MulAut A) a) : ℂ) := by
        have h3 : dualSmul (g * h)⁻¹ χ₂ = dualSmul h⁻¹ χ₁ := by
          rw [← hg, hds_mul, show (g * h)⁻¹ * g = h⁻¹ from by group]
        have hu : (χ₂ ((φ (g * h) : MulAut A) a) : ℂˣ) = (χ₁ ((φ h : MulAut A) a) : ℂˣ) := by
          rw [hcomp_eq χ₂ (g * h) a, hcomp_eq χ₁ h a, h3]
        exact congrArg Units.val hu
      -- Induced-datum factor: `Uc χ₂ W ((g h) g' (g h)⁻¹) = Uc χ₁ U₁ (h g' h⁻¹)`.
      have hUcW : Uc χ₂ W ((g * h) * g' * (g * h)⁻¹) = Uc χ₁ U₁ (h * g' * h⁻¹) := by
        rw [show (g * h) * g' * (g * h)⁻¹ = g * (h * g' * h⁻¹) * g⁻¹ from by group]
        have hconjeq : g⁻¹ * (g * (h * g' * h⁻¹) * g⁻¹) * g = h * g' * h⁻¹ := by group
        by_cases hz : (h * g' * h⁻¹) ∈ stab χ₁
        · have hgz : g * (h * g' * h⁻¹) * g⁻¹ ∈ stab χ₂ := by
            rw [hconj_mem, hconjeq]; exact hz
          rw [hUc_app, dif_pos hgz, hUc_app, dif_pos hz,
            hWchar ⟨g * (h * g' * h⁻¹) * g⁻¹, hgz⟩]
          congr 1
          apply Subtype.ext
          rw [hcj_coe]
          change g⁻¹ * (g * (h * g' * h⁻¹) * g⁻¹) * g = (h * g' * h⁻¹)
          group
        · have hgz : g * (h * g' * h⁻¹) * g⁻¹ ∉ stab χ₂ := by
            rw [hconj_mem, hconjeq]; exact hz
          rw [hUc_app, dif_neg hgz, hUc_app, dif_neg hz]
      rw [hchi, hUcW]
    -- Steps C–D: same-orbit Mackey reduction + `char_orthonormal`.
    -- Conjugation invariance and support of the extended class functions.
    have hUc_conj : ∀ (ξ : A →* ℂˣ) (W' : FDRep ℂ ↥(stab ξ)) (k y : G),
        k ∈ stab ξ → Uc ξ W' (k * y * k⁻¹) = Uc ξ W' y := by
      intro ξ W' k y hk
      by_cases hy : y ∈ stab ξ
      · have hconj : k * y * k⁻¹ ∈ stab ξ :=
          (stab ξ).mul_mem ((stab ξ).mul_mem hk hy) ((stab ξ).inv_mem hk)
        rw [hUc_app, hUc_app, dif_pos hconj, dif_pos hy]
        have hval : (⟨k * y * k⁻¹, hconj⟩ : ↥(stab ξ)) = ⟨k, hk⟩ * ⟨y, hy⟩ * ⟨k, hk⟩⁻¹ := by
          apply Subtype.ext; rfl
        rw [hval, FDRep.char_conj]
      · have hconj : k * y * k⁻¹ ∉ stab ξ := by
          intro hc; apply hy
          have hrw : y = k⁻¹ * (k * y * k⁻¹) * k := by group
          rw [hrw]
          exact (stab ξ).mul_mem ((stab ξ).mul_mem ((stab ξ).inv_mem hk) hc) hk
        rw [hUc_app, hUc_app, dif_neg hconj, dif_neg hy]
    have hUc_vanish : ∀ (ξ : A →* ℂˣ) (W' : FDRep ℂ ↥(stab ξ)) (y : G),
        y ∉ stab ξ → Uc ξ W' y = 0 := by
      intro ξ W' y hy; rw [hUc_app, dif_neg hy]
    -- For `ξ₁ = ξ₂ = ξ`, the orbit condition collapses to a stabilizer membership.
    have hcond_stab : ∀ (ξ : A →* ℂˣ) (g₀ h h' : G),
        (dualSmul h⁻¹ ξ = dualSmul (g₀ * h'⁻¹) ξ) ↔ h * g₀ * h'⁻¹ ∈ stab ξ := by
      intro ξ g₀ h h'
      rw [_hstab]
      constructor
      · intro H
        have hH := congrArg (dualSmul h) H
        rw [hds_mul, hds_mul, mul_inv_cancel, hds_one] at hH
        rw [← mul_assoc] at hH
        exact hH.symm
      · intro H
        have hH := congrArg (dualSmul h⁻¹) H
        rw [hds_mul, show h⁻¹ * (h * g₀ * h'⁻¹) = g₀ * h'⁻¹ from by group] at hH
        exact hH.symm
    -- Mackey collapse of the conditional triple sum (two conjugation reindexings), mirroring
    -- Part (i)'s norm computation but for two class functions `f₁, f₂`.
    have hcollapse : ∀ (ξ : A →* ℂˣ) (f₁ f₂ : G → ℂ),
        (∀ y : G, y ∉ stab ξ → f₁ y = 0) →
        (∀ (k y : G), k ∈ stab ξ → f₂ (k * y * k⁻¹) = f₂ y) →
        (∑ g₀ : G, ∑ h : G, ∑ h' : G,
          (if h * g₀ * h'⁻¹ ∈ stab ξ then (1 : ℂ) else 0)
            * f₁ (h * g₀ * h⁻¹) * f₂ (h' * g₀⁻¹ * h'⁻¹))
        = (Fintype.card G : ℂ) * (Fintype.card ↥(stab ξ) : ℂ) * ∑ u : G, f₁ u * f₂ u⁻¹ := by
      intro ξ f₁ f₂ hf₁ hf₂
      have hstep_h : ∀ h : G,
          (∑ g₀ : G, ∑ h' : G,
            (if h * g₀ * h'⁻¹ ∈ stab ξ then (1 : ℂ) else 0) * f₁ (h * g₀ * h⁻¹)
              * f₂ (h' * g₀⁻¹ * h'⁻¹))
          = ∑ u : G, ∑ t : G,
            (if u * t ∈ stab ξ then (1 : ℂ) else 0) * f₁ u * f₂ (t⁻¹ * u⁻¹ * t) := by
        intro h
        let Φ : (G × G) ≃ (G × G) :=
          { toFun := fun p => (h * p.1 * h⁻¹, h * p.2⁻¹)
            invFun := fun q => (h⁻¹ * q.1 * h, q.2⁻¹ * h)
            left_inv := by rintro ⟨g₀, h'⟩; refine Prod.ext ?_ ?_ <;> · simp only []; group
            right_inv := by rintro ⟨u, t⟩; refine Prod.ext ?_ ?_ <;> · simp only []; group }
        rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
        refine Fintype.sum_equiv Φ _ _ ?_
        rintro ⟨g₀, h'⟩
        change (if h * g₀ * h'⁻¹ ∈ stab ξ then (1 : ℂ) else 0) * f₁ (h * g₀ * h⁻¹)
              * f₂ (h' * g₀⁻¹ * h'⁻¹)
            = (if h * g₀ * h⁻¹ * (h * h'⁻¹) ∈ stab ξ then (1 : ℂ) else 0) * f₁ (h * g₀ * h⁻¹)
              * f₂ ((h * h'⁻¹)⁻¹ * (h * g₀ * h⁻¹)⁻¹ * (h * h'⁻¹))
        rw [show h * g₀ * h⁻¹ * (h * h'⁻¹) = h * g₀ * h'⁻¹ from by group,
            show (h * h'⁻¹)⁻¹ * (h * g₀ * h⁻¹)⁻¹ * (h * h'⁻¹) = h' * g₀⁻¹ * h'⁻¹ from by group]
      have hinner : (∑ u : G, ∑ t : G,
            (if u * t ∈ stab ξ then (1 : ℂ) else 0) * f₁ u * f₂ (t⁻¹ * u⁻¹ * t))
          = (Fintype.card ↥(stab ξ) : ℂ) * ∑ u : G, f₁ u * f₂ u⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : u ∈ stab ξ
        · have hkey : ∀ t : G, (if u * t ∈ stab ξ then (1 : ℂ) else 0) * f₂ (t⁻¹ * u⁻¹ * t)
              = if t ∈ stab ξ then f₂ u⁻¹ else 0 := by
            intro t
            by_cases ht : t ∈ stab ξ
            · have hut : u * t ∈ stab ξ := (stab ξ).mul_mem hu ht
              rw [if_pos hut, if_pos ht, one_mul]
              have hc := hf₂ t⁻¹ u⁻¹ ((stab ξ).inv_mem ht)
              rw [inv_inv] at hc
              exact hc
            · have hut : u * t ∉ stab ξ := by
                intro hcc; apply ht
                have htt : t = u⁻¹ * (u * t) := by group
                rw [htt]; exact (stab ξ).mul_mem ((stab ξ).inv_mem hu) hcc
              rw [if_neg hut, if_neg ht, zero_mul]
          have hrw : ∀ t : G,
              (if u * t ∈ stab ξ then (1 : ℂ) else 0) * f₁ u * f₂ (t⁻¹ * u⁻¹ * t)
              = f₁ u * ((if u * t ∈ stab ξ then (1 : ℂ) else 0) * f₂ (t⁻¹ * u⁻¹ * t)) := by
            intro t; ring
          rw [Finset.sum_congr rfl (fun t _ => hrw t), ← Finset.mul_sum,
              Finset.sum_congr rfl (fun t _ => hkey t), ← Finset.sum_filter, Finset.sum_const,
              ← Fintype.card_subtype (· ∈ stab ξ), nsmul_eq_mul]
          ring
        · have h0 : f₁ u = 0 := hf₁ u hu
          simp only [h0, zero_mul, mul_zero, Finset.sum_const_zero]
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun h _ => hstep_h h), Finset.sum_const,
          Finset.card_univ, hinner, nsmul_eq_mul]
      ring
    -- The same-orbit inner product `⟨χ_{V χ₂ U₂}, χ_{V χ₂ W}⟩`, computed two ways.
    have hcrossval := hcross χ₂ χ₂ U₂ W hU₂ hWsimple
    have htrip : (∑ g₀ : G, ∑ h : G, ∑ h' : G,
          (if dualSmul h⁻¹ χ₂ = dualSmul (g₀ * h'⁻¹) χ₂ then (Fintype.card A : ℂ) else 0)
            * Uc χ₂ U₂ (h * g₀ * h⁻¹) * Uc χ₂ W (h' * g₀⁻¹ * h'⁻¹))
        = (Fintype.card A : ℂ) * ((Fintype.card G : ℂ) * (Fintype.card ↥(stab χ₂) : ℂ) *
            ∑ u : G, Uc χ₂ U₂ u * Uc χ₂ W u⁻¹) := by
      rw [← hcollapse χ₂ (Uc χ₂ U₂) (Uc χ₂ W) (fun y hy => hUc_vanish χ₂ U₂ y hy)
            (fun k y hk => hUc_conj χ₂ W k y hk), Finset.mul_sum]
      refine Finset.sum_congr rfl fun g₀ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h' _ => ?_
      by_cases hc : h * g₀ * h'⁻¹ ∈ stab χ₂
      · rw [if_pos ((hcond_stab χ₂ g₀ h h').mpr hc), if_pos hc]; ring
      · rw [if_neg (fun hcc => hc ((hcond_stab χ₂ g₀ h h').mp hcc)), if_neg hc]; ring
    have hval_card : (∑ x : A ⋊[φ] G, (V χ₂ U₂).character x * (V χ₂ W).character x⁻¹)
        = (Nat.card (A ⋊[φ] G) : ℂ) := by
      have hce := hcharVeq.trans hchar_eq
      rw [show (∑ x : A ⋊[φ] G, (V χ₂ U₂).character x * (V χ₂ W).character x⁻¹)
            = ∑ x : A ⋊[φ] G, (V χ₂ U₂).character x * (V χ₂ U₂).character x⁻¹ from
          Finset.sum_congr rfl fun x _ => by rw [hce]]
      exact (FDRep.simple_iff_char_is_norm_one (V χ₂ U₂)).mp (hVsimple χ₂ U₂ hU₂)
    rw [htrip, hval_card] at hcrossval
    -- The restricted-orbit inner product is nonzero.
    have hS_ne : (∑ u : G, Uc χ₂ U₂ u * Uc χ₂ W u⁻¹) ≠ 0 := by
      intro hS0
      rw [hS0, mul_zero, mul_zero, mul_zero] at hcrossval
      exact (show (Nat.card (A ⋊[φ] G) : ℂ) ≠ 0 from by exact_mod_cast Nat.card_pos.ne')
        hcrossval
    -- Rewrite the extended-support sum as a sum over the stabilizer subgroup.
    have hrestrict : (∑ u : G, Uc χ₂ U₂ u * Uc χ₂ W u⁻¹)
        = ∑ s : ↥(stab χ₂), U₂.character s * W.character s⁻¹ := by
      have hfilter : ∑ u : G, Uc χ₂ U₂ u * Uc χ₂ W u⁻¹
          = ∑ u ∈ Finset.univ.filter (· ∈ stab χ₂), Uc χ₂ U₂ u * Uc χ₂ W u⁻¹ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : u ∈ stab χ₂
        · rw [if_pos hu]
        · rw [if_neg hu, hUc_vanish χ₂ U₂ u hu, zero_mul]
      rw [hfilter, Finset.sum_subtype (p := (· ∈ stab χ₂)) (Finset.univ.filter (· ∈ stab χ₂))
            (fun x => by simp [Finset.mem_filter]) (fun u => Uc χ₂ U₂ u * Uc χ₂ W u⁻¹)]
      refine Finset.sum_congr rfl fun u _ => ?_
      have h1 : Uc χ₂ U₂ ↑u = U₂.character u := by
        rw [hUc_app, dif_pos u.2, Subtype.coe_eta]
      have h2 : Uc χ₂ W (↑u : G)⁻¹ = W.character u⁻¹ := by
        have huinv : ((u : G))⁻¹ ∈ stab χ₂ := (stab χ₂).inv_mem u.2
        rw [hUc_app, dif_pos huinv]
        exact congrArg W.character (Subtype.ext rfl)
      rw [h1, h2]
    -- `char_orthonormal`: a nonzero inner product between simples forces an isomorphism.
    haveI := hU₂
    haveI := hWsimple
    have hs2ne : (Fintype.card ↥(stab χ₂) : ℂ) ≠ 0 := by
      have : Fintype.card ↥(stab χ₂) ≠ 0 := Fintype.card_ne_zero
      exact_mod_cast this
    haveI : Invertible (Fintype.card ↥(stab χ₂) : ℂ) := invertibleOfNonzero hs2ne
    have horth := FDRep.char_orthonormal_fintype U₂ W
    by_contra hcon
    apply hS_ne
    rw [hrestrict]
    have hzero : (∑ s : ↥(stab χ₂), U₂.character s * W.character s⁻¹)
        = (Fintype.card ↥(stab χ₂) : ℂ) • (⅟(Fintype.card ↥(stab χ₂) : ℂ) •
            (∑ s : ↥(stab χ₂), U₂.character s * W.character s⁻¹)) := by
      rw [smul_smul, mul_invOf_self, one_smul]
    rw [hzero, horth, if_neg hcon]
    simp
  refine ⟨hVsimple, hclassify, ?_⟩
  -- Part (iii): completeness, every simple `W` is some `V χ U`.
  -- Strategy: the sum-of-squares count `Σ_{χ,U} dim(V χ U)² = |A ⋊[φ] G|` (from (iv) and the
  -- orbit decomposition) exhausts the regular representation. The orbit-method family
  -- `{V(χ, U) : χ an orbit representative, U an irreducible of stab χ}` consists of pairwise
  -- non-isomorphic simples (parts (i), (ii)) whose squared dimensions already sum to
  -- `|A ⋊[φ] G|`, so `FDRep.complete_of_sum_finrank_sq_eq_card` forces it to exhaust all simples.
  intro W hW
  classical
  haveI : Fintype (A ⋊[φ] G) :=
    Fintype.ofEquiv (A × G) (SemidirectProduct.equivProd (φ := φ)).symm
  haveI : NeZero (Nat.card (A ⋊[φ] G) : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  -- `dualSmul` is a left `G`-action on `Â = (A →* ℂˣ)` (re-derived locally).
  have hds_mul : ∀ (p q : G) (ν : A →* ℂˣ), dualSmul p (dualSmul q ν) = dualSmul (p * q) ν := by
    intro p q ν
    ext a
    rw [_hdual, _hdual, _hdual]
    congr 1
    have : (φ (p * q)⁻¹ : MulAut A) a = (φ q⁻¹ : MulAut A) ((φ p⁻¹ : MulAut A) a) := by
      rw [mul_inv_rev, map_mul]; rfl
    rw [this]
  have hds_one : ∀ (ν : A →* ℂˣ), dualSmul 1 ν = ν := by
    intro ν; ext a; rw [_hdual]; simp
  -- Register the action so the orbit/stabilizer API applies to `Â`.
  letI actSMul : SMul G (A →* ℂˣ) := ⟨dualSmul⟩
  letI actInst : MulAction G (A →* ℂˣ) :=
    { one_smul := hds_one, mul_smul := fun p q ν => (hds_mul p q ν).symm }
  have hsmul_eq : ∀ (g : G) (χ : A →* ℂˣ), g • χ = dualSmul g χ := fun _ _ => rfl
  -- The abstract stabilizer `stab χ` coincides with the group-action stabilizer.
  have hstab_eq : ∀ χ : A →* ℂˣ, MulAction.stabilizer G χ = stab χ := by
    intro χ
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul_eq, _hstab]
  -- `Â` is finite (dual of a finite abelian group), hence so is the orbit space.
  haveI : Finite (A →* ℂˣ) :=
    Finite.of_equiv A (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A ℂ).some.symm.toEquiv
  haveI : Fintype (A →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient G (A →* ℂˣ)) := Fintype.ofFinite _
  -- Positive-order stabilizers carry the char-zero non-vanishing needed for `IrrepDecomp`.
  haveI hNZstab : ∀ (H : Subgroup G), NeZero (Nat.card H : ℂ) :=
    fun _ => ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  -- The orbit-method family, indexed by (orbit representative, irreducible of its stabilizer).
  set Ω := MulAction.orbitRel.Quotient G (A →* ℂˣ) with hΩ
  set χω : Ω → (A →* ℂˣ) := fun ω => Quotient.out ω with hχω
  let Dω : (ω : Ω) → IrrepDecomp ℂ ↥(stab (χω ω)) := fun ω => IrrepDecomp.mk'
  set Wf : (Σ ω : Ω, Fin (Dω ω).n) → FDRep ℂ (A ⋊[φ] G) :=
    fun j => V (χω j.1) ((Dω j.1).columnFDRep j.2) with hWf
  -- (a) Every family member is simple: `columnFDRep` is simple, and part (i) preserves it.
  have hWf_simple : ∀ j, Simple (Wf j) := by
    intro j
    exact hVsimple (χω j.1) ((Dω j.1).columnFDRep j.2) ((Dω j.1).columnFDRep_simple j.2)
  -- (b) The family is pairwise non-isomorphic (uses the classification `hclassify`).
  have hWf_inj : ∀ j j', Nonempty (Wf j ≅ Wf j') → j = j' := by
    rintro ⟨ω, i⟩ ⟨ω', i'⟩ hiso
    simp only [hWf] at hiso
    -- Classification (part ii): the isomorphism forces `χω ω'` into the orbit of `χω ω`.
    obtain ⟨g, hg, hiso2⟩ := hclassify (χω ω) (χω ω')
      ((Dω ω).columnFDRep i) ((Dω ω').columnFDRep i')
      ((Dω ω).columnFDRep_simple i) ((Dω ω').columnFDRep_simple i') hiso
    -- Same orbit ⟹ same orbit class `ω = ω'`.
    have horbit : χω ω' ∈ MulAction.orbit G (χω ω) :=
      MulAction.mem_orbit_iff.mpr ⟨g, by rw [hsmul_eq]; exact hg⟩
    have hωeq : ω = ω' := by
      have e1 : (Quotient.mk'' (χω ω') : Ω) = Quotient.mk'' (χω ω) :=
        Quotient.sound' (MulAction.orbitRel_apply.mpr horbit)
      have o1 : (Quotient.mk'' (χω ω) : Ω) = ω := Quotient.out_eq' ω
      have o2 : (Quotient.mk'' (χω ω') : Ω) = ω' := Quotient.out_eq' ω'
      rw [o1] at e1; rw [o2] at e1; exact e1.symm
    subst hωeq
    -- Within the orbit: `g ∈ stab (χω ω)`, and `transport g χ χ` is a self-conjugation, so
    -- `transport g χ χ hg (colU i) ≅ colU i`; hence `colU i' ≅ colU i` and `i' = i`.
    have hg_mem : g ∈ stab (χω ω) := (_hstab (χω ω) g).mpr hg
    set ge : ↥(stab (χω ω)) := ⟨g, hg_mem⟩ with hge
    have hchar : ∀ s : ↥(stab (χω ω)),
        (transport g (χω ω) (χω ω) hg ((Dω ω).columnFDRep i)).character s
          = ((Dω ω).columnFDRep i).character s := by
      intro s
      have hs : g⁻¹ * (s : G) * g ∈ stab (χω ω) :=
        (stab (χω ω)).mul_mem ((stab (χω ω)).mul_mem ((stab (χω ω)).inv_mem hg_mem) s.2) hg_mem
      rw [_htransport g (χω ω) (χω ω) hg ((Dω ω).columnFDRep i) s hs]
      have hconj : (⟨g⁻¹ * (s : G) * g, hs⟩ : ↥(stab (χω ω))) = ge⁻¹ * s * ge := by
        apply Subtype.ext
        simp [hge]
      rw [hconj]
      have := FDRep.char_conj ((Dω ω).columnFDRep i) (s : ↥(stab (χω ω))) ge⁻¹
      rw [inv_inv] at this
      exact this
    have htiso : Nonempty
        (transport g (χω ω) (χω ω) hg ((Dω ω).columnFDRep i) ≅ (Dω ω).columnFDRep i) :=
      Etingof.charEq_iso _ _ (funext hchar)
    have hii : i' = i :=
      (Dω ω).columnFDRep_injective i' i ⟨hiso2.some ≪≫ htiso.some⟩
    subst hii
    rfl
  -- (c) The squared dimensions sum to `|A ⋊[φ] G|` (orbit-method dimension count).
  have hWf_sum : ∑ j, (Module.finrank ℂ (Wf j)) ^ 2 = Fintype.card (A ⋊[φ] G) := by
    -- Dimension formula: `dim (V χ U) = [G : stab χ] · dim U`, obtained by evaluating the
    -- character formula (iv) at the identity `⟨1, 1⟩` (`char_one`).
    have hdimM : ∀ (χ : A →* ℂˣ) (U : FDRep ℂ ↥(stab χ)), Simple U →
        Module.finrank ℂ (V χ U) = Nat.card (G ⧸ stab χ) * Module.finrank ℂ U := by
      intro χ U hU
      have hchar1 : (Module.finrank ℂ (V χ U) : ℂ)
          = (Fintype.card ↥(stab χ) : ℂ)⁻¹ * (Fintype.card G : ℂ) * (Module.finrank ℂ U : ℂ) := by
        have h1 : (V χ U).character 1 = (Module.finrank ℂ (V χ U) : ℂ) := FDRep.char_one _
        have hone : (1 : A ⋊[φ] G) = ⟨1, 1⟩ := rfl
        rw [hone, character_formula χ U hU 1 1] at h1
        have hterm : ∀ h : G, (if hh : h * 1 * h⁻¹ ∈ stab χ
                then (χ ((φ h : MulAut A) 1) : ℂ) * U.character ⟨h * 1 * h⁻¹, hh⟩ else 0)
              = (Module.finrank ℂ U : ℂ) := by
          intro h
          have hh1 : h * (1 : G) * h⁻¹ = 1 := by group
          simp only [hh1]
          rw [dif_pos (stab χ).one_mem]
          simp only [map_one, Units.val_one, one_mul]
          rw [show (⟨(1 : G), (stab χ).one_mem⟩ : ↥(stab χ)) = 1 from rfl]
          exact FDRep.char_one U
        rw [Finset.sum_congr rfl (fun h _ => hterm h), Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul] at h1
        rw [← h1]; ring
      have hstabne : (Fintype.card ↥(stab χ) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hN : Fintype.card ↥(stab χ) * Module.finrank ℂ (V χ U)
          = Fintype.card G * Module.finrank ℂ U := by
        have hc : (Fintype.card ↥(stab χ) : ℂ) * (Module.finrank ℂ (V χ U) : ℂ)
            = (Fintype.card G : ℂ) * (Module.finrank ℂ U : ℂ) := by
          rw [hchar1]; field_simp
        exact_mod_cast hc
      have hlag : Fintype.card G = Nat.card (G ⧸ stab χ) * Fintype.card ↥(stab χ) := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (stab χ)
        rwa [Nat.card_eq_fintype_card (α := G), Nat.card_eq_fintype_card (α := ↥(stab χ))] at h
      apply Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := ↥(stab χ)))
      rw [hN, hlag]; ring
    -- Per-orbit contribution: `Σ_U dim(V χω U)² = [G:stab] · |G|` using `Σ_U dim(U)² = |stab|`.
    have key : ∀ ω : Ω,
        ∑ i : Fin (Dω ω).n, (Module.finrank ℂ (V (χω ω) ((Dω ω).columnFDRep i))) ^ 2
          = Nat.card (G ⧸ stab (χω ω)) * Fintype.card G := by
      intro ω
      have hpt : ∀ i, (Module.finrank ℂ (V (χω ω) ((Dω ω).columnFDRep i))) ^ 2
          = (Nat.card (G ⧸ stab (χω ω))) ^ 2 *
              (Module.finrank ℂ ((Dω ω).columnFDRep i)) ^ 2 := by
        intro i
        rw [hdimM (χω ω) ((Dω ω).columnFDRep i) ((Dω ω).columnFDRep_simple i)]; ring
      rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Finset.mul_sum,
        (Dω ω).sum_finrank_sq_eq_card (Dω ω).columnFDRep (Dω ω).columnFDRep_simple
          (Dω ω).columnFDRep_injective]
      have hlagω : Fintype.card G
          = Nat.card (G ⧸ stab (χω ω)) * Fintype.card ↥(stab (χω ω)) := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (stab (χω ω))
        rwa [Nat.card_eq_fintype_card (α := G),
          Nat.card_eq_fintype_card (α := ↥(stab (χω ω)))] at h
      rw [hlagω]; ring
    -- Class formula: the orbit sizes `[G:stab]` partition `Â`, giving `Σ_ω [G:stab] = |Â|`.
    have hclass_sum : (∑ ω : Ω, Nat.card (G ⧸ stab (χω ω))) = Fintype.card (A →* ℂˣ) := by
      have hcong : ∀ ω : Ω, Nat.card (G ⧸ stab (χω ω))
          = Nat.card (G ⧸ MulAction.stabilizer G (Quotient.out ω)) := by
        intro ω; rw [hstab_eq (χω ω)]
      rw [Finset.sum_congr rfl (fun ω _ => hcong ω), ← Nat.card_eq_fintype_card,
        Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G (A →* ℂˣ)),
        Nat.card_sigma]
    -- `|Â| = |A|` (dual of a finite abelian group) and `|A ⋊ G| = |A|·|G|`.
    have hcardDual : Fintype.card (A →* ℂˣ) = Fintype.card A := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A ℂ]
    have hcardSemi : Fintype.card A * Fintype.card G = Fintype.card (A ⋊[φ] G) := by
      rw [← Fintype.card_prod]
      exact Fintype.card_congr (SemidirectProduct.equivProd (φ := φ)).symm
    -- Assemble.
    calc ∑ j, (Module.finrank ℂ (Wf j)) ^ 2
        = ∑ ω : Ω, ∑ i : Fin (Dω ω).n,
            (Module.finrank ℂ (V (χω ω) ((Dω ω).columnFDRep i))) ^ 2 := Fintype.sum_sigma _
      _ = ∑ ω : Ω, Nat.card (G ⧸ stab (χω ω)) * Fintype.card G :=
            Finset.sum_congr rfl (fun ω _ => key ω)
      _ = (∑ ω : Ω, Nat.card (G ⧸ stab (χω ω))) * Fintype.card G := by rw [Finset.sum_mul]
      _ = Fintype.card (A →* ℂˣ) * Fintype.card G := by rw [hclass_sum]
      _ = Fintype.card A * Fintype.card G := by rw [hcardDual]
      _ = Fintype.card (A ⋊[φ] G) := hcardSemi
  -- Conclude via the dimension-count completeness criterion.
  obtain ⟨j, hj⟩ := FDRep.complete_of_sum_finrank_sq_eq_card Wf hWf_simple hWf_inj hWf_sum W hW
  exact ⟨χω j.1, (Dω j.1).columnFDRep j.2, (Dω j.1).columnFDRep_simple j.2, hj⟩

end Etingof

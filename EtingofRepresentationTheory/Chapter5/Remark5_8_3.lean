import Mathlib

/-!
# Remark 5.8.3: Dimension of the induced representation

Etingof's Remark 5.8.3 observes that if we choose a representative `x_σ` from every right `H`-coset
`σ` of `G`, then any `f ∈ Ind_H^G V` (in the function-space model) is uniquely determined by the
family `{f(x_σ)}`. Consequently
$$\dim(\operatorname{Ind}_H^G V) = \dim V \cdot (G : H),$$
where `(G : H)` is the index of `H` in `G`.

## Formalization

The induced representation of Etingof's `Definition 5.8.1` is `Representation.ind H.subtype ρ`,
built on the module `Representation.IndV H.subtype ρ` (the tensor model, `H`-coinvariants of
`ℂ[G] ⊗ V`). Etingof's remark reasons about the isomorphic *function-space* (coinduced) model
`Representation.coindV H.subtype ρ = {f : G → V | f(s x) = ρ(s) f(x) for all s ∈ H}`, where the
representative-evaluation observation is transparent.

We formalize the remark in three steps:

* `Etingof.coindVEquivPi`: the `ℂ`-linear equivalence
  `coindV H.subtype ρ ≃ₗ[ℂ] (Quotient (rightRel H) → V)` given by evaluating `f` at a chosen
  representative of each right coset. This is exactly Etingof's statement that `f` is uniquely
  determined by `{f(x_σ)}`.
* `Etingof.indVLinearEquivCoindV`: the `ℂ`-linear equivalence `IndV ≃ₗ[ℂ] coindV` between the
  tensor and function-space models, extracted from Mathlib's finite-index isomorphism
  `Rep.indToCoind` / `Rep.coindToInd`.
* `Etingof.Remark5_8_3`: the dimension formula
  `finrank ℂ (IndV H.subtype ρ) = finrank ℂ V * H.index`.
-/

open Representation Module

namespace Etingof

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Given `g : G`, this is the element `g · x_σ⁻¹` of `H`, where `x_σ = (Quotient.mk'' g).out` is
the chosen representative of the right coset of `g`. It measures how `g` differs from its coset
representative, so that `g = (cosetTwist H g) · x_σ`. -/
noncomputable def cosetTwist (H : Subgroup G) (g : G) : H :=
  ⟨g * (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out⁻¹,
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out' (s₁ := QuotientGroup.rightRel H) g)⟩

@[simp] lemma cosetTwist_coe (H : Subgroup G) (g : G) :
    (cosetTwist H g : G)
      = g * (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out⁻¹ := rfl

/-- **Remark 5.8.3 (evaluation at coset representatives).** A function `f` in the function-space
model `coindV H.subtype ρ` of the induced representation is uniquely determined by its values at a
chosen representative of each right `H`-coset. Concretely, evaluation at `Quotient.out` gives a
`ℂ`-linear equivalence
`coindV H.subtype ρ ≃ₗ[ℂ] (Quotient (QuotientGroup.rightRel H) → V)`.
(Etingof Remark 5.8.3) -/
noncomputable def coindVEquivPi (H : Subgroup G) (ρ : Representation ℂ H V) :
    Representation.coindV H.subtype ρ ≃ₗ[ℂ]
      (Quotient (QuotientGroup.rightRel H) → V) where
  toFun f q := f.1 q.out
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun φ :=
    ⟨fun g => ρ (cosetTwist H g) (φ (Quotient.mk'' g)), by
      rw [Representation.mem_coindV]
      intro s g
      -- The right cosets of `↑s * g` and `g` coincide, so their chosen representatives agree.
      have hmk : (Quotient.mk'' (H.subtype s * g) : Quotient (QuotientGroup.rightRel H))
          = Quotient.mk'' g :=
        Quotient.eq''.mpr (QuotientGroup.rightRel_apply.mpr (by
          have hs : g * (H.subtype s * g)⁻¹ = (s : G)⁻¹ := by
            rw [Subgroup.subtype_apply]; group
          rw [hs]
          exact inv_mem s.2))
      have hout : (Quotient.mk'' (H.subtype s * g)).out = (Quotient.mk'' g).out :=
        congrArg Quotient.out hmk
      -- The twist at `↑s * g` factors as `s` times the twist at `g`.
      have h2 : cosetTwist H (H.subtype s * g) = s * cosetTwist H g := by
        apply Subtype.ext
        simp only [cosetTwist_coe, Subgroup.coe_mul]
        rw [hout, Subgroup.subtype_apply]
        group
      change ρ (cosetTwist H (H.subtype s * g)) (φ (Quotient.mk'' (H.subtype s * g)))
          = ρ s (ρ (cosetTwist H g) (φ (Quotient.mk'' g)))
      rw [hmk, h2, map_mul]
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    -- `f g = ρ (cosetTwist H g) (f x_σ)` by equivariance of `f`.
    change ρ (cosetTwist H g)
        (f.1 (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out) = f.1 g
    have hf := (Representation.mem_coindV H.subtype ρ f.1).mp f.2
        (cosetTwist H g) (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out
    have heq : H.subtype (cosetTwist H g)
        * (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)).out = g := by
      rw [Subgroup.subtype_apply, cosetTwist_coe]; group
    conv_rhs => rw [← heq]
    exact hf.symm
  right_inv φ := by
    funext q
    change ρ (cosetTwist H q.out) (φ (Quotient.mk'' q.out)) = φ q
    -- `mk'' q.out = q`, so the representative is `q.out` itself and the twist is trivial.
    have hq : (Quotient.mk'' q.out : Quotient (QuotientGroup.rightRel H)) = q :=
      Quotient.out_eq' q
    have h1 : cosetTwist H q.out = 1 := by
      apply Subtype.ext
      rw [cosetTwist_coe, show (Quotient.mk'' q.out).out = q.out from by rw [hq]]
      simp
    rw [h1, hq, map_one]
    rfl

/-- **Remark 5.8.3 (tensor vs. function-space model).** For a finite index subgroup `H ≤ G`, the
tensor model `IndV H.subtype ρ` of the induced representation is `ℂ`-linearly equivalent to the
function-space model `coindV H.subtype ρ`. This is Mathlib's finite-index isomorphism
`Ind_H^G V ≅ Coind_H^G V` read off on underlying modules. -/
noncomputable def indVLinearEquivCoindV (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex] (ρ : Representation ℂ H V) :
    Representation.IndV H.subtype ρ ≃ₗ[ℂ] Representation.coindV H.subtype ρ :=
  LinearEquiv.ofLinear
    (Rep.indToCoind (Rep.of ρ)) (Rep.coindToInd (Rep.of ρ))
    (Rep.coindToInd_indToCoind (Rep.of ρ)) (Rep.indToCoind_coindToInd (Rep.of ρ))

/-- **Remark 5.8.3.** The dimension of the induced representation `Ind_H^G V` of a finite index
subgroup `H ≤ G` equals `dim V` times the index `(G : H)`:
$$\dim(\operatorname{Ind}_H^G V) = \dim V \cdot (G : H).$$
(Etingof Remark 5.8.3) -/
theorem Remark5_8_3 (H : Subgroup G) [H.FiniteIndex] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) :
    finrank ℂ (Representation.IndV H.subtype ρ) = finrank ℂ V * H.index := by
  classical
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H)) := inferInstance
  rw [(indVLinearEquivCoindV H ρ).finrank_eq, (coindVEquivPi H ρ).finrank_eq,
    Module.finrank_pi_fintype (R := ℂ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    QuotientGroup.card_quotient_rightRel H, Subgroup.index_eq_card, Nat.card_eq_fintype_card,
    Nat.mul_comm]

end Etingof

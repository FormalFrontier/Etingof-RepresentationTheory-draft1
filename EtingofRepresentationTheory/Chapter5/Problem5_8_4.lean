import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1

/-!
# Problem 5.8.4: transitivity of induction (induction in stages)

**Problem 5.8.4.** Check that if `K ⊂ H ⊂ G` are groups and if `V` is a representation of
`K`, then `Ind_H^G Ind_K^H V` is isomorphic to `Ind_K^G V`.

## Formalization

We take subgroups `K H : Subgroup G` with `K ≤ H`. Induction is the project's
`Etingof.Definition5_8_1` (Mathlib's `Representation.ind` along a subgroup inclusion).

For the inner induction `Ind_K^H` we need `K` viewed as a subgroup of `H`, namely
`K.subgroupOf H`, and the representation `V` of `K` transported to `K.subgroupOf H` along the
canonical isomorphism `K.subgroupOf H ≃* K` (`Subgroup.subgroupOfEquivOfLe`). Write
`ρ' : Representation ℂ (K.subgroupOf H) V` for this transport.

The claim is a `G`-equivariant linear isomorphism between the carrier of
`Ind_H^G (Ind_K^H V)` and the carrier of `Ind_K^G V`.

Statement pass: the proof (assembling the coset/tensor models of the two iterated inductions)
is left as `sorry`.
-/

open CategoryTheory

namespace Etingof

section Problem584

variable {G : Type*} [Group G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The representation `V` of `K`, transported to a representation of `K.subgroupOf H`
(the copy of `K` sitting inside `H`) along `Subgroup.subgroupOfEquivOfLe`. -/
noncomputable def indStagesInnerRep
    (H K : Subgroup G) (hKH : K ≤ H) (ρ : Representation ℂ K V) :
    Representation ℂ (K.subgroupOf H) V :=
  ρ.comp (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom

/-- **Change of source group along an isomorphism.** For an isomorphism `σ : S ≃* K` and a
map `f : K →* G`, inducing `ρ` along `f` and inducing the pulled-back representation `ρ ∘ σ`
along `f ∘ σ` give the *same* underlying module `(ℂ[G] ⊗ V)` and the same `G`-action; only the
subgroup by which one takes coinvariants is reindexed by the bijection `σ`. Hence the two
coinvariant kernels coincide as submodules. -/
theorem indStages_ker_eq {K S : Type*} [Group K] [Group S]
    (fφ : S →* G) (τ' : Representation ℂ S V) (f : K →* G) (σ : S →* K)
    (τ : Representation ℂ K V) (hfφ : fφ = f.comp σ) (hτ : τ' = τ.comp σ)
    (hσ : Function.Bijective σ) :
    Representation.Coinvariants.ker
        (Representation.tprod ((Representation.leftRegular ℂ G).comp fφ) τ') =
      Representation.Coinvariants.ker
        (Representation.tprod ((Representation.leftRegular ℂ G).comp f) τ) := by
  subst hfφ hτ
  have hpt : ∀ (s : S), (Representation.tprod
        ((Representation.leftRegular ℂ G).comp (f.comp σ)) (τ.comp σ)) s
      = (Representation.tprod ((Representation.leftRegular ℂ G).comp f) τ) (σ s) := fun s => rfl
  unfold Representation.Coinvariants.ker
  congr 1
  ext y
  constructor
  · rintro ⟨⟨s, m⟩, rfl⟩
    exact ⟨(σ s, m), by simp only [hpt]⟩
  · rintro ⟨⟨k, m⟩, rfl⟩
    obtain ⟨s, rfl⟩ := hσ.surjective k
    exact ⟨(s, m), by simp only [hpt]⟩

/-- **Induction in stages, abstract form.** For group homomorphisms `φ : S →* H` and `ψ : H →* G`
and a representation `τ` of `S`, the two-step induction `Ind_ψ (Ind_φ τ)` is `G`-equivariantly
isomorphic to the direct induction `Ind_{ψ∘φ} τ`. In the tensor/coinvariants model of `ind` this is
the associativity identity `⟦g ⊗ ⟦h ⊗ v⟧⟧ ↦ ⟦g · ψ(h) ⊗ v⟧`.

Stated as an existence lemma so the two-step reindexing can be supplied later; the surrounding
`ind_ind_iso_ind` reduces the subgroup statement to this via a change-of-source-group relabelling
(`indStages_ker_eq`). -/
theorem ind_stages_exists {S H : Type*} [Group S] [Group H]
    (φ : S →* H) (ψ : H →* G) (τ : Representation ℂ S V) :
    ∃ e : Representation.IndV ψ (Representation.ind φ τ)
            ≃ₗ[ℂ] Representation.IndV (ψ.comp φ) τ,
      ∀ (g : G) x,
        e (Representation.ind ψ (Representation.ind φ τ) g x)
          = Representation.ind (ψ.comp φ) τ g (e x) := by
  sorry

/-- Problem 5.8.4. For `K ≤ H ≤ G` and a representation `ρ` of `K`, the two-step induction
`Ind_H^G (Ind_K^H V)` is `G`-equivariantly isomorphic to the direct induction `Ind_K^G V`. -/
theorem ind_ind_iso_ind
    (H K : Subgroup G) (hKH : K ≤ H) (ρ : Representation ℂ K V) :
    ∃ e : Representation.IndV H.subtype
            (Etingof.Definition5_8_1 (K.subgroupOf H) (indStagesInnerRep H K hKH ρ))
          ≃ₗ[ℂ] Representation.IndV K.subtype ρ,
      ∀ (g : G) x,
        e (Etingof.Definition5_8_1 H
              (Etingof.Definition5_8_1 (K.subgroupOf H) (indStagesInnerRep H K hKH ρ)) g x)
          = Etingof.Definition5_8_1 K ρ g (e x) := by
  classical
  have hσbij : Function.Bijective (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom :=
    (Subgroup.subgroupOfEquivOfLe hKH).bijective
  -- STAGES: `Ind_H^G (Ind_{K.subgroupOf H} ρ') ≅ Ind_{ψ∘φ} ρ'` (abstract induction in stages).
  obtain ⟨e1, he1⟩ := ind_stages_exists (K.subgroupOf H).subtype H.subtype
    (indStagesInnerRep H K hKH ρ)
  -- RELABEL: `Ind_{ψ∘φ} (ρ∘σ) ≅ Ind_K^G ρ`, the two quotients share the module `ℂ[G]⊗V`, the same
  -- `G`-action, and (by `indStages_ker_eq`) equal coinvariant kernels.
  have hker := indStages_ker_eq (V := V)
    (H.subtype.comp (K.subgroupOf H).subtype) (indStagesInnerRep H K hKH ρ)
    K.subtype (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom ρ rfl rfl hσbij
  let relabelLE : Representation.IndV (H.subtype.comp (K.subgroupOf H).subtype)
        (indStagesInnerRep H K hKH ρ) ≃ₗ[ℂ] Representation.IndV K.subtype ρ :=
    Submodule.quotEquivOfEq _ _ hker
  -- the relabelling intertwines the two `ind` actions (both descend the same base map on `ℂ[G]⊗V`)
  have stepB : ∀ (g : G) (y : Representation.IndV (H.subtype.comp (K.subgroupOf H).subtype)
        (indStagesInnerRep H K hKH ρ)),
      relabelLE (Representation.ind (H.subtype.comp (K.subgroupOf H).subtype)
          (indStagesInnerRep H K hKH ρ) g y)
        = Representation.ind K.subtype ρ g (relabelLE y) := by
    have hrel : ∀ w : TensorProduct ℂ (G →₀ ℂ) V,
        relabelLE (Representation.Coinvariants.mk _ w)
          = Representation.Coinvariants.mk _ w := by
      intro w
      exact Submodule.quotEquivOfEq_mk _ _ hker w
    intro g y
    refine Representation.Coinvariants.induction_on y (fun m => ?_)
    rw [Representation.ind_apply, Representation.ind_apply,
      Representation.Coinvariants.map_mk, hrel, hrel,
      Representation.Coinvariants.map_mk]
    rfl
  refine ⟨e1.trans relabelLE, ?_⟩
  intro g x
  simp only [LinearEquiv.trans_apply, Etingof.Definition5_8_1]
  rw [he1, stepB]

end Problem584

end Etingof

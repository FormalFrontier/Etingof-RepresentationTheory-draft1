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
  sorry

end Problem584

end Etingof

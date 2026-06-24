import Mathlib

/-!
# Remark 5.8.2: `Ind_H^G V ≅ Hom_H(k[G], V)`

Etingof's Remark 5.8.2 states that the induced representation `Ind_H^G V` is naturally
isomorphic to the coinduced representation `Hom_H(k[G], V)`.

## Mathlib correspondence

Mathlib realizes both sides directly:

* `Rep.ind H.subtype A` is the induced representation `Ind_H^G V` (the tensor model, the left
  adjoint of restriction), matching `Etingof.Definition5_8_1`.
* `Rep.coind' H.subtype A` is `Hom_H(k[G], V)`: its underlying module is the space of
  `H`-representation morphisms `res H.subtype (leftRegular k G) ⟶ A`, i.e. the `H`-equivariant
  `k`-linear maps `k[G] → V`. This is literally Etingof's `Hom_H(k[G], V)`.

For a finite index subgroup, induction and coinduction agree. Mathlib provides this as
`Rep.indCoindIso : Ind_H^G V ≅ Coind_H^G V`, where `Coind_H^G V = Rep.coind H.subtype A` is the
function-space model `{f : G → V | f(φg · h) = ρ(g) f(h)}`. Composing with
`Rep.coindIso`, the isomorphism `Coind_H^G V ≅ Hom_H(k[G], V)`, yields Etingof's stated
isomorphism `Ind_H^G V ≅ Hom_H(k[G], V)`.

(Etingof Remark 5.8.2)
-/

open CategoryTheory

namespace Etingof

/-- **Remark 5.8.2.** For a finite index subgroup `H ≤ G` and a representation `A` of `H`, the
induced representation `Ind_H^G V = Rep.ind H.subtype A` is naturally isomorphic to
`Hom_H(k[G], V) = Rep.coind' H.subtype A`, the `H`-equivariant maps `k[G] → V`.

The isomorphism is the composite of Mathlib's finite-index isomorphism `Ind ≅ Coind`
(`Rep.indCoindIso`) with the identification `Coind ≅ Hom_H(k[G], -)` (`Rep.coindIso`).
(Etingof Remark 5.8.2) -/
noncomputable def Remark5_8_2
    {k : Type*} [CommRing k]
    {G : Type*} [Group G] (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex]
    (A : Rep k H) :
    Rep.ind H.subtype A ≅ Rep.coind' H.subtype A :=
  Rep.indCoindIso A ≪≫ Rep.coindIso H.subtype A

end Etingof

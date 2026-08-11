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

The remark asserts this isomorphism is **natural**, i.e. it is the value at each `A` of a
natural isomorphism of functors `Rep k H ⥤ Rep k G`. We expose this as `Remark5_8_2NatIso`,
the composite of Mathlib's natural isomorphisms `Rep.indCoindNatIso` (`indFunctor ≅ coindFunctor`)
and `Rep.coindFunctorIso` (`coindFunctor ≅ coindFunctor'`). Its component at each `A` is
definitionally the objectwise `Remark5_8_2 H A`, recorded as `Remark5_8_2NatIso_app`.

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

/-- **Remark 5.8.2 (functorial form).** For a finite index subgroup `H ≤ G`, the induction
functor `Rep.indFunctor k H.subtype : Rep k H ⥤ Rep k G` is *naturally* isomorphic to the
coinduction functor `Rep.coindFunctor' k H.subtype`, whose value at `A` is
`Hom_H(k[G], V) = Rep.coind' H.subtype A`.

This is the natural-isomorphism upgrade of the objectwise `Remark5_8_2`: it is the composite of
Mathlib's finite-index natural isomorphism `Rep.indCoindNatIso` (`Ind ≅ Coind`) with the natural
identification `Rep.coindFunctorIso` (`Coind ≅ Hom_H(k[G], -)`). Naturality equations are exposed
to clients through the `@[simps]` lemmas `Remark5_8_2NatIso_hom_app` /
`Remark5_8_2NatIso_inv_app` together with `Iso.hom_inv_id_app` etc. from the category library.
(Etingof Remark 5.8.2) -/
@[simps!]
noncomputable def Remark5_8_2NatIso
    {k : Type*} [CommRing k]
    {G : Type*} [Group G] (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex] :
    Rep.indFunctor k H.subtype ≅ Rep.coindFunctor' k H.subtype :=
  Rep.indCoindNatIso k H ≪≫ Rep.coindFunctorIso H.subtype

/-- The component of the natural isomorphism `Remark5_8_2NatIso` at a representation `A` agrees
with the objectwise isomorphism `Remark5_8_2 H A`. An object-indexed isomorphism is thus recovered
from the functorial statement, confirming the two formalizations are the same map. -/
theorem Remark5_8_2NatIso_app
    {k : Type*} [CommRing k]
    {G : Type*} [Group G] (H : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel H)] [H.FiniteIndex]
    (A : Rep k H) :
    (Remark5_8_2NatIso H).app A = Remark5_8_2 H A :=
  rfl

end Etingof

import Mathlib

/-!
# Theorem 5.10.1: Frobenius Reciprocity

For a subgroup H ≤ G, a representation V of G, and a representation W of H,
there is a natural isomorphism:

  Hom_G(V, Ind_H^G W) ≅ Hom_H(Res_H^G V, W)

where `Ind_H^G W` is the book's function-space (coinduced) representation
`{f : G → W | f(hx) = h·f(x)}`, the right adjoint of restriction. This is
the fundamental adjunction between restriction and (co)induction functors, stated
in the book's direction `Res ⊣ Coind`.

## Book statement (Etingof, Theorem 5.10.1)

> The space `Hom_G(V, Ind_H^G W)` is naturally isomorphic to `Hom_H(Res_H^G V, W)`,

with `V : Rep G`, `W : Rep H`, and `Ind_H^G W` the function-space representation.
The book's proof constructs `F(α)v = (αv)(e)` for `α : V → Ind W`, i.e. the
right-adjoint form `Res ⊣ Coind`.

## What is formalized here

The word *naturally* in the book's statement is load-bearing, so a pointwise
`Hom`-space equivalence does not on its own express Theorem 5.10.1. This file
records the statement at three increasing strengths, all sorry-free:

* `Etingof.Theorem5_10_1` — the natural isomorphism of `k`-linear `Hom`
  bifunctors `Hom_G(-, Ind_H^G -) ≅ Hom_H(Res_H^G -, -)` on
  `(Rep k G)ᵒᵖ × Rep k H`, i.e. naturality in `V` *and* in `W`, with the
  isomorphism being one of `k`-modules (the book's "space ... isomorphic").
  This is the book's statement, and carries the item's name for that reason.
* `Etingof.Theorem5_10_1_adjunction` — the adjunction `Res_H^G ⊣ Ind_H^G`.
* `Etingof.Theorem5_10_1_homEquiv` / `Etingof.Theorem5_10_1_nonempty` — the
  underlying pointwise `k`-linear equivalence, recovered as the components of
  the natural isomorphism (`Theorem5_10_1_hom_app_app_apply`).

`Etingof.Theorem5_10_1_apply` pins the components down to the book's own formula
`F(α)v = (αv)(e)`, so the natural isomorphism above is the map the book's proof
constructs and not merely *some* isomorphism.

## Mathlib correspondence

- `Rep.resCoindHomEquiv`: the k-linear equivalence `(res φ B ⟶ A) ≃ₗ[k] (B ⟶ coind φ A)`
- `Rep.resCoindAdjunction`: the categorical adjunction `Res ⊣ Coind`
- `Rep.coind`: the coinduced (function-space) representation, right adjoint of `res`
- `Rep.resFunctor` / `Rep.res`: the restriction functor along `φ`
- `CategoryTheory.linearCoyoneda`: the `ModuleCat k`-valued `Hom` bifunctor of a
  `k`-linear category, used to state naturality on the nose

Instantiating `φ := H.subtype : ↥H →* G`, `B := V : Rep k G`, `A := W : Rep k ↥H`
gives `(Res_H^G V ⟶ W) ≃ₗ[k] (V ⟶ Ind_H^G W)`; taking `.symm` states it in the
book's orientation `Hom_G(V, Ind W) ≅ Hom_H(Res V, W)`.

## Relation to the book's proof

The book concludes Theorem 5.10.1 from the tensor-hom adjunction of Problem
2.11.6(b) applied to the `k[G]`-bimodule `k[G]` (see the Discussion in the proof
of Problem 5.10.2). This formalization instead obtains the same equivalence
directly from Mathlib's `Rep.resCoindHomEquiv`, so it does not depend on
Problem 2.11.6. See `Chapter2/Problem2_11_6.lean` for the conclusion that
Problem 2.11.6 is not load-bearing for any formalized content.
-/

open CategoryTheory Opposite

universe w

namespace Etingof

variable (k G : Type) [Field k] [Group G] (H : Subgroup G)

/-! ### The two functors of the adjunction -/

/-- `Res_H^G : Rep k G ⥤ Rep k H`, restriction along the inclusion `H ↪ G`. -/
abbrev resSubgroupFunctor : Rep.{w} k G ⥤ Rep.{w} k ↥H := Rep.resFunctor H.subtype

/-- `Ind_H^G : Rep k H ⥤ Rep k G`, the book's function-space induction
`Ind_H^G W = {f : G → W | f (h * x) = h · f x}`. This is Mathlib's coinduction
functor along `H.subtype`, the right adjoint of restriction. -/
noncomputable abbrev indSubgroupFunctor : Rep.{w} k ↥H ⥤ Rep.{w} k G :=
  Rep.coindFunctor k H.subtype

/-- Frobenius reciprocity as an adjunction: `Res_H^G ⊣ Ind_H^G`.
This is the categorical content of Etingof Theorem 5.10.1. -/
noncomputable def Theorem5_10_1_adjunction :
    resSubgroupFunctor.{w} k G H ⊣ indSubgroupFunctor.{w} k G H :=
  Rep.resCoindAdjunction.{w} k H.subtype

/-! ### The two `Hom` bifunctors, in the book's orientation -/

/-- The bifunctor `(V, W) ↦ Hom_G(V, Ind_H^G W)`, contravariant in `V : Rep k G`
and covariant in `W : Rep k H`, valued in `k`-modules. This is the left-hand side
of the book's statement of Theorem 5.10.1. -/
noncomputable def homIndBifunctor : (Rep.{w} k G)ᵒᵖ ⥤ Rep.{w} k ↥H ⥤ ModuleCat k :=
  linearCoyoneda k (Rep.{w} k G) ⋙
    (Functor.whiskeringLeft (Rep.{w} k ↥H) (Rep.{w} k G) (ModuleCat k)).obj
      (indSubgroupFunctor.{w} k G H)

/-- The bifunctor `(V, W) ↦ Hom_H(Res_H^G V, W)`, contravariant in `V : Rep k G`
and covariant in `W : Rep k H`, valued in `k`-modules. This is the right-hand side
of the book's statement of Theorem 5.10.1. -/
noncomputable def homResBifunctor : (Rep.{w} k G)ᵒᵖ ⥤ Rep.{w} k ↥H ⥤ ModuleCat k :=
  (resSubgroupFunctor.{w} k G H).op ⋙ linearCoyoneda k (Rep.{w} k ↥H)

@[simp]
lemma homIndBifunctor_obj_obj (V : Rep.{w} k G) (W : Rep.{w} k ↥H) :
    ((homIndBifunctor.{w} k G H).obj (op V)).obj W =
      ModuleCat.of k (V ⟶ (indSubgroupFunctor.{w} k G H).obj W) :=
  rfl

@[simp]
lemma homResBifunctor_obj_obj (V : Rep.{w} k G) (W : Rep.{w} k ↥H) :
    ((homResBifunctor.{w} k G H).obj (op V)).obj W =
      ModuleCat.of k ((resSubgroupFunctor.{w} k G H).obj V ⟶ W) :=
  rfl

/-! ### The natural isomorphism -/

variable {k G H}

/-- For a fixed `G`-representation `V`, the `k`-linear isomorphism
`Hom_G(V, Ind_H^G W) ≅ Hom_H(Res_H^G V, W)` is natural in `W`.

Kept as a separate named definition (rather than inlined into
`Theorem5_10_1_natIso`) so that the outer naturality proof never has to unfold the
baked-in proof term of this inner `NatIso`. -/
noncomputable def frobeniusNatIsoApp (V : Rep.{w} k G) :
    (homIndBifunctor.{w} k G H).obj (op V) ≅ (homResBifunctor.{w} k G H).obj (op V) :=
  NatIso.ofComponents
    (fun W => (Rep.resCoindHomEquiv.{w} H.subtype V W).symm.toModuleIso)
    (fun {_ _} g => by
      ext α
      exact (Rep.resCoindAdjunction.{w} k H.subtype).homEquiv_naturality_right_symm α g)

@[simp]
lemma frobeniusNatIsoApp_hom_app_apply (V : Rep.{w} k G) (W : Rep.{w} k ↥H)
    (α : V ⟶ (indSubgroupFunctor.{w} k G H).obj W) :
    ((frobeniusNatIsoApp V).hom.app W).hom α =
      (Rep.resCoindHomEquiv.{w} H.subtype V W).symm α :=
  rfl

variable (k G H)

/-- **Theorem 5.10.1 (Frobenius reciprocity).** The `k`-linear `Hom` bifunctors
`Hom_G(-, Ind_H^G -)` and `Hom_H(Res_H^G -, -)` on `(Rep k G)ᵒᵖ × Rep k H` are
naturally isomorphic — natural in the `G`-representation `V` *and* in the
`H`-representation `W`, and an isomorphism of `k`-modules pointwise.

This is the book's statement verbatim: "the space `Hom_G(V, Ind_H^G W)` is
naturally isomorphic to `Hom_H(Res_H^G V, W)`". The components are the book's own
map `F(α)v = (αv)(e)` — see `Theorem5_10_1_apply`. -/
noncomputable def Theorem5_10_1 :
    homIndBifunctor.{w} k G H ≅ homResBifunctor.{w} k G H :=
  NatIso.ofComponents (fun V => frobeniusNatIsoApp V.unop)
    (fun {_ _} f => by
      ext W α
      exact (Rep.resCoindAdjunction.{w} k H.subtype).homEquiv_naturality_left_symm f.unop α)

@[simp]
lemma Theorem5_10_1_hom_app (V : Rep.{w} k G) :
    (Theorem5_10_1.{w} k G H).hom.app (op V) = (frobeniusNatIsoApp V).hom :=
  rfl

/-- The components of the natural isomorphism are exactly Mathlib's Frobenius
reciprocity equivalence `Rep.resCoindHomEquiv`, read in the book's orientation.
This is what ties the naturality statement above to the pointwise equivalence. -/
@[simp]
lemma Theorem5_10_1_hom_app_app_apply (V : Rep.{w} k G) (W : Rep.{w} k ↥H)
    (α : V ⟶ (indSubgroupFunctor.{w} k G H).obj W) :
    (((Theorem5_10_1.{w} k G H).hom.app (op V)).app W).hom α =
      (Rep.resCoindHomEquiv.{w} H.subtype V W).symm α :=
  rfl

/-! ### The pointwise equivalence, and the book's formula for it -/

variable {k G H}

/-- Frobenius reciprocity as a `k`-linear equivalence of `Hom` spaces,
`Hom_G(V, Ind_H^G W) ≃ₗ[k] Hom_H(Res_H^G V, W)`, in the book's orientation.
It is the component at `(V, W)` of `Theorem5_10_1`. -/
noncomputable def Theorem5_10_1_homEquiv (V : Rep.{w} k G) (W : Rep.{w} k ↥H) :
    (V ⟶ (indSubgroupFunctor.{w} k G H).obj W) ≃ₗ[k]
      ((resSubgroupFunctor.{w} k G H).obj V ⟶ W) :=
  (Rep.resCoindHomEquiv.{w} H.subtype V W).symm

/-- The equivalence of Theorem 5.10.1 is the book's map `F(α)v = (αv)(e)`:
it sends `α : V ⟶ Ind_H^G W` to the `H`-map evaluating `α v : G → W` at the
identity of `G`. -/
@[simp]
lemma Theorem5_10_1_apply (V : Rep.{w} k G) (W : Rep.{w} k ↥H)
    (α : V ⟶ (indSubgroupFunctor.{w} k G H).obj W) (v : V.V) :
    (Theorem5_10_1_homEquiv V W α).hom v = (α.hom v).1 (1 : G) :=
  rfl

/-- Frobenius reciprocity: there is a k-linear equivalence
  Hom_G(V, Ind_H^G W) ≃ₗ[k] Hom_H(Res_H^G V, W),
where `Ind_H^G W = Rep.coind H.subtype W` is the book's function-space (coinduced)
representation, the right adjoint of restriction. The arrows match the book:
maps `V ⟶ Ind W` of `G`-representations correspond to maps `Res V ⟶ W` of
`H`-representations. (Etingof Theorem 5.10.1)

This is only the pointwise shadow of the book's statement; `Theorem5_10_1` itself
is the natural isomorphism, which additionally records the naturality the book
asserts. Retained under this name because it is the form cited from
`Chapter2/Problem2_11_6.lean` and `Chapter5/Discussion5_11_examples.lean`. -/
theorem Theorem5_10_1_nonempty
    (k G : Type) [Field k] [Group G]
    (H : Subgroup G)
    (V : Rep k G) (W : Rep k ↥H) :
    Nonempty ((V ⟶ Rep.coind H.subtype W) ≃ₗ[k]
      ((Rep.resFunctor H.subtype).obj V ⟶ W)) :=
  ⟨Theorem5_10_1_homEquiv V W⟩

end Etingof

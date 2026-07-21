import Mathlib

/-!
# Theorem 5.10.1: Frobenius Reciprocity

For a subgroup H ≤ G, a representation V of G, and a representation W of H,
there is a natural isomorphism:

  Hom_G(V, Ind_H^G W) ≅ Hom_H(Res_H^G V, W)

where `Ind_H^G W` is the book's **function-space (coinduced)** representation
`{f : G → W | f(hx) = h·f(x)}` — the **right** adjoint of restriction. This is
the fundamental adjunction between restriction and (co)induction functors, stated
in the book's direction `Res ⊣ Coind`.

## Book statement (Etingof, Theorem 5.10.1)

> The space `Hom_G(V, Ind_H^G W)` is naturally isomorphic to `Hom_H(Res_H^G V, W)`,

with `V : Rep G`, `W : Rep H`, and `Ind_H^G W` the function-space representation.
The book's proof constructs `F(α)v = (αv)(e)` for `α : V → Ind W`, i.e. the
right-adjoint form `Res ⊣ Coind`. Mathlib's `Rep.coind` is precisely this
function-space (coinduced) representation, and `Rep.resCoindHomEquiv` provides the
`k`-linear equivalence realising the adjunction.

## Mathlib correspondence

- `Rep.resCoindHomEquiv` — the k-linear equivalence `(res φ B ⟶ A) ≃ₗ[k] (B ⟶ coind φ A)`
- `Rep.resCoindAdjunction` — the categorical adjunction `Res ⊣ Coind`
- `Rep.coind` — the coinduced (function-space) representation, right adjoint of `res`
- `Rep.resFunctor` / `Rep.res` — the restriction functor along `φ`

Instantiating `φ := H.subtype : ↥H →* G`, `B := V : Rep k G`, `A := W : Rep k ↥H`
gives `(Res_H^G V ⟶ W) ≃ₗ[k] (V ⟶ Ind_H^G W)`; taking `.symm` states it in the
book's orientation `Hom_G(V, Ind W) ≅ Hom_H(Res V, W)`.

## Book route vs. this formalization (completeness audit, epic #5338)

The book concludes Theorem 5.10.1 from the tensor-hom adjunction of Problem
2.11.6(b) applied to the `k[G]`-bimodule `k[G]` (see the Discussion in the proof
of Problem 5.10.2). This formalization instead obtains the same equivalence
directly from Mathlib's `Rep.resCoindHomEquiv`, so it does **not** depend on
Problem 2.11.6. See `Chapter2/Problem2_11_6.lean` for the audit conclusion that
Problem 2.11.6 is not load-bearing for any formalized content.
-/

open CategoryTheory

/-- Frobenius reciprocity: there is a k-linear equivalence
  Hom_G(V, Ind_H^G W) ≃ₗ[k] Hom_H(Res_H^G V, W),
where `Ind_H^G W = Rep.coind H.subtype W` is the book's function-space (coinduced)
representation — the **right** adjoint of restriction. The arrows match the book:
maps `V ⟶ Ind W` of `G`-representations correspond to maps `Res V ⟶ W` of
`H`-representations. (Etingof Theorem 5.10.1) -/
theorem Etingof.Theorem5_10_1
    (k G : Type) [Field k] [Group G]
    (H : Subgroup G)
    (V : Rep k G) (W : Rep k ↥H) :
    Nonempty ((V ⟶ Rep.coind H.subtype W) ≃ₗ[k]
      ((Rep.resFunctor H.subtype).obj V ⟶ W)) :=
  ⟨(Rep.resCoindHomEquiv H.subtype V W).symm⟩

/-!
# Problem 2.11.6: Bimodules, associativity, and the tensor-hom adjunction

> Throughout, `k` is an arbitrary field and `A, B, C, D` are `k`-algebras. An
> `(A, B)`-**bimodule** is a `k`-vector space `V` with a left `A`-module and a
> right `B`-module structure satisfying `(a v) b = a (v b)`. For a right
> `B`-module `V` and a left `B`-module `W`, `V ⊗_B W` is the tensor product over
> `B` of Remark 2.11.4; bimodule structures on the factors induce module
> structures on `V ⊗_B W`.
> (a) For `V` an `(A, B)`-bimodule, `W` a `(B, C)`-bimodule, `X` a
> `(C, D)`-bimodule, there is an `(A, D)`-bimodule isomorphism
> `(V ⊗_B W) ⊗_C X ≅ V ⊗_B (W ⊗_C X)`, `(v ⊗ w) ⊗ x ↦ v ⊗ (w ⊗ x)`
> (**associativity**).
> (b) `Hom_A(V, W)` is a `(B, C)`-bimodule via `(b f)(v) = f(v b)` and
> `(f c)(v) = f(v) c`; and for `V` a `(B, A)`-bimodule, `W` a `(C, B)`-bimodule,
> `X` a `(C, D)`-bimodule there is an `(A, D)`-bimodule isomorphism
> `Hom_B(V, Hom_C(W, X)) ≅ Hom_C(W ⊗_B V, X)`, `f ↦ (w ⊗ v ↦ f(v) w)`
> (the **tensor-hom adjunction**).

## Role in the development

The only place the book cites Problem 2.11.6 is the Discussion in the proof of
Problem 5.10.2 (`blobs/Chapter5/Discussion_Problem5.10.2_parts.md`), which opens
"Throughout this exercise, we will use the notation and results of Problem 2.11.6"
and, in part (b), reads:

> "According to Remark 5.8.2, `Ind_H^G W ≅ Hom_H(k[G], W)`. In other words, we
> have `Ind_H^G W ≅ Hom_{k[H]}(k[G]₁, W)`. Now use part (b) of Problem 2.11.6 to
> conclude Theorem 5.10.1."

So the role of Problem 2.11.6 in the book is to supply the tensor-hom adjunction
(part (b)), from which Frobenius reciprocity (Theorem 5.10.1) is deduced via the
`k[G]`-bimodule form of the adjunction.

Theorem 5.10.1 itself is formalized directly in `Chapter5/Theorem5_10_1.lean` as

  `Etingof.Theorem5_10_1 (k G : Type) [Field k] [Group G] (H : Subgroup G) :`
  `    Etingof.homIndBifunctor k G H ≅ Etingof.homResBifunctor k G H`

a natural isomorphism of the `ModuleCat k`-valued `Hom` bifunctors
`Hom_G(-, Ind_H^G -)` and `Hom_H(Res_H^G -, -)` on `(Rep k G)ᵒᵖ × Rep k H`
(`Etingof.Theorem5_10_1_nonempty` is the pointwise shadow of it). That proof
obtains Frobenius reciprocity from Mathlib's `Rep.resCoindHomEquiv` and
`Rep.resCoindAdjunction`, packaging the `Res ⊣ Coind` adjunction, rather than from
the `k[G]`-bimodule tensor-hom adjunction of Problem 2.11.6(b). So Theorem 5.10.1
does not depend on Problem 2.11.6.

The Discussion of Problem 5.10.2 that carries the citation is an alternative,
module-theoretic re-derivation of the induction/restriction adjunctions. The
bimodule associativity (a) and tensor-hom adjunction (b) are self-contained
statements that the formalized development does not use, so Problem 2.11.6 is not
separately formalized here; the machine-checked citation target is
`Etingof.Theorem5_10_1`. A faithful formalization would first require a full
bimodule and universal-property API on top of the tensor product
`Etingof.TensorProductOverRing` of Remark 2.11.4 (the `V ⊗_B W` used throughout
Problem 2.11.6), which currently exposes only `tmul`, `add_tmul`, `tmul_add`,
`smul_tmul`. This is an intentional project-scope decision recorded publicly in
`skipped-exercises.md`, not an unfinished proof; accordingly this file introduces
no placeholder declaration for either part.
-/

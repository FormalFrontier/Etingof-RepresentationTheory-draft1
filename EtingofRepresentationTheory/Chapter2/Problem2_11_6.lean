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

## Coverage status (completeness audit, epic #5338)

The only place the main narrative cites Problem 2.11.6 is the **Discussion in the
proof of Problem 5.10.2** (`blobs/Chapter5/Discussion_Problem5.10.2_parts.md`),
which opens "Throughout this exercise, we will use the notation and results of
Problem 2.11.6" and, in part (b), reads:

> "According to Remark 5.8.2, `Ind_H^G W ≅ Hom_H(k[G], W)`. In other words, we
> have `Ind_H^G W ≅ Hom_{k[H]}(k[G]₁, W)`. Now use part (b) of Problem 2.11.6 to
> conclude Theorem 5.10.1."

So the book's role for Problem 2.11.6 is to supply the tensor-hom adjunction
(part (b)) from which Frobenius reciprocity (Theorem 5.10.1) is deduced along
this particular `k[G]`-bimodule route.

The load-bearing conclusion — Theorem 5.10.1 itself — is formalized directly and
completely in `Chapter5/Theorem5_10_1.lean` as

  `Etingof.Theorem5_10_1 (k G : Type) [Field k] [Group G] (H : Subgroup G)`
  `    (V : Rep k G) (W : Rep k ↥H) :`
  `    Nonempty ((Rep.ind H.subtype W ⟶ V) ≃ₗ[k]`
  `      (W ⟶ (Rep.resFunctor H.subtype).obj V))`

That proof obtains Frobenius reciprocity from Mathlib's `Rep.indResHomEquiv`, the
native `k`-linear equivalence packaging the `Ind ⊣ Res` adjunction. It does
**not** route through the `k[G]`-bimodule tensor-hom adjunction of Problem
2.11.6(b); it proves the required equivalence by an independent, self-contained
Mathlib construction. Consequently Theorem 5.10.1 does not silently assume
Problem 2.11.6.

The Discussion of Problem 5.10.2 that carries the citation is an alternative,
module-theoretic re-derivation of the induction/restriction adjunctions; it has
no separate Lean formalization, and nothing that *is* formalized depends on it.
The `TensorProductOverRing` construction of Remark 2.11.4 (the `V ⊗_B W` used
throughout Problem 2.11.6) is imported by no downstream Lean file.

Therefore Problem 2.11.6 is **not load-bearing** for any formalized content:
- its sole narrative use (deriving Theorem 5.10.1 via the tensor-hom adjunction)
  is superseded by the direct Mathlib proof of `Etingof.Theorem5_10_1`;
- the bimodule associativity (a) and tensor-hom adjunction (b) are self-contained
  exercises that no formalized item consumes.

Accordingly, per the audit task, Problem 2.11.6 is not separately formalized. A
faithful formalization would require first building a full bimodule/universal-
property API on top of the bare-quotient `Etingof.TensorProductOverRing` (which
currently exposes only `tmul`, `add_tmul`, `tmul_add`, `smul_tmul`); that is a
large standalone effort with no downstream consumer, tracked here only as an
audit conclusion.

This file records the audit conclusion and carries no proof; the machine-checked
citation target is `Etingof.Theorem5_10_1`.
-/

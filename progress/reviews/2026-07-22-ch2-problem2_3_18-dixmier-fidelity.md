# Fidelity audit — Problem 2.3.18 (Dixmier's infinite-dimensional Schur lemma)

**Issue:** #7243
**Date:** 2026-07-22
**Item:** `Chapter2/Problem2.3.18`
**Lean:** `EtingofRepresentationTheory/Chapter2/Problem2_3_18.lean`, headline `Etingof.Problem_2_3_18`
**Verdict:** ✅ **VERIFIED (faithful)** — `fidelity: verified`, `coverage: covered_full`

## Book statement (blob)

> Let $A$ be an algebra over $\mathbb{C}$ and let $V$ be an irreducible representation of $A$
> with at most countable basis. Then any homomorphism of representations $\phi : V \to V$ is a
> scalar operator.

## Lean statement

```lean
theorem Problem_2_3_18
    {A : Type*} [Ring A] [Algebra ℂ A]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    [IsSimpleModule A V]
    (hcard : Module.rank ℂ V ≤ Cardinal.aleph0)
    (φ : V →ₗ[A] V) :
    ∃ c : ℂ, ∀ v : V, φ v = c • v
```

## Non-vacuity checks (Stage 3.2 steps 6–7)

This item is a classic vacuity trap: an "infinite-dimensional" lemma is easy to collapse to
ordinary finite-dimensional Schur by accidentally having a `FiniteDimensional` instance in scope.
Each load-bearing hypothesis was checked explicitly.

1. **Countability hypothesis is genuine, not over-strong.** The hypothesis is
   `hcard : Module.rank ℂ V ≤ Cardinal.aleph0` — a genuine cardinal bound stating the ℂ-dimension
   is *at most countable*. This is **not** `FiniteDimensional`. The statement therefore covers
   genuinely countably-infinite-dimensional `V` (e.g. `A = V = ℂ(x)`-style examples) and is strictly
   more general than finite-dimensional Schur — the whole point of Dixmier's lemma. No hidden
   `FiniteDimensional` or `Finite`/`Fintype` instance is present in the binder list or the local
   context of the statement. Non-vacuous witness: `A = ℂ`, `V = ℂ` satisfies all hypotheses.

2. **Irreducibility is genuine.** `[IsSimpleModule A V]` is the real simple-module hypothesis (the
   proof pulls `Nontrivial V` *out* of it via `IsSimpleModule.nontrivial`), not a weaker
   `[Nontrivial V]` standing in for irreducibility.

3. **Conclusion asserts a genuine scalar operator.** The conclusion `∃ c : ℂ, ∀ v, φ v = c • v` is
   exactly "$\phi = c\cdot\mathrm{id}$". It is not the far weaker "`φ` commutes with the action"
   (that is *encoded in the type* `φ : V →ₗ[A] V`, i.e. the hypothesis) and not an existential so
   weak it would hold for any endomorphism. Note `φ : V →ₗ[A] V` is `A`-linear, i.e. a genuine
   homomorphism of representations, matching the book's "homomorphism of representations".

4. **Ground field is ℂ literally.** `ℂ` appears literally, not an over-general `[IsAlgClosed k]`.
   This is load-bearing: the proof genuinely uses both algebraic closure of ℂ (degree-one minimal
   polynomial ⟹ scalar) **and** the uncountability of ℂ (`Cardinal.mk_complex`,
   `Cardinal.aleph0_lt_continuum`) to derive the contradiction from an uncountable
   `ℂ`-linearly-independent family `{(φ - a)⁻¹ : a ∈ ℂ}`. A generic algebraically-closed field of
   countable cardinality (e.g. `algebraic closure of ℚ`) would break the argument, and correctly so:
   the statement is specialized to ℂ, matching the book.

## Proof-route fidelity

The proof follows Etingof's hint faithfully:
- `D := Module.End A V` is a division ring by Schur (`Module.End.instDivisionRing`).
- `D` is at most countably dimensional over ℂ via the injective ℂ-linear evaluation
  `ev : D → V`, `ψ ↦ ψ v₀` at a fixed nonzero `v₀` (`rank ℂ D ≤ rank ℂ V ≤ ℵ₀`).
- A non-scalar `φ` is transcendental over ℂ (else `minpoly` has degree 1 since ℂ is algebraically
  closed and `D` is a domain, forcing `φ ∈ ℂ`).
- `ℂ(φ)` is realized as the double centralizer `Subalgebra.centralizer ℂ (Set.centralizer {φ})`,
  a commutative division subring, hence a field (`IsField.toField`); inside it
  `Transcendental.linearIndependent_sub_inv` yields the uncountable independent family, transported
  to `D` along the injective inclusion.
- `𝔠 = #ℂ ≤ rank ℂ D ≤ ℵ₀` contradicts `ℵ₀ < 𝔠`.

## Build / axioms

- `lake build EtingofRepresentationTheory.Chapter2.Problem2_3_18` exits 0.
- `#print axioms Etingof.Problem_2_3_18` → `[propext, Classical.choice, Quot.sound]`; **no `sorryAx`**.

## Recorded state

`progress/items.json` `Chapter2/Problem2.3.18`: `fidelity: verified`, `coverage: covered_full`,
`lean_decl: Etingof.Problem_2_3_18`, plus a `fidelity_note` summarizing the checks. `status` stays
`sorry_free`.

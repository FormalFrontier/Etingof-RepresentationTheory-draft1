# Stage 3.7 fidelity & non-vacuity audit — Problem 4.12.3 (SⁿV and ∧ᵐV irreducible as GL(V)-reps)

- **Issue:** #7278
- **Verdict:** `verified` — `covered_full`
- **Audited against:** `origin/main` HEAD `77de7a8e`
- **Mathlib:** v4.32.0-rc1
- **Reviewer path:** independent re-derivation from the book statement + criterion
  soundness read, distinct from the original formalizer's construction path.

## Book statement (`blobs/Chapter4/Problem4.12.3.md`)

> Let `V` be a finite dimensional complex vector space, and let `GL(V)` be the group of
> invertible linear transformations of `V`. Then `SⁿV` and `∧ᵐV` (`m ≤ dim V`) are
> representations of `GL(V)` in a natural way. Show that they are irreducible
> representations.

Hint: a diagonal `H ∈ GL(V)` with distinct eigenvalues shows any subrep `W` is spanned by
a subset `S` of an eigenbasis; the transvections `ρ(1 + E_{ij})` then force nonempty `S` to
be the whole basis.

## Declarations audited

| # | Declaration | File:line |
|---|-------------|-----------|
| 1 | `Etingof.symmetricPower_eq_bot_or_top` | `Chapter5/SymmetricIrreducible.lean:137` |
| 2 | `Etingof.Example5_19_3_symmetric_irreducible` | `Chapter5/SymmetricIrreducible.lean:193` |
| 3 | `Etingof.exteriorPower_eq_bot_or_top` | `Chapter5/ExteriorIrreducible.lean:139` |
| 4 | `Etingof.Example5_19_3_exterior_irreducible` | `Chapter5/Example5_19_3.lean:593` |

Common shape (over `[Field k] [CharZero k] [Module.Finite k V]`):

```lean
(W : Submodule k <space>)
(hW : ∀ g : V ≃ₗ[k] V, ∀ w ∈ W, <map> (g : V →ₗ[k] V) w ∈ W) :
  W = ⊥ ∨ W = ⊤
```

with `<map> = symmetricPowerMap` (SⁿV) / `exteriorPower.map n` (∧ⁿV).

## 1. Statement fidelity

**Irreducibility encoding.** Each headline asserts "every `GL(V)`-stable submodule `W` is
`⊥` or `⊤`" — the simple-module condition. This is the project's established rendering of
"irreducible representation" (matching the sibling audits #7250/#7269/#7273). Faithful.

**Natural GL(V)-action.** The stability hypothesis quantifies over **all** `g : V ≃ₗ[k] V`
(the whole general linear group), via the induced functorial maps `symmetricPowerMap g`
and `exteriorPower.map n g`. Quantifying over each `g` independently is exactly the
subrepresentation condition and is the correct encoding of "GL(V)-subrepresentation";
irreducibility does not even require the map `g ↦ …` to be recorded as a homomorphism here,
only invariance under each group element, which is present. Faithful.

**Both halves covered.** The book claims irreducibility of *both* `SⁿV` (decl 1/2) and
`∧ᵐV` (decl 3/4). Both are formalized and proved. `covered_full`.

**Criterion soundness (spot-checked, not black-boxed).** Both proofs route through
`Etingof.DiagonalCoordinate.eq_bot_or_eq_top_of_connected`
(`Chapter5/DiagonalCoordinate.lean:121`), which is a genuine proof: `mem_of_repr_ne_zero`
(line 65) is the real Lagrange-interpolation argument (`p = ∏_{s≠t}(X - w s)` annihilates all
eigencomponents but `t`, whose surviving scale `∏_{s≠t}(w t - w s) ≠ 0` uses injectivity of
`w`), and the connectivity half propagates membership along a `ReflTransGen Adj` chain, then
`b.span_eq` closes to `⊤`. No shortcut, no `True`-typed hypothesis. The eigenvalue-injectivity
inputs are honest: symmetric uses `t_i = pᵢ` (i-th prime) with unique factorisation
(`factorization_prod_prime_eq_card_filter`); exterior uses `t_i = 2^(2^i)` with distinct
subset-sums of powers of two (`diagEig_injective`, via `Nat.pow_right_injective` +
`Finset.equivBitIndices`). Both genuinely deliver pairwise-distinct eigenvalues.

## 2. Non-vacuity — the `m ≤ dim V` / degenerate-range analysis (the key check)

**Hypotheses are simultaneously satisfiable.** Take `k = ℂ`, `V = k^d` with `d ≥ 1`. Then
`[CharZero k]`, `[Module.Finite k V]` hold and `V` is a genuine nonzero finite-dimensional
space, so none of the four theorems is vacuous by unsatisfiable typeclass hypotheses.

**`m ≤ dim V` bound: needed? present? correctly handled?**

- **Present?** No — the exterior theorems (decl 3/4) carry **no** `n ≤ dim V` hypothesis;
  they are stated for all `n : ℕ`.
- **Needed for truth?** No, and this is the crux. The conclusion is the bare
  `W = ⊥ ∨ W = ⊤`, which does **not** carry a nontriviality clause (`⊥ ≠ ⊤`). For
  `n ≤ dim V` the space `∧ⁿV` is nonzero (`finrank = C(dim V, n) ≥ 1`), so the statement is
  genuine, non-vacuous irreducibility and the proof does real work (distinct eigenvalues +
  transitive permutation action). For `n > dim V`, `Set.powersetCard (Fin d) n` is empty,
  `∧ⁿV = 0`, and `W = ⊥ = ⊤` is *trivially* true — the proof simply takes the `W = ⊥`
  branch. So the theorem is **true for all `n`**, never falsely asserting irreducibility of
  a zero space; the book's `m ≤ dim V` restriction is exactly the range where the true
  statement is *non-degenerate*.
- **Correctly handled?** Yes, and unusually carefully. The project provides a dedicated
  companion lemma `Etingof.Example5_19_3_exterior_subsingleton_of_dim_lt`
  (`Example5_19_3.lean:570`) proving `Subsingleton (⋀[k]^n V)` for `dim V < n`, and the
  exterior wrapper's docstring (`Example5_19_3.lean:579-592`) explicitly points the reader
  to it. The degenerate range the issue flagged as a vacuity risk is thus not silently
  swept under the rug — it is proved out and cross-referenced. The `⊥ ∨ ⊤` conclusion is
  the honest simple-*or-zero* property; combined with the separately-visible nonzero-ness
  for `n ≤ dim V`, it yields genuine irreducibility in exactly the book's range.

**Symmetric side.** `SⁿV` is nonzero for every `n` when `V ≠ 0` (`finrank = C(d+n-1, n) ≥ 1`
for `d ≥ 1`), so decl 1/2 are non-vacuous for all `n` — consistent with the book placing no
range restriction on `SⁿV`. (Only the edge case `V = 0` makes `SⁿV = 0` for `n ≥ 1`, the
same harmless trivially-true degeneracy.)

**Constructions are real, not `True`-typed.** `symmetricPowerMap`, `exteriorPower.map`,
`symmetricPowerMonomialBasis`, `bV.exteriorPower n`, and the diagonal `H = bV.equiv (bV.unitsSMul u)`
are genuine data (bases, honest `V ≃ₗ[k] V`), not placeholders. No hypothesis is
trivially dischargeable.

## 3. `[CharZero k]` generalization of ℂ

**Sound.** The book works over ℂ; the formalization generalizes to any `[CharZero k]`. This
is genuinely where the argument lives, not a spurious weakening: the distinct-eigenvalue
diagonal element requires char 0 (primes `pᵢ ≠ 0` and injective for the symmetric weights;
`(2:k)^a = (2:k)^b ⟹ a = b` for the exterior weights). Over a small finite field the
diagonal element with distinct eigenvalues need not exist, so `[CharZero k]` is not
gratuitous.

**Documentation.** The symmetric low-level theorem and its wrapper both loudly flag
`[CharZero k]` as essential (`SymmetricIrreducible.lean:32-33, 190-192`). The exterior
wrapper `Example5_19_3_exterior_irreducible` also documents it
(`Example5_19_3.lean:590-592`). The only omission is the low-level
`exteriorPower_eq_bot_or_top` docstring (`ExteriorIrreducible.lean:136-138`), which states
the result but not the char-0 essentiality note. This is a minor documentation nit at the
lemma level, **not** a statement-fidelity gap (the hypothesis is present in the signature and
documented at the wrapper the book maps to). Report-only: no Lean edit made. Optional
follow-up for a future doc pass, not worth a repair issue.

## 4. Axiom cleanliness

`lake build` of both files exits 0. `#print axioms` on all four declarations:

```
'Etingof.symmetricPower_eq_bot_or_top'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.Example5_19_3_symmetric_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.exteriorPower_eq_bot_or_top'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.Example5_19_3_exterior_irreducible'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

All subsets of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no custom axioms.
Word-boundary `grep -w sorry` over both files returns nothing (the docstring `sorry` token
cited in the issue text belongs to Problem 4.12.5, not these files).

## Verdict

**`verified` / `covered_full`.** All four declarations faithfully assert the irreducibility
of `SⁿV` and `∧ᵐV` as `GL(V)`-representations, with the natural functorial action quantified
over the full `GL(V)`. The `m ≤ dim V` vacuity risk is genuine in principle but is correctly
handled: the `⊥ ∨ ⊤` conclusion is true for all `n`, non-degenerate exactly on the book's
range where the space is nonzero, and the degenerate `n > dim V` case is separately proved
zero (`Example5_19_3_exterior_subsingleton_of_dim_lt`) and cross-referenced. `[CharZero k]`
is a sound, essential generalization of ℂ and is documented on the wrappers. No fidelity gap;
no repair issue filed; no Lean proof modified.

Minor, non-blocking observation (recorded, not escalated): the low-level
`exteriorPower_eq_bot_or_top` docstring could repeat the "char 0 essential" note that its
symmetric counterpart and its own wrapper already carry.

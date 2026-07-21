# Review: Ch2 Problem 2.16.2 — irreps of the 2d Lie algebra `[X,Y]=Y` (char 0 & p): statement-fidelity + non-vacuity audit

**Issue:** #7200 (review, report-only)
**File:** `EtingofRepresentationTheory/Chapter2/Problem2_16_2.lean` (509 lines)
**Book reference:** `blobs/Chapter2/Problem2.16.2.md`
**Date:** 2026-07-21 (UTC)

## Verdict

**GAP — partial rendering of "classify" (char-0 existence half absent).** Everything that
*is* proved is faithful, non-vacuous, and axiom-clean; there are **no defects** in the
existing statements or proofs. The gap is a *completeness* gap, not an error:

- **Lie algebra correctness — FAITHFUL.** `g k` is genuinely the 2-dimensional Lie algebra
  `⟨X, Y | [X,Y]=Y⟩`, `bracket_X_Y` proves the defining relation, and `instIsSolvable` is the
  real `LieAlgebra.IsSolvable`.
- **Char `p` counterexample — FAITHFUL and non-vacuous.** `repModule_irreducible` genuinely
  proves the explicit `k^{ℤ/p}` (`X` = `diagOp`, `Y` = `shiftOp`) is `LieModule.IsIrreducible`,
  and `lie_theorem_fails_charP` is a real, witnessed negation of "every irreducible is
  1-dimensional" (the module has dimension `p > 1`). This faithfully answers the book's "is
  Lie's theorem true in positive characteristic?" with **no**.
- **Char `0` classification — PARTIAL.** `charZero_irreducible_finrank_one` +
  `charZero_Y_acts_zero` prove only the **necessary-condition direction**: every f.d.
  irreducible is 1-dimensional and has `Y` acting by `0`. The **existence / realization half**
  of "classify" — that every scalar `λ ∈ k` is realized by a genuine irreducible rep
  (`X ↦ λ, Y ↦ 0`), and hence that the char-0 irreducibles are *exactly* `{(λ) : λ ∈ k}` — is
  **not present** in the file (nor anywhere else in the project). No char-0 `g k`-module is
  constructed at all.

Because the book's instruction is "**Classify** irreducible finite dimensional representations"
and the file renders only the "⇒" half of the char-0 classification, per the issue's explicit
criterion this item is scored **`gap`**, with a `feature` follow-up filed for the missing
char-0 `λ`-realization existence half. Report-only: no Lean changes made in this review.

- `lake build EtingofRepresentationTheory.Chapter2.Problem2_16_2` exits 0 (8580 jobs); only
  style/lint warnings (unused simp arg at :351, `show`-vs-`change` at :352, unused section var
  at :389, deprecated `push_neg` at :432 — none affect correctness).
- The file is `sorry`-free; every `def`/`instance` (`g`, `X`, `Y`, `spanB`, `lam`, `diagOp`,
  `shiftOp`, `rowZero`, `ρ`, `repModule`, `repLieModule`, `vsupp`) is genuinely constructed —
  in particular `ρ.map_lie'` is fully proved (lines 296–328), so the char-`p` representation is
  real, not a stub.

## 1. Axiom-cleanliness audit

`#print axioms` was run on all headline declarations plus the representation `ρ` via a scratch
importer. Every one reports exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
no custom axiom:

| Declaration | Location | Axioms |
|---|---|---|
| `bracket_X_Y` | `Problem2_16_2.lean:86` | clean |
| `instIsSolvable` | `Problem2_16_2.lean:141` | clean |
| `charZero_irreducible_finrank_one` | `Problem2_16_2.lean:162` | clean |
| `charZero_Y_acts_zero` | `Problem2_16_2.lean:191` | clean |
| `ρ` (the char-`p` representation) | `Problem2_16_2.lean:288` | clean |
| `repModule_irreducible` | `Problem2_16_2.lean:398` | clean |
| `lie_theorem_fails_charP` | `Problem2_16_2.lean:495` | clean |

("clean" = `depends on axioms: [propext, Classical.choice, Quot.sound]`.)

## 2. What the book claims

> **Problem 2.16.2.** Classify irreducible finite dimensional representations of the
> two-dimensional Lie algebra with basis `X, Y` and commutation relation `[X, Y] = Y`. Consider
> the cases of zero and positive characteristic. Is the Lie theorem true in positive
> characteristic?

The standard answers (Etingof et al.): in char 0 with `k` algebraically closed, `𝔤` is
solvable, so by Lie's theorem every f.d. irreducible is 1-dimensional; then `Y = [X,Y]` acts by
a commutator of scalars `= 0`, and the irreducibles are exactly the 1-dim reps `X ↦ λ, Y ↦ 0`
(`λ ∈ k`, pairwise non-isomorphic). In char `p`, Lie's theorem **fails**: `k^{ℤ/p}` with `X`
diagonal (eigenvalues `0,…,p-1`) and `Y` the cyclic shift is an irreducible of dimension `p`.

## 3. Statement-fidelity audit

### 3.1 The Lie algebra — FAITHFUL

`g k := LieSubalgebra.lieSpan k _ {single 0 0 1, single 0 1 1}` (line 42), i.e. the subalgebra
of `𝔤𝔩(2,k)` spanned by the matrix units `e₁₁, e₁₂`. `X k`, `Y k` are these two generators
(lines 46–51). The defining relation is genuinely proved: `bracket_X_Y : ⁅X k, Y k⁆ = Y k`
(line 86), reducing to `⁅e₁₁, e₁₂⁆ = e₁₂` (`bracket_e11_e12`). Solvability is the genuine
Mathlib notion: `instIsSolvable : LieAlgebra.IsSolvable (g k)` (line 141), proved by showing the
derived series reaches `⊥` after two steps (`derivedSeries … 2 = ⊥`).

*Minor completeness note (not scored as a defect):* the book phrases `𝔤` as "the 2-dimensional
Lie algebra with **basis** `X, Y`". The formalization realizes `g k` correctly and `e₁₁, e₁₂`
are genuinely linearly independent (distinct matrix units), so `g k` **is** 2-dimensional; but
`finrank (g k) = 2` / linear-independence of `X, Y` is not separately asserted. No downstream
claim depends on it, and the realized object is the correct one, so this is an observation, not
a gap.

### 3.2 Char 0 — necessary-condition direction FAITHFUL; existence half ABSENT (the gap)

- `charZero_irreducible_finrank_one` (line 162): over `[IsAlgClosed k] [CharZero k]`, any
  `M` with `[FiniteDimensional k M]` and `[LieModule.IsIrreducible k (g k) M]` has
  `finrank k M = 1`. The hypothesis is the genuine `LieModule.IsIrreducible` (§4). Faithful
  rendering of "every f.d. irreducible is 1-dimensional". Proof reuses the general solvable-Lie
  argument (`Problem2_16_1.finrank_eq_one_of_isSolvable` pattern via
  `exists_nontrivial_weightSpace_of_isSolvable`).
- `charZero_Y_acts_zero` (line 191): under the same hypotheses, `⁅Y k, m⁆ = 0` for all `m`.
  Faithful rendering of "`Y` acts by `0`", via `X, Y` acting as commuting scalars on the
  1-dim space and `Y = ⁅X,Y⁆`.

Together these give the **shape** of char-0 irreducibles (1-dim, `Y ↦ 0`, `X ↦ λ`). **What is
missing:** no statement/construction that each `λ ∈ k` is *realized* by an actual irreducible
`g k`-module (equivalently, that the trivial-`Y` scalar-`X` reps exist and are irreducible),
and no distinctness ("different `λ` ⇒ non-isomorphic"). `grep` over the file and the whole
`EtingofRepresentationTheory/` tree confirms **no** char-0 `g k`-module is constructed anywhere.
So "classify" is rendered only in the "⇒" direction. This is the completeness gap.

### 3.3 Char `p` — FAITHFUL and non-vacuous

- `ρ : g k →ₗ⁅k⁆ Module.End k (ZMod p → k)` (line 288) is a genuine Lie-algebra homomorphism:
  `map_add'`, `map_smul'`, and crucially `map_lie'` are all fully proved. `ρ_X : ρ (X) = diagOp`
  and `ρ_Y : ρ (Y) = shiftOp` (lines 337, 347). The key relation
  `bracket_diag_shift : ⁅diagOp, shiftOp⁆ = shiftOp` (line 252) mirrors `[X,Y]=Y`.
  `diagOp` genuinely has the `p` distinct eigenvalues `lam k p i` (`lam` injective, line 227),
  and `shiftOp` is the genuine cyclic shift `v ↦ v(· - 1)`.
- `repModule_irreducible` (line 398): proves `LieModule.IsIrreducible k (g k) (ZMod p → k)`
  from the genuine "no nontrivial `LieSubmodule`" condition (`IsIrreducible.mk`, `N ≠ ⊥ → N = ⊤`),
  by the minimal-support argument the book/plan describes (diagonal action shrinks support to a
  point, shift `p`-cycle sweeps all basis vectors). Genuine irreducibility, no surrogate.
- `lie_theorem_fails_charP` (line 495): `¬ ∀ (M : Type) …, finrank k M = 1`, witnessed by
  `k^{ℤ/p}` whose `finrank` is `card (ZMod p) = p`, and `p.Prime.one_lt` gives `p ≠ 1`. This is
  a correct negation of "every f.d. irreducible is 1-dimensional" — a faithful "no" to the
  book's positive-characteristic question. The extra `[IsAlgClosed k]` hypothesis only
  *strengthens* the counterexample (Lie's theorem fails even over alg-closed `k`), so it is
  faithful, not a weakening. The universe specialization to `M : Type` (matching the witness's
  universe) is a soundness-neutral technical choice, documented at lines 215–217 / 492–494.

## 4. "Irreducible" is genuine

`LieModule.IsIrreducible R L M` unfolds (Mathlib `Algebra/Lie/Semisimple/Defs.lean:33`) to
`IsSimpleOrder (LieSubmodule R L M)` — the honest "only submodules are `⊥` and `⊤`, and they
differ" condition, carrying `Nontrivial M`. Both the char-0 hypothesis and the char-`p`
conclusion use exactly this. No surrogate notion is substituted anywhere.

## 5. Non-vacuity

- **Char `p` (witnessed):** `k^{ℤ/p}` is a genuine dimension-`p` module (`p` prime `≥ 2`), and
  `repModule_irreducible` proves it irreducible, so `lie_theorem_fails_charP` is a real
  counterexample, **not vacuous**. Inhabitable e.g. `k = algebraic closure of `𝔽ₚ``.
- **Char 0 (in principle, but unwitnessed):** the universally-quantified char-0 statements are
  not *logically* vacuous — irreducible `g k`-modules exist (any 1-dimensional module is
  irreducible). But the file supplies **no** witnessing char-0 module, so inhabitability is
  argued only externally. This coincides with the §3.2 gap: constructing the `λ`-family would
  both complete the classification and exhibit the witnesses.

## 6. Verdict and follow-up

- `progress/items.json` (`Chapter2/Problem2.16.2`): `fidelity` set to **`gap`** with a note
  pointing to the missing char-0 `λ`-realization existence half.
- Follow-up `feature` issue filed (**#7206**): construct, for each `λ ∈ k` (char 0, `k` alg. closed), the
  1-dimensional `g k`-representation `X ↦ λ, Y ↦ 0`, prove it is irreducible, and (ideally)
  that distinct `λ` give non-isomorphic reps — completing "classify" to a biconditional
  `irreducible f.d. ↔ ≅ (λ) for a unique λ`.

No Lean edits were made in this review (report-only, per the issue). The existing statements
and proofs are all correct and axiom-clean; the gap is purely the absent existence half of the
char-0 classification.

# Statement-fidelity & non-vacuity audit — Ch3 Theorem 3.8.1 (Krull-Schmidt)

**Date:** 2026-07-21
**Reviewer:** review session (issue #7152)
**Files audited:**
- `EtingofRepresentationTheory/Chapter3/Theorem3_8_1.lean` (845 lines, 0 sorry)
- `EtingofRepresentationTheory/Chapter3/Lemma3_8_2.lean` (Fitting dependency, 0 sorry)
- `EtingofRepresentationTheory/Chapter2/Definition2_3_8.lean` (`IsIndecomposable`)
- Book source: `blobs/Chapter3/Theorem3.8.1.md`,
  `blobs/Chapter3/Discussion_proof_of_Theorem3.8.1.md`

## Verdict summary

| Declaration | Verdict |
|---|---|
| `Etingof.krull_schmidt_existence` | **FAITHFUL** |
| `Etingof.krull_schmidt_uniqueness` | **FAITHFUL** |
| `Etingof.IsIndecomposable` (Def 2.3.8, underlying predicate) | **FAITHFUL, has real content** |
| Non-vacuity / axiom audit | **CLEAN** (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) |

No defect found. This is a **report-only** deliverable; no `.lean` files were
modified.

## Book statement

> **Theorem 3.8.1** (Krull-Schmidt). *Any finite dimensional representation of A
> can be uniquely (up to an isomorphism and the order of summands) decomposed
> into a direct sum of indecomposable representations.*

The single book sentence bundles an existence claim ("can be decomposed") and a
uniqueness claim ("uniquely up to isomorphism and order"). The Lean encoding
splits these into two public theorems, which together render the book statement.

## 1. Existence — `Etingof.krull_schmidt_existence`

```
theorem Etingof.krull_schmidt_existence (k A V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] :
    ∃ (n : ℕ) (W : Fin n → Submodule A V),
      (∀ i, Etingof.IsIndecomposable A (W i)) ∧
      iSup W = ⊤ ∧ iSupIndep W
```

**FAITHFUL.**

- **Genuine internal direct sum, not a weaker covering claim.** The conjunction
  `iSup W = ⊤ ∧ iSupIndep W` is exactly Mathlib's characterization of an internal
  direct-sum decomposition: `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`
  states `DirectSum.IsInternal W ↔ iSupIndep W ∧ iSup W = ⊤`. The file itself
  relies on this equivalence (Theorem3_8_1.lean:236-239) to build the internal
  direct sum from the two conditions. `iSup W = ⊤` alone would be a mere spanning
  ("covering") claim; the added `iSupIndep W` upgrades it to a genuine direct sum
  (pairwise-independent summands). So the `Fin n`-indexed family with these two
  conditions is a real internal `⊕`, matching the book's "direct sum".
- **Indecomposable factors.** `∀ i, Etingof.IsIndecomposable A (W i)` requires
  each summand to be indecomposable, matching "direct sum of *indecomposable*
  representations".
- **`n = 0` edge case is correct.** When `V = 0`, the empty family (`n = 0`) is a
  valid decomposition (empty direct sum), which is the mathematically correct
  reading of the book for the zero representation. Not a vacuity problem.

## 2. Uniqueness — `Etingof.krull_schmidt_uniqueness`

```
theorem Etingof.krull_schmidt_uniqueness (k A V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V]
    {n m : ℕ} (W : Fin n → Submodule A V) (W' : Fin m → Submodule A V)
    (hW_indec : ∀ i, Etingof.IsIndecomposable A (W i))
    (hW'_indec : ∀ i, Etingof.IsIndecomposable A (W' i))
    (hW_ne : ∀ i, W i ≠ ⊥) (hW'_ne : ∀ i, W' i ≠ ⊥)
    (hW_sup : iSup W = ⊤) (hW_ind : iSupIndep W)
    (hW'_sup : iSup W' = ⊤) (hW'_ind : iSupIndep W') :
    n = m ∧ ∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i)))
```

**FAITHFUL.**

- **Captures uniqueness up to isomorphism AND reordering — both halves.** The
  conclusion is a conjunction:
  1. `n = m` — the two decompositions have equal numbers of summands, and
  2. `∃ σ : Fin n ≃ Fin m, ∀ i, Nonempty ((W i) ≃ₗ[A] (W' (σ i)))` — there is a
     bijection (permutation/matching) `σ` of the index sets under which every
     summand `W i` is `A`-linearly isomorphic to its partner `W' (σ i)`.

  This is precisely "uniquely up to an isomorphism and the order of summands":
  `σ` is the reordering ("order of summands"), and the `≃ₗ[A]` gives the summand
  isomorphisms ("up to an isomorphism"). The statement does **not** stop at
  equal counts (`n = m`) — the isomorphism matching is present — nor does it
  give only isomorphisms without a permutation. Both required components are
  there.

- **`Nonempty (… ≃ₗ[A] …)` is the right strength.** Uniqueness "up to
  isomorphism" is an existence-of-isomorphism claim, correctly modeled by
  `Nonempty` of the `LinearEquiv` type rather than a chosen equivalence.

### Scope nuance (not a defect): redundant `hW_ne` / `hW'_ne`

The uniqueness hypotheses `hW_ne : ∀ i, W i ≠ ⊥` and `hW'_ne` are logically
**redundant**: `Etingof.IsIndecomposable A (W i)` already contains a
`Nontrivial ↥(W i)` conjunct (see §3), which is equivalent to `W i ≠ ⊥`. Requiring
them explicitly slightly over-specifies the hypothesis list but does **not**
weaken the theorem in any meaningful way (the extra hypotheses are derivable, so
any caller holding indecomposability can discharge them). In particular this is
not a *stronger-than-the-book* assumption. It is a minor formalization
convenience, harmless to fidelity.

## 3. `Etingof.IsIndecomposable` has real content

```
def Etingof.IsIndecomposable (A V : Type*) [Ring A] [AddCommGroup V] [Module A V] : Prop :=
  Nontrivial V ∧ ∀ (W₁ W₂ : Submodule A V), IsCompl W₁ W₂ → W₁ = ⊥ ∨ W₂ = ⊥
```

**FAITHFUL, non-vacuous.** This is Etingof Definition 2.3.8: "a *nonzero*
representation V ... not isomorphic to a direct sum of two nonzero
representations." The `Nontrivial V` conjunct enforces nonzero, and the second
conjunct rules out any complementary splitting into two nonzero pieces. Crucially
the `Nontrivial V` component means `IsIndecomposable` is **not** vacuously
satisfiable (the zero module fails it), so the existence theorem's conclusion is
a real decomposition into genuine nonzero indecomposables, not an empty claim.

## 4. Proof route uses Lemma 3.8.2 (Fitting), as the book prescribes

The book proves uniqueness by induction on `dim V`, using the following Lemma
3.8.2: an endomorphism of an indecomposable finite-dimensional module is either
nilpotent or an isomorphism, and a sum of nilpotents is nilpotent.

The Lean proof honors this route:

- `Chapter3/Lemma3_8_2.lean` provides both parts, sorry-free:
  - `Etingof.endo_indecomposable_iso_or_nilpotent` — 3.8.2(i): bijective or
    nilpotent (proved via Mathlib's Fitting decomposition
    `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`).
  - `Etingof.sum_nilpotent_endo_indecomposable` — 3.8.2(ii): a finite sum of
    nilpotent endomorphisms is nilpotent.
- The internal helper `krull_schmidt_find_iso_summand` invokes both:
  `sum_nilpotent_endo_indecomposable` (Theorem3_8_1.lean:313) to derive that the
  endomorphisms `θ_s` summing to the identity cannot all be nilpotent, and
  `endo_indecomposable_iso_or_nilpotent` (lines 321, 357) to promote a
  non-nilpotent `θ_{j₀}` to an isomorphism — exactly the book's
  `∑ θ_s = 1 ⇒ some θ_s` is an iso argument.
- `krull_schmidt_uniqueness_aux` (line 477) then runs the book's induction on
  `Module.finrank k V`, splitting off the matched summand `W' j₀` and matching the
  complements via `isCompl_equiv_of_isCompl`.

The intended dependency chain (Krull-Schmidt uniqueness → Lemma 3.8.2 → Fitting)
is therefore recorded in the code.

### Scope nuance (favorable, not a defect): Problem 3.8.3 is subsumed

The book's proof of Lemma 3.8.2 assumes `k` is algebraically closed, and
**Problem 3.8.3** explicitly asks the reader to remove that assumption. The Lean
`endo_indecomposable_iso_or_nilpotent` proof uses the Noetherian/Artinian Fitting
decomposition and requires only `[Field k]` (no `IsAlgClosed`). The formalization
is therefore *more general* than the book's stated proof and effectively solves
Problem 3.8.3, while remaining faithful to the Theorem 3.8.1 statement.

## 5. Hypotheses match the book, nothing silently stronger

- `[Field k]` + `[FiniteDimensional k V]` renders the book's "finite dimensional
  representation" (`dim_k V < ∞`). This is the intended finiteness.
- `[Ring A] [Algebra k A] [Module A V] [IsScalarTower k A V]` is the standard
  scaffolding for "representation of the algebra A over k" — `V` is an
  `A`-module whose `A`-action is compatible with the base `k`-action.
- **No hidden strengthening.** There is no commutativity of `A`, no algebraic
  closedness of `k`, and no semisimplicity assumption. This matters:
  Krull-Schmidt is a theorem about *indecomposable* (not necessarily
  irreducible) decomposition and holds without semisimplicity; the Lean statement
  correctly makes no such assumption.

## 6. Non-vacuity / axiom audit

`lake build EtingofRepresentationTheory.Chapter3.Theorem3_8_1` exits 0 (1593
jobs; only pre-existing `linter.style.show` style warnings, no errors).
`grep -c sorry` = 0 in both `Theorem3_8_1.lean` and `Lemma3_8_2.lean`.

`#print axioms`:

```
'Etingof.krull_schmidt_existence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.krull_schmidt_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.endo_indecomposable_iso_or_nilpotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Etingof.sum_nilpotent_endo_indecomposable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All four reduce to the three standard Lean/Mathlib axioms with **no `sorryAx`**
and **no stray custom axiom**. The theorems are genuinely proved.

## Conclusion

Both `Etingof.krull_schmidt_existence` and `Etingof.krull_schmidt_uniqueness` are
**FAITHFUL** renderings of Etingof Theorem 3.8.1, together capturing existence
and uniqueness-up-to-isomorphism-and-reordering. The underlying
`IsIndecomposable` predicate carries real (nonzero, no-nontrivial-splitting)
content, the proof genuinely runs through Lemma 3.8.2 (Fitting) as the book
prescribes, and the axiom audit is clean. The only nuances are favorable or
harmless: the uniqueness hypotheses `hW_ne`/`hW'_ne` are redundant (derivable
from indecomposability), and the Lemma 3.8.2 proof is more general than the
book's (solving Problem 3.8.3 by not needing algebraic closedness). No fidelity
or non-vacuity defect found; no follow-up `feature` issue required.

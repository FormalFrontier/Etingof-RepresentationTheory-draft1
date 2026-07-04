# Fidelity sweep — Wave 9 (Chapter 9, issue #5346)

Judge: Fable 5 (main auditor for the six changed items, three parallel
sub-auditors for the twelve previously-verified items), distinct from the
Sonnet/Opus authors of the items below.
Scope: all 18 Chapter 9 claim-bearing done items (types theorem / proposition /
lemma / corollary / definition / example / remark).
Method: PLAN.md Stage 3.2 steps 6–7 — anti-vacuity decision test, then
conjunct-by-conjunct fidelity of the Lean statement against the book blob.
Calibrated on confirmed examples #5322, #5323, #5326.

## Context

Issue #5346 was created with all 18 items at `fidelity: unchecked`, but waves
1–4 had already assigned verdicts (12 verified, 5 gap, 1 non-standard
`faithful`) and opened repair issues for the gaps — without writing a Chapter 9
wave certificate or reconciling once the repairs merged. All five gap-repair
issues (#5669, #5664, #5631, #5648, #5665) and the `faithful` resolution issue
(#5738) had since closed, with the repairs on `main`. This wave re-audits every
item against the **current** (post-repair) Lean, reconciles the merged repairs,
normalizes the `faithful` label, and — following the wave-7 precedent —
re-checks the previously-`verified` items rather than trusting them.

Re-auditing the 12 previously-`verified` items was again not a formality:
1 of them (Definition9.5.1, verified by both wave 1 and wave 2) was
**refuted to `gap`**.

## Outcome

After this wave every Chapter 9 claim-bearing done item (18 total) is
**`verified` (17)** or **`gap` (1)**; no item remains `unchecked` or
`faithful`. Only `progress/items.json` and this file were touched — no Lean
changes.

- **verified: 17**
- **gap: 1** — Definition9.5.1 (#5850, new).

Method caveat: no `lake build` was run (no Lean files changed in this wave);
statements were inspected in the current checked-in code on `main`, and
`sorry` absence in the audited files was checked by grep, not by compilation.
The repairs themselves were build-verified by CI on their own merged PRs.

### Gap → verified reconciliations (5; merged repairs confirmed faithful)

- **Theorem9.2.1** (was gap #5669, dropped uniqueness) — `Theorem_9_2_1_i` now
  carries the uniqueness conjunct: any indecomposable f.g. projective `Q` with
  the same Kronecker-delta Hom property at index `i` is `≃ₗ[A] P i`, proved via
  Fitting's lemma (`indecomposable_projective_iso_of_hom`). Parts (ii)
  (`A ≃ₗ[A] ⨁ᵢ (dim Mᵢ) · P i`) and (iii) (completeness of the classification)
  match the book; the `P i` are genuinely constructed as left ideals
  `A·eᵢ` from lifted Wedderburn–Artin idempotents. No sorry. → **verified**.
- **Definition9.2.2** (was gap #5664, missing essential-epi) — repaired via
  PR #5702: `ProjectiveCover` now bundles `surjection_essential`
  (`∀ N, N ⊔ ker π = ⊤ → N = ⊤`, the superfluous-kernel condition) alongside
  projectivity, indecomposability, and surjectivity. → **verified**.
- **Definition9.3.1** (was gap #5631, degenerate wrapper) — `algebraCartanMatrix`
  no longer wraps an arbitrary `jhMultiplicity` function; it is genuinely
  constructed as `cᵢⱼ = finrank k (P i →ₗ[A] P j)`, exactly the book's
  `cᵢⱼ := dim Hom_A(Pᵢ, Pⱼ)` (§9.3 opening), with the `[Pⱼ : Mᵢ]` reading
  recovered by Proposition 9.2.3. → **verified**. *Noted residual (not a gap):*
  the blob's prose observation "nonnegative entries, positive diagonal" has no
  Lean lemma for the positive-diagonal half (nonnegativity is inherent in the
  ℕ-valued matrix); it is an "obviously" remark the book derives from the
  formalized Prop 9.2.3.
- **Example9.5.2** (was gap #5648, three findings) — repaired via PRs
  #5730/#5734 and re-confirmed on the issue: (i) `semisimple_areLinked_iff_iso`
  (+ corollary `semisimple_blocks_singleton`), (ii)
  `local_artinian_single_block`, (iii) `problem_9_3_2_single_block` via a fully
  constructed algebra `ℂ⟨g,x⟩/(gx+xg, x², g²−1)` with a genuine nonsplit
  extension (`extClass_ne_zero`). Non-vacuous throughout. → **verified**.
  *Noted residuals (adjudicated in #5648, not silent):* (i)'s "each block ≃
  Vec" is captured at the one-simple-object level per the module docstring's
  scope note; (iii) does not prove S₊/S₋ exhaust the simples of that algebra.
  Note these statements survive the Definition9.5.1 finding below: under the
  coarser `AreLinked`, (i)/(ii) conclusions are stronger than or equal to the
  book's, and (iii)'s witness is a direct Ext¹ link between two simples, which
  is also a book-chain of length 1.
- **Theorem9.6.4** (was gap #5665, Noetherian over-hypothesis) —
  `Theorem_9_6_4` and `Theorem_9_6_4_corollary` now assume only the book's
  hypotheses (k-linear finite abelian category over a field, progenerator P)
  and *derive* `IsNoetherianRing (End P)ᵐᵒᵖ` via
  `isNoetherianRing_endOp_of_overField`; the Noetherian-hypothesis variants
  are retained as explicitly-labeled ring-level engines. → **verified**.

### `faithful` normalization (1)

- **Corollary9.7.3** (was non-standard `faithful`, #5738) — gap 2 of #5738 is
  closed by `Corollary_9_7_3_i_categorical_fgModule`: for a k-linear finite
  abelian category over an algebraically closed field with progenerator P,
  a basic algebra B with the single equivalence `𝒞 ≌ FGModuleCat B` — the
  book's part (i). Uniqueness by `Corollary_9_7_3_i_unique` (dimension/corner
  argument via MoritaStructural), dimension bound by `Corollary_9_7_3_ii`.
  The existence construction (`exists_basic_morita_equivalent`) proves both
  the book's literal `IsBasicAlgebra` (B/Rad(B) commutative) and the split
  form used by the Morita development. → **verified**. *Noted residual (gap 1
  of #5738, documented in the module docstring):* the progenerator P is
  carried as an explicit hypothesis rather than produced — consistent with how
  the audited Theorem 9.6.4 is stated; the book constructs P = ⊕ Pᵢ in the
  §9.6 discussion (Problem 9.6.5, `not_formalized`).

### verified → gap (1; prior verdict refuted)

- **Definition9.5.1** (→ new issue #5850) — the book defines linking on
  **simple** modules via chains **of simple modules** with Ext¹ ≠ 0, and the
  k-th block 𝒞ₖ as the subcategory of objects whose Jordan–Hölder factors lie
  in one class Sₖ. The Lean `AreLinked := Relation.EqvGen (ExtOrIso R)` is
  defined on **all** of `ModuleCat R`, so chains may pass through arbitrary
  modules — strictly coarser on simples. Concrete counterexample (confirmed by
  Codex cross-vendor review): over `A = k[ε]/ε² × k[ε]/ε²` with `X`, `Y` the
  simples of the two factors, the mixed direct sum `N = X ⊕ Y` gives
  `Ext¹(X, N) ≠ 0` and `Ext¹(N, Y) ≠ 0` (since `Ext¹(k, k) ≠ 0` over
  `k[ε]/ε²`), so `AreLinked X Y` — yet `X` and `Y` lie in different book
  blocks, because Ext between simples of different product factors vanishes
  and a book chain of simples cannot cross the factors. Moreover
  `Etingof.Block := Quotient (blockSetoid R)` quotients all modules and drops
  the JH-factor condition entirely, producing spurious classes corresponding
  to no Sₖ. The divergence is not flagged in the file — a silent weakening
  (Step 7), missed by both wave 1 and wave 2.

### Previously-verified items confirmed (11)

Re-audited by three parallel sub-auditors against blob + current Lean; all
sorry-free and non-vacuous:

- **Proposition9.1.1** — both conjuncts real: existence of an idempotent lift,
  and conjugacy of any two lifts by a unit `u` with `u − 1 ∈ I`.
- **Definition9.1.2** — Mathlib `CompleteOrthogonalIdempotents`: idem +
  pairwise-orthogonal + `∑ eᵢ = 1`, all three book conjuncts.
- **Corollary9.1.3** — lifts a complete orthogonal system mod a nilpotent
  two-sided ideal, componentwise lifting equations asserted.
- **Proposition9.2.3** — exact equality `finrank k Hom(Pᵢ, N) =
  compositionFactorMultiplicity s (Mᵢ)` for every composition series, with a
  genuine factor-counting function. (Minor: `hM`/`hP_indec` hypotheses unused
  — mild over-hypothesizing, not a weakening.)
- **Definition9.4.1** — delegates to Mathlib `CategoryTheory.projectiveDimension`
  (Ext-vanishing form, agrees with shortest-resolution length; `⊥`-for-zero
  deviation documented).
- **Definition9.4.3** — `∀ M, HasProjectiveDimensionLE M d` + infimum with `⊤`
  convention, the book's definition exactly.
- **Example9.4.4** — `homologicalDimension (MvPolynomial (Fin n) k) = n`, both
  `le_antisymm` directions substantive (Koszul SES induction; augmentation
  module non-projectivity + Shapiro transfer).
- **Definition9.6.1** — `IsFiniteAbelianCategory` carries both book conjuncts
  (enough projectives, finitely many simples up to iso) plus the §9.6
  standing finite-length assumption; the over-a-field data lives in
  `IsFiniteAbelianCategoryOverField` scoped to the Introduction_9.6 item.
- **Definition9.6.2** — `IsProgenerator extends Projective` + epi from a finite
  biproduct `Pⁿ` onto every object; both conjuncts.
- **Definition9.7.1** — `MoritaEquivalent` is a genuine `ModuleCat A ≌
  ModuleCat B`; full-module-category substitution for A-fmod is an honest
  documented note (equivalent for f.d. algebras); `KLinearMoritaEquivalent`
  adds functor linearity with proved refl/symm/trans.
- **Definition9.7.2** — `IsBasicAlgebra` is literally "B/Rad(B) commutative";
  the strictly-stronger `IsBasicAlgebraSplit` is documented as the
  algebraically-closed reading, not silently substituted. (Wave-9 also removed
  this item's stale `fidelity_issue` #5386, closed with the repair on main.)

## Sweep status

Chapter 9 fidelity: 17/18 verified, 1 gap. This is the first Chapter 9 wave
certificate. The one gap is tracked by open repair issue #5850, linked to
#5346; a future wave should reconcile it once repaired, and the sweep may not
be called complete until it reaches two consecutive dry waves.

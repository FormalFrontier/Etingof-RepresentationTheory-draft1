# Fidelity sweep — Wave 8 (Chapter 8, issue #5345)

Judge: Fable 5 (single auditor, full statement-by-statement read), distinct
from the Sonnet/other authors and repairers of the items below, and distinct
from the wave-1/wave-2 (Sonnet) and Codex judges whose verdicts this wave
reconciles.
Scope: all 9 Chapter 8 claim-bearing done items (types theorem / proposition /
lemma / corollary / definition / example / remark), per
`progress/coverage-audit/fidelity-worklist.tsv`.
Method: PLAN.md Stage 3.2 steps 6–7 — anti-vacuity decision test, then
conjunct-by-conjunct fidelity of the Lean statement against the book blob.
Calibrated on confirmed examples #5322, #5323, #5326.
Cross-vendor check: OpenAI Codex independently reviewed all five judgment
calls below and concurred with every verdict (9/9 verified, no downgrades),
with one caveat noted under Definition8.1.8.

## Context

Issue #5345 was created with all 9 items at `fidelity: unchecked`, but the
wave-1/wave-2 sweeps had already assigned verdicts (5 verified, 2 gap, 2
non-standard `faithful`) and opened repair issues — without reconciling once
the repairs merged. All four Chapter 8 repair issues (#5627, #5628, #5629,
#5630) have since closed via merged PRs (#5690, #5694, #5697, #5698). This
wave re-audits every item against the **current** (post-repair) Lean on
`main`, reconciles the merged repairs, normalizes the `faithful` labels, and
re-checks the previously-`verified` items rather than trusting them (wave 7
refuted 3 previously-`verified` Chapter 7 items, so this is not a formality).

## Outcome

After this wave every Chapter 8 claim-bearing done item (9 total) is
**`verified` (9)**; no item remains `unchecked`, `faithful`, or `gap`.
Only `progress/items.json` and this file were touched — no Lean changes.

- **verified: 9**
- **gap: 0**

### Gap/faithful → verified reconciliations (4; merged repairs confirmed faithful)

- **Theorem8.1.1** (was `faithful`, issue #5629, repaired by PR #5697) —
  `EtingofRepresentationTheory/Chapter8/Theorem8_1_1.lean`. The wave-2 gap
  (condition (iv), exactness of `Hom_A(P,?)`, absent) is repaired:
  `Theorem_8_1_1_i_iff_iv` states projectivity ⟺ preservation of short exact
  sequences by `Hom_A(P,?)`, with all three conjuncts of the image sequence
  asserted (injectivity at `Hom(P,K)`, `range = ker` at `Hom(P,M)`,
  surjectivity onto `Hom(P,N)`). Conditions (ii) (`i_iff_ii`, split
  surjections) and (iii) (`i_iff_iii`, retract of a free module — the standard
  equivalent of the book's "P ⊕ Q free"; the `∃ Q` is constrained by
  `Module.Free R Q` and the split `s ∘ i = id`, so it is not vacuous) are as
  before. The hub is `Module.Projective`, documented as condition (i) with the
  Mathlib bridge lemmas (`Module.projective_lifting_property` /
  `Module.Projective.of_lifting_property`) cited in the module docstring and
  used inside the proofs, satisfying the Stage 3.2 step 4 bridge-note
  requirement. Both directions of every iff are proved; nothing decorative.
  **verified**.
- **Theorem8.1.5** (was `faithful`, issue #5630, repaired by PR #5698) —
  `Theorem8_1_5.lean`. The wave-2 gap (condition (iii), exactness of
  `Hom_A(?,I)`, absent; Baer substituted) is repaired:
  `Theorem_8_1_5_i_iff_iii` states injectivity ⟺ preservation of short exact
  sequences by contravariant `Hom_A(?,I)`, all three conjuncts asserted.
  `Module.Injective` is literally the book's condition (i) (extension along
  injections); `i_iff_ii` covers (ii). Baer's criterion is retained but now
  explicitly labelled "supplementary characterization, not one of the book's
  three conditions" in both docstring and theorem header. **verified**.
- **Definition8.1.2** (was `gap`, issue #5627, repaired by PR #5690) —
  `Definition8_1_2.lean`. The `[CommRing R]` narrowing is repaired: the abbrev
  `Etingof.ProjectiveModule` now requires only `[Ring R]`, matching Theorem
  8.1.1's setting and the book's general (possibly non-commutative) algebra,
  with a docstring note explaining the choice. Real data (alias of
  `Module.Projective`), no sorried obligations. **verified**.
- **Definition8.2.3** (was `gap`, issue #5628, repaired by PR #5694) —
  `Definition8_2_3.lean`. The wave-2 gap (Mathlib's monoidal
  `CategoryTheory.Tor` cannot express the book's asymmetric right-module ×
  left-module Tor over a non-commutative ring) is repaired by a genuine direct
  construction: the balanced tensor `M ⊗_A N` is built as the quotient of
  `M ⊗_ℤ N` by the balancing subgroup `⟨(m·a) ⊗ n − m ⊗ (a·n)⟩`, right
  `A`-modules are `ModuleCat Aᵐᵒᵖ`, `tensorRightFunctor A N` is proved
  additive, and `Etingof.Tor A M N n` is its `n`-th left derived functor
  evaluated at `M`. Mathlib's `Functor.leftDerived` is by definition the
  homology of the functor applied to a projective resolution of `M`, so this
  matches the book's "i-th homology of `P• ⊗_A N`" with
  resolution-independence built in; the equivalence is documented in the
  module docstring. All data real, no sorries. **verified**.

### Previously-verified items re-checked (5; all upheld)

- **Definition8.1.6** — `Etingof.InjectiveModule` = `Module.Injective R M`
  over `[Ring R]`; `Module.Injective` is literally condition (i) of Theorem
  8.1.5, whose equivalence with (ii)–(iii) is the (formalized) Theorem 8.1.5.
  **verified**.
- **Example8.1.7** — the wave-1 vacuity (one-directional, field-only,
  decorative hypothesis) is long gone: `Etingof.Example_8_1_7` is a genuine
  biconditional `Module.Projective A P ↔ Module.Injective Aᵐᵒᵖ (Dual k P)`
  over a finite-dimensional algebra `A` and finite-dimensional `P` (the book's
  Chapter 8 standing convention), with the dual carrying a real contragredient
  right-`A`-action (`contragredient` instance, defining equation
  `contragredient_smul_apply`). Forward direction proved for *any* `k`-algebra
  (no finiteness); converse via the finite-dimensional evaluation isomorphism.
  The finite-dimensionality restriction on the converse (vs. the book's bare
  "algebra") is honestly documented: the infinite-dimensional case needs
  Bass's perfect-ring theorem, absent from Mathlib. Both hypotheses genuinely
  used; nothing vacuous. Stale wave-1/2 bookkeeping fields dropped
  (repair issue #5385 closed). **verified**.
- **Definition8.1.8** — `Etingof.ProjectiveObject` / `InjectiveObject` alias
  `CategoryTheory.Projective` / `Injective` (lifting-property form, over any
  category) where the book defines via Hom-exactness in an abelian category.
  Wave-2 flagged this; a Codex cross-vendor tiebreak adjudicated it faithful.
  Upheld here: the lifting form agrees with Hom-exactness on the book's
  domain (abelian categories) — left-exactness of Hom is automatic and the
  surjectivity conjunct is precisely the lifting property, exactly the bridge
  proved in module form in `Theorem_8_1_1_i_iff_iv` / `Theorem_8_1_5_i_iff_iii`
  — and the extra generality (`[Category C]` rather than `[Abelian C]`) is a
  conservative extension of the same kind accepted (indeed demanded) in the
  #5627 repair. Adjudication provenance moved here from the item's
  `fidelity_note`. Wave-8 Codex concurrence adds the caveat that this is the
  weakest bridge in the chapter — documented rather than formalized in-file;
  an explicit abelian-category bridge theorem (lifting ⟺ Hom-exactness)
  would strengthen it, but its absence is not a fidelity gap. **verified**.
- **Definition8.2.1** — `Etingof.ProjectiveResolution` =
  `CategoryTheory.ProjectiveResolution X` over `[Abelian C]`: a chain complex
  of projectives with a quasi-isomorphism to `X`, i.e. exactly the book's
  exact sequence `⋯ → P₁ → P₀ → M → 0` with all `Pᵢ` projective. **verified**.
- **Definition8.2.4** — `Etingof.Ext` = `CategoryTheory.Abelian.Ext M N n`
  (derived-category shifted homs), specializing to the classical Ext for
  `ModuleCat A`; both book arguments are left `A`-modules, so no
  non-commutative asymmetry arises (unlike Tor) and Mathlib's Ext applies
  as-is. The derived-category-vs-resolution-homology reformulation is the
  same standard, documented equivalence accepted for Definition8.2.3.
  **verified**.

## Sweep status

Chapter 8 fidelity: 9/9 verified, 0 gap. This is the first Chapter 8 wave
certificate; with it the chapter's worklist is fully reconciled — no open
Chapter 8 repair issues remain. Per PLAN §3.7 the sweep as a whole may not be
called complete until two consecutive dry waves; this wave was dry for
Chapter 8 (no new gaps found).

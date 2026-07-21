# Docstring-Fidelity Wave Audit (Issue #7088)

**Date:** 2026-07-21 (UTC)
**Session type:** review
**Scope:** Spot-check the docstring-fidelity PR wave (36 `docstring-fidelity`
PRs among the 71 merged since summarize #6917 closed 2026-07-18) for *claim
accuracy* — verify that docstrings now asserting "proved sorry-free in-file"
name theorems that (a) exist, (b) are genuinely sorry-free, and (c) state what
the docstring says, with no overclaim of scope and no over-correction of a
genuine deferral.

**This is a read-and-report review. No `.lean` files were edited.** The three
findings below are proposed corrections; a follow-up `feature` issue can apply
them.

---

## Method

1. **Genuine-sorry baseline.** Re-ran the comment-stripped depth-counter (the
   `awk` `/- … -/` counter from
   `progress/2026-07-11T00-49-00Z-sorry-landscape.md` lines 70-80) across the
   whole `EtingofRepresentationTheory/` tree. Result reproduced exactly:

   ```
   1  EtingofRepresentationTheory/Chapter2/Problem2_16_3.lean
   ```

   The single genuine sorry is `finrank_g_three` (Problem 2.16.3(a)), claimed
   under #7084 — expected and not flagged. Every sampled file below prints
   nothing under this counter (genuinely sorry-free code).

2. **Per-file check.** For each sampled file, for each theorem/def *named* in a
   docstring as proved sorry-free:
   - **Existence** — `grep` the exact name in-file (and in any named sibling
     file the docstring points to).
   - **Sorry-free / non-vacuous** — comment-stripped depth-counter on the file;
     confirm the named decl is a real Prop (not `: True`, not vacuous).
   - **Scope** — read the actual signature; compare its hypotheses
     (`IsAlgClosed`, `CharP`/`p ≠ 2`, `[Fact p.Prime]`, finite-dimensionality,
     `IsAlgDense`, `CharZero`, …) against what the docstring claims.
   - **Over-correction** — check no genuine deferral of a sub-part was silently
     erased.

3. **Legitimate patterns held harmless** (per the issue): "not yet formalized
   **in Mathlib**" statements, and honest "this sub-part / the full
   classification is deferred" scope statements, are correct and were **not**
   flagged.

---

## Sample (25 primary files + verified siblings)

Spans all audited chapters and every merged docstring-fidelity PR family.

**Chapter 2:** Problem2_5_2 (#7051), Problem2_16_4 (legitimate-deferral
reference case), Problem2_16_5 (#7061), Problem2_11_3, Problem2_13_1,
Problem2_8_11.
**Chapter 4:** Exercise4_2_3 (#7077) + Exercise4_2_3_Assembly (+ its sorry-free
dependency files FieldGeneral / StrictBound / SplitSimples).
**Chapter 5:** PolynomialRepEmbedding (#7044/#7066) + sibling
PolynomialTensorBridge (#7050), Theorem5_22_1 (#7086) + siblings
Lemma5_13_1 / CharacterOrthogonality, LinearDualDetTwistCharacter (#7075),
GL2ConjugacyClassCount, SchurModuleSpecialBlock (#7043) + sibling
Theorem5_22_1:1195, PolynomialGLRightAction, Example5_1_3, Theorem5_18_1,
Theorem5_12_2_Irreducible.
**Chapter 6:** Proposition6_6_7 (#7085), Problem6_1_5_OrbitComorphism (#7079)
+ siblings OrbitInjective / DimBound.
**Chapter 8:** Problem8_2_8 (#7056).
**Chapter 9:** Theorem9_2_1 (#7016), KrullSchmidt/Length (#7015),
KrullSchmidt/Fitting (#7015), Definition9_7_1, Definition9_2_2.
**Chapter 7:** Example7_2_2.

---

## Findings (3)

All three are the failure mode the issue anticipated — a docstring drifting
ahead of the code. **None** is a false sorry-free claim (all files are
genuinely sorry-free); each is a *prose* inaccuracy: one names a lemma that
does not exist, and two carry stale "remaining / to be discharged" phrasing
that reads as if a proved result is still open.

### Finding 1 — `LinearDualDetTwistCharacter.lean:38` (existence mismatch)

The module docstring's "## What this file proves" list contains a bullet naming
`detTwist_dual_algIrrepρ_eq` (lines 38-42, and the dependency-flow line at 144),
described as "collapsing the stacked twists on the contragredient … via
`dual_charTwistRep` + `charTwistRep_charTwistRep`."

**No declaration of that name exists anywhere in the repo** (grep finds only the
two docstring mentions). The collapse step is real and sorry-free, but it is
*inlined* inside `coeff_formalCharacter_detTwist_dual` (a `change` +
`dual_charTwistRep, charTwistRep_charTwistRep` rewrite), not factored into a
named lemma. So the docstring advertises a theorem the file does not provide.

**Suggested fix (choose one):** either extract the collapse as an actual
`theorem detTwist_dual_algIrrepρ_eq`, or reword lines 38-42 and the flow at line
144 to drop the standalone name, e.g. "the stacked twists collapse to a single
`det^{(m:ℤ)}` **inline within `coeff_formalCharacter_detTwist_dual`**, via
`dual_charTwistRep` + `charTwistRep_charTwistRep`."

### Finding 2 — `Chapter9/KrullSchmidt/Length.lean:542` (stale deferral, self-contradicting)

The `clength_additive` theorem docstring (lines 540-542) says of the
`clength_le_add` direction: "see its docstring for the order-reflecting
embedding `Subobject X₂ ↪ Subobject X₁ × Subobject X₃` **that remains to be
discharged**."

That is stale. `clength_le_add` is fully proved sorry-free at
`Length.lean:501`, and its own docstring (lines 493-500) describes it as the
completed Schreier half. This directly contradicts the *same file's* line 53
("… is now **proved** (`clength_additive`), sorry-free …") — the internal
inconsistency PR #7015 anticipated. (Sibling `Fitting.lean` sits on the correct
side and is clean.)

**Suggested fix:** replace "…embedding `Subobject X₂ ↪ Subobject X₁ ×
Subobject X₃` that remains to be discharged." with "…embedding `Subobject X₂ ↪
Subobject X₁ × Subobject X₃`; proved sorry-free via `Φ_reflecting` +
`height_prod_le`."

### Finding 3 — `Chapter5/SchurModuleSpecialBlock.lean:28` (stale "remaining gap", self-contradicting)

The module docstring (line 28) calls the character-determines-module step "the
single remaining gap, isolated as
`simpleSymGroupImageSubmodule_iso_of_spechtCharacter_eq` below."

Stale: that theorem is proved sorry-free (it delegates to
`simpleSubmodule_iso_of_spechtCharacter_eq` at `Theorem5_22_1.lean:1195`, itself
sorry-free), and lines 52-53 of the *same file* correctly say "It is
**proved**." "single remaining gap" reads as an open obligation.

**Suggested fix:** reword line 28 "the single remaining gap" → "the single
genuinely character-theoretic ingredient" (matching the line-52 phrasing).

---

## Clean results (no findings)

The following claims were checked and are **accurate** — named theorems exist,
are sorry-free and non-vacuous, and scope hypotheses match the docstring:

- **Scope claims correctly stated (no overclaim):** GL2ConjugacyClassCount
  (`q²−1` count gated on odd `q`, `p ≠ 2`, with the exact-division note);
  Problem2_16_4 (`finrank_irreducible_le_char` carries `[IsAlgClosed] [Fact
  p.Prime] [CharP k p] (2 < p)`); Theorem9_2_1 (`Theorem_9_2_1_i/ii/iii` carry
  `[IsAlgClosed k]`); PolynomialRepEmbedding (`[CharZero]` inj-only vs
  `[IsAlgClosed]` full equivariant embedding, `hP_mul` hypotheses honest);
  Problem8_2_8 (`Ext` half explicitly gated on finite-dimensionality);
  Problem2_16_5 (`(q:ℂ)^2 ≠ 1` = the module's standing `q ≠ ±1`);
  Problem6_1_5_OrbitComorphism siblings (`IsAlgDense`, `[Infinite k]`,
  `[Finite (orbit quotient)]` all present); Exercise4_2_3_Assembly
  (`Etingof.Exercise4_2_3` genuinely at full modular generality — arbitrary
  field with `(card G : k) = 0`, no hidden `IsAlgClosed`).

- **Legitimate deferrals correctly preserved (no over-correction):**
  Problem2_16_4 (fine highest-weight classification noted deferred);
  Problem2_5_2 (part (c) deferred); Problem2_11_3 (parts (d)-(f) deferred);
  Problem2_13_1 (Dehn-invariant parts (a),(c) deferred, part (b) proved);
  PolynomialGLRightAction (the (K′) core tracked as follow-up); Example7_2_2
  (symmetric-power / Schur-functor / reflection-functor items deferred pending
  upstream API); Exercise4_2_3 (main comparison honestly deferred to Assembly).

- **"Not yet formalized in Mathlib" statements (true, held harmless):**
  Theorem5_18_1 (double centralizer), Theorem5_12_2_Irreducible (Specht module
  irreducibility), Definition9_7_1 (Morita), Definition9_2_2 (projective
  cover), Proposition6_6_7.

- **Corrections verified genuinely landed:** Theorem5_22_1
  (`youngSym_charValue_orthogonality` and `Etingof.Lemma5_13_1` really are
  proved/used sorry-free); Proposition6_6_7 (`Proposition6_6_7_sink/source`
  carry the full indecomposability construction, the old "BLOCKED / not yet
  formalized" preamble is genuinely gone); Fitting.lean (`clength_*`
  dependencies genuinely sorry-free).

---

## Assessment

The docstring-fidelity wave is **substantially accurate**: across 25 sampled
files touching every merged PR family, no docstring made a false sorry-free
claim, no scope overclaim (hypothesis-hiding), and no over-correction of a
genuine deferral. The residual risk the issue named — prose drifting ahead of
code — materialized in exactly **3 low-severity ways**, all cosmetic to CI
(every file is sorry-free) but misleading to a reader:

1. one docstring names a lemma that was never given that name (the step is
   inlined), and
2-3. two docstrings retain stale "remaining gap / remains to be discharged"
   wording that each *self-contradicts a correct sentence in the same file*.

These are worth a small cleanup but do not indicate a systemic problem with the
wave.

**Recommended next step:** open one `feature` issue applying the three
suggested rewordings above (all pure-docstring edits, no code change, one small
PR). Findings 2 and 3 are especially clear since each contradicts the same
file's own corrected sentence.

## Verification

- Baseline reproduced: comment-stripped depth-counter reports the single
  expected `finrank_g_three` sorry and nothing else.
- Each of the three findings is reproducible: the named absence
  (`detTwist_dual_algIrrepρ_eq` — `grep` returns only docstring mentions) and
  each stale-phrasing contradiction (Length.lean:542 vs :53; SchurModule
  SpecialBlock.lean:28 vs :52-53) verified directly against the source.
- No `.lean` files edited by this review (`git diff --stat` shows only this new
  doc).

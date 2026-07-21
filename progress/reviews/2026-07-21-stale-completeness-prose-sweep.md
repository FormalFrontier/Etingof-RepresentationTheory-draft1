# Whole-tree stale-completeness-prose sweep

**Issue:** #7096 · **Session:** review · **Date:** 2026-07-21T02:35Z ·
**Base:** `origin/main` @ `fa897063`

## Summary

The tree-wide grep for stale-completeness prose returns **61 files / 65
matched lines**. Classifying each against the actual code (comment-stripped
depth-counter for sorry-freeness, plus reading the named decl) yields:

- **2 new DEFECTs** (beyond #7093's trio): `PolynomialRepEmbedding.lean:1114`
  and `GL2ConjugacyClassCount.lean:72` — both call now-proved content
  "deferred".
- **1 borderline / low-severity DEFECT**: `Exercise4_2_3_FieldGeneral.lean:59`
  — a linter-justification comment whose "until the deferred proofs are filled
  in" clause is stale (proofs are filled).
- **1 already tracked by #7093**: `KrullSchmidt/Length.lean:542`
  ("remains to be discharged"). The other two #7093 files
  (`LinearDualDetTwistCharacter.lean`, `SchurModuleSpecialBlock.lean`) do not
  match this grep pattern (their stale phrasings — a non-existent lemma name,
  and "gap" — are not in the search set), so they do not appear below; they
  remain covered by #7093.
- **The remaining 60 matched lines are LEGITIMATE**: honest "not in Mathlib /
  not yet in Mathlib" coverage statements, genuine scope deferrals to absent
  follow-up content, correct mathematical non-existence claims, the lone #7084
  sorry, and forward references inside completed proofs.

**Sweep status: NOT yet converged** — 2 (or 3, counting the borderline) new
DEFECTs to apply. After a single follow-up `feature` PR lands the #7093 trio
plus these, the tree-wide stale-completeness class is closed.

Whole-tree sorry check (comment-stripped `awk` depth counter over every
`.lean`): exactly **1** genuine sorry, `finrank_g_three` in
`Chapter2/Problem2_16_3.lean` (#7084). Every other matched file is sorry-free,
so for every DEFECT below the file is provably sorry-free and the contradiction
is real.

---

## New DEFECTs (for one follow-up `feature` PR)

### 1. `EtingofRepresentationTheory/Chapter5/PolynomialRepEmbedding.lean:1114`

- **Matched phrase:** `Proof strategy (the genuine mathematical content,
  deferred — see issue #4598 decomposition):`
- **Decl described:** `theorem polynomialRep_homogeneous_hpoly'` (line 1124).
- **Contradicting fact:** the theorem is **fully proved, sorry-free**. Its body
  (lines 1136–1142) assembles the "deferred" strategy directly:
  `hpoly'_of_scalarGL_action k N n M halg h_span (fun t => scalarGL_acts_as_pow …)`.
  Both helpers are real proved private theorems in the same file —
  `scalarGL_acts_as_pow` (line 799) and `hpoly'_of_scalarGL_action` (line 1072)
  — and the file contains **no `axiom`**. The docstring's very next sentences
  ("evaluate the matrix-coefficient identity at the scalar matrix … clear
  denominators … Zariski density …") describe exactly what the proof carries
  out. So the mathematical content is present, not deferred.
- **Suggested reword:** drop "deferred — see issue #4598 decomposition"; e.g.
  "Proof strategy (carried out below, assembled from `scalarGL_acts_as_pow`
  and `hpoly'_of_scalarGL_action`; issue #4598 decomposition):".

### 2. `EtingofRepresentationTheory/Chapter5/GL2ConjugacyClassCount.lean:72`

- **Matched phrase:** `The three deferred per-type counts all follow the same
  recipe:`
- **Context:** module docstring of the `## A class-count bridge` section.
- **Contradicting fact:** the three per-type counts are **proved and consumed**.
  `numParabolicClasses_eq` (line 743), `numSplitSemisimpleClasses_eq` (line 787),
  and `numEllipticClasses_eq` (line 844) are all proved lemmas, and the final
  result `card_conjClasses_eq` (line 940) rewrites by all three (plus
  `numScalarClasses_eq`) to conclude `Nat.card (ConjClasses (GL₂)) = q² − 1`.
  The sibling docstring at line 938 already calls the partition
  `card_conjClasses_eq_sum` "Proved fully" and line 936 calls the four counts
  "fully-proved". "deferred" is stale.
- **Suggested reword:** drop "deferred" → "The three per-type counts all follow
  the same recipe:".

### 3. (borderline / low-severity) `EtingofRepresentationTheory/Chapter4/Exercise4_2_3_FieldGeneral.lean:59`

- **Matched phrase:** `not in the statement types until the deferred proofs are
  filled in.` (a `--` comment justifying
  `set_option linter.unusedFintypeInType false`).
- **Contradicting fact:** the file is sorry-free; the header (lines 48–54)
  states the assembly `natCard_irrepClasses_le_conjClasses` "is proved outright"
  from two lemmas "both now sorry-free" (#6126, #6127). There are no remaining
  deferred proofs, so the temporal clause "until the deferred proofs are filled
  in" is stale.
- **Suggested reword (pure-docstring only):** drop the clause — "`[Fintype G]`
  is used at proof time (cocenter dimension, finiteness of the class count) but
  not in the statement types." The core justification for the linter option is
  preserved.
- **Note:** classified borderline because this is a linter-justification code
  comment, not a mathematical completeness claim, and because whether the
  `set_option` is now vestigial is a separate (code, not docstring) question the
  applier may want to check. If in doubt, apply only the clause deletion.

---

## LEGITIMATE (held harmless)

All entries below are honest statements — "(not yet) in Mathlib" coverage
notes, genuine scope deferrals to content absent from the file, correct
mathematical non-existence, the #7084 sorry, or forward references inside
completed proofs. `file:line — matched phrase — why legitimate`.

**Chapter 2**
- `Problem2_3_18.lean:35` — "not in Mathlib …" — Mathlib coverage note.
- `Definition2_3_8.lean:18` — "not in Mathlib as of v4.28" — coverage note.
- `Problem2_11_3.lean:19` — parts (d)–(f) "deferred to a dedicated follow-up
  item" — genuine scope deferral; only (a),(b),(c),(g) are in the file.
- `Proposition2_7_1_ii.lean:40` — "q-Weyl algebra / quantum torus is not in
  Mathlib" — coverage note.
- `Problem2_13_1.lean:19` — parts (a),(c) "deferred to a dedicated follow-up
  item" — genuine deferral; only (b) formalized.
- `Problem2_5_2.lean:23` — part (c) "deferred to a dedicated follow-up item" —
  genuine deferral; (a),(b) proved, (c) absent.
- `Problem2_15_1_complete_reducibility.lean:16` — "general Weyl theorem …
  not in Mathlib" — coverage note.
- `Theorem2_1_2.lean:22` — "Gabriel's theorem is not in Mathlib" — coverage.
- `Problem2_16_4.lean:23` — full parametrization "requires highest-weight-module
  infrastructure and is deferred. Here we record the sharp dimension bound" —
  genuine deferral; the parametrization is genuinely absent, the bound is what
  the file proves.
- `Problem2_16_3.lean:35` — "Statement-only (proofs deferred)." — the **#7084**
  file, genuine open sorry `finrank_g_three`; held harmless (claimed by #7084).
- `Problem2_16_3.lean:508` — "deferred (see the tracking …)" — same #7084 file.
- `Theorem2_1_1.lean:30` — "sl(2)-representations and complete reducibility are
  not in Mathlib" — coverage note.
- `Sl2Irrep.lean:35` — "for semisimple Lie algebras … not in Mathlib" — coverage.

**Chapter 4**
- `Definition4_10_1.lean:14` — "Not in Mathlib. Needs a custom definition" —
  coverage note.
- `Example4_8_1.lean:52` and `Example4_8_1/Q8.lean:52` — "Character tables …
  not in Mathlib; built here from scratch" — coverage notes.
- `Exercise4_2_3_SplitSimples.lean:14` — algebra isomorphism "which does not
  exist modularly (the radical is nonzero)" — correct mathematical statement
  motivating the surjective-hom design.
- `Example4_9_1.lean:78` — "Tensor-product decomposition multiplicities …
  not in Mathlib" — coverage note.
- `Remark4_6_4.lean:27` — "Indecomposability is not in Mathlib; we record it" —
  coverage note.
- `Theorem4_5_4.lean:31` — "Column (second) orthogonality, not in Mathlib as of
  v4.28" — coverage note.
- `Theorem4_10_2.lean:20` — "Not in Mathlib. … Frobenius's original
  factorization" — coverage note.
- `Exercise4_2_3_SplitSimples.lean` (see above); `Exercise4_2_3_FieldGeneral.lean:59`
  is the borderline DEFECT above.

**Chapter 5**
- `Corollary5_19_2.lean:13` — "Requires Schur-Weyl duality … not yet in Mathlib".
- `Example5_1_3.lean:580` — "the even-dimensional A₅ case is blocked on; this
  lemma is the verified endgame they feed into" — honest downstream-assembly
  note: `A5_frobeniusSchur_all_pos` is deliberately stated with the three
  numeric inputs as hypotheses (the full A₅ assembly is genuinely not completed
  in this file), so "blocked on … foundations" describes real unfinished
  downstream work, not an unproved decl. (Borderline wording, but not a DEFECT.)
- `Exercise5_3_3.lean:167` — "piece that is not in Mathlib; it is now supplied by
  the reverse indicator bridge" — coverage note (positive: supplied here).
- `Definition5_1_4.lean:15` — "Frobenius-Schur indicator is not in Mathlib" —
  coverage note.
- `PolynomialRepEmbedding.lean:492` — "the derivation is deferred to a follow-up"
  — genuine deferral: `hP_mul` is taken as an explicit hypothesis; its
  derivation from `CharZero` is genuinely absent from the file.
- `Proposition5_22_2.lean:34` — "Not yet in Mathlib." — coverage note.
- `Proposition5_19_1.lean:13` — "tensor power and Schur-Weyl duality
  infrastructure not yet in Mathlib" — coverage note.
- `Proposition5_21_1.lean:13` — "Schur polynomials are not yet in Mathlib" —
  coverage note.
- `Theorem5_12_2_Irreducible.lean:16` — "the Specht module construction and its
  irreducibility are not yet formalized" — under the `## Mathlib correspondence`
  header; a Mathlib-coverage note (the file itself constructs `SpechtModule` and
  proves irreducibility here).
- `Remark5_2_8.lean:38` — "… that is rational and lies strictly between 0 and 1
  does not exist" — correct mathematical statement about the indicator value.
- `Lemma5_18_3.lean:21` — "algebra structure on Sⁿ A is not yet in Mathlib
  (listed as TODO)" — coverage note.
- `Problem5_11_1.lean:100` — "character over ⊞, which is not in Mathlib; we
  establish it here" — coverage note.
- `SchurModuleSimple.lean:184` — "nonvanishing is deferred to the reconciliation
  α = α' below" — forward reference **within a completed proof** (the
  nonvanishing is established later in the same sorry-free proof), not
  incomplete work.
- `Theorem5_25_2.lean:16` — "principal series construction is not in Mathlib; we
  define" — coverage note.
- `Theorem5_18_1.lean:19` — "itself is not yet formalized in Mathlib" — coverage.
- `Theorem5_27_1.lean:23` — "orbit method classification is not yet in Mathlib" —
  coverage note.

**Chapter 6**
- `Definition6_5_1.lean:12` — "dimension vector … is not in Mathlib" — coverage.
- `Proposition6_6_7.lean:20`, `Corollary6_8_4.lean:31`,
  `ReflectionFunctorInfrastructure.lean:22`, `Proposition6_6_6.lean:14`,
  `Proposition6_6_6_source.lean:14`, `Theorem6_8_1.lean:28` — "Not in Mathlib." —
  coverage notes.
- `Definition6_6_3.lean:20`, `Definition6_6_4.lean:21` — "BGP reflection functors
  are not in Mathlib" — coverage notes.
- `Theorem6_5_2.lean:23`, `Problem6_1_5_theorem.lean:22` — "Gabriel's theorem is
  NOT in Mathlib" — coverage notes.
- `Lemma6_4_6.lean:17` — "combinatorial/algebraic lemma about Dynkin diagrams not
  in Mathlib" — coverage note.
- `Problem6_9_1.lean:51` — "Not in Mathlib. … relies on the Jordan normal form
  theorem" — coverage note.
- `Problem6_9_1.lean:525` — "requires the structure theorem for modules over
  k[X]/(Xᴺ), not yet in Mathlib" — background note on the private lemma
  `ker_sum_ge_one`; the lemma is proved by a direct route, and the sentence
  describes the general Mathlib-coverage context, not an unproved decl.

**Chapter 7**
- `Example7_2_2.lean:227` — Schur functors "genuinely advanced and is deferred;
  the tensor-power functor above is the first ingredient" — genuine scope
  deferral (the Schur-functor endofunctor is not assembled here).
- `Example7_2_2.lean:241` — BGP-functor packaging "deferred pending a
  CategoryTheory-level quiver-representation category" — genuine scope deferral
  (object-level construction exists; the `Functor` packaging is genuinely
  absent).

**Chapter 8**
- `Problem8_2_7.lean:133` — "These are not in Mathlib, so we prove them here" —
  coverage note (positive).
- `ExtAbelianComparison.lean:55` — "Mathlib records this as a TODO in
  Algebra/Homology/Linear" — accurate statement about **Mathlib's** TODO.

**Chapter 9**
- `Definition9_2_2.lean:15` — "Projective covers are not yet formalized in
  Mathlib" — coverage note.
- `Definition9_7_1.lean:38` — "Eilenberg-Watts is not yet formalized" — coverage.
- `Example9_4_4.lean:28` — "Hilbert syzygy theorem is not yet in Mathlib" —
  coverage note.
- `Introduction_9_7.lean:43` — "categories is not in Mathlib; it is built up in
  Chapter9/KrullSchmidt/" — coverage note (positive).
- `Problem9_5_3_S3Char2.lean:8` — "This file discharges part (iii) … (deferred
  by Problem9_5_3.lean)" — positive: this file **discharges** the deferral.
  Verified against `Problem9_5_3.lean:27-28`, which correctly says (iii) "is
  discharged in Problem9_5_3_S3Char2.lean". No stale claim.
- `Problem9_3_2.lean:35` — "which until now was only a TODO comment in
  Chapter9/Example9_5_2.lean" — historical narration; verified
  `Example9_5_2.lean:38` now reads "Part (iii) … is now formalized" (the TODO is
  gone). Accurate.

**Chapter 9 — already tracked by #7093**
- `KrullSchmidt/Length.lean:542` — "remains to be discharged" — DEFECT
  (`clength_le_add` is proved at line 501 and consumed at 549). **Already queued
  in #7093; not re-filed here.**

---

## Recommended follow-up

One `feature` PR, comment-only edits (no code, no CI-behaviour change), applying:

1. `PolynomialRepEmbedding.lean:1114` reword (DEFECT 1 above),
2. `GL2ConjugacyClassCount.lean:72` reword (DEFECT 2 above),
3. optionally `Exercise4_2_3_FieldGeneral.lean:59` clause deletion (borderline),

alongside — or after — the #7093 trio. Once those land, the tree-wide
stale-completeness-prose class is **converged**: only legitimate coverage notes,
genuine scope deferrals, and the lone #7084 sorry remain.

## Reproduction

```bash
# matched set (61 files / 65 lines)
grep -rniE 'not yet formalized|remains to be|remains open|to be discharged|## blocked|is blocked|deferred|\bTODO\b|not (yet )?(available|in) mathlib|does not (yet )?exist' \
  EtingofRepresentationTheory/ --include=*.lean

# authoritative sorry count (comment-stripped depth counter) -> 1 (Problem2_16_3)
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  n=$(awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b')
  [ "$n" -gt 0 ] && echo "$n $f"
done
```

# Sorry Landscape Analysis — post-23-merge refresh

Generated 2026-07-17 22:16 UTC by summarize session (issue #6917, branch
`agent/373b5043`) against `origin/main` at HEAD `f3721e82`. **Supersedes
`progress/2026-07-16T21-47-07Z-sorry-landscape.md`** (issue #6871, HEAD
`40317cf7`), which reported **9 genuine sorries in 6 files**; the current count
is **6 in 5 files**. Since that snapshot was generated (2026-07-16 21:47Z),
**23 PRs merged to `main`** (the issue #6917 body counted 13 as of 17:46; 10
more landed while it sat in the queue). The merges concentrated in three active
threads — **Ch6 Problem 6.1.3-g** (affine-Dynkin ⟹ tree case: 12 merges),
**Ch8 Problem 8.2.8-Ext** (Künneth cochain assembly + the `Ext ≃ Extₖ` bridge:
7 merges), and **Ch4 Problem 4.12.8-a-iv** (SO(3) pole classification: 2
merges), plus the Ch9 char-2 k[S₃] residual (#6886) that closed the last Ch9
sorry and a prior summarize doc (#6887). The net count fell 9 → 6, but as in prior windows the frontier
**shifted** rather than simply shrank: whole tree-case sub-lemmas closed in Ch6
and Ch9 went source-sorry-free, while fresh residual layout/bridge sorries
surfaced (the Ch6 arm-layout lemmas, the Ch8 `extAbelianIsoExtₖ` `map_smul'`).
Every current sorry is a spec-first skeleton with its assembly already stated.

## Headline: 6 genuine sorries across 5 files

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **6 genuine proof-gap `sorry`
tactics in 5 files** — down from 9/6. There are **no `axiom` declarations and
no `admit`s** (every `axiom`/`admit` string hit is English prose inside
docstrings). Two files record book-unproved statements via **`proof_wanted`**
rather than `sorry` — **2** `proof_wanted` declarations, unchanged:
`Chapter2/Remark2_9_3.lean:47` (`ado`, Ado's theorem) and
`Chapter5/Remark5_23_3.lean:209` (`sl_finiteDimensional_completely_reducible`).
These `proof_wanted` gaps are genuine unproved surface the comment-stripped
counter does **not** see, so "6 sorries" slightly understates the unproved
frontier.

Reproduce the headline count (comment-stripping `awk` depth-counter, then
whole-word `sorry` on surviving code) against a clean `origin/main` checkout:
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 6 across 5 files at HEAD f3721e82
```

Per-file genuine-sorry tally (comment-stripped), with the enclosing declaration
and tracking issue/PR:
```
1  Chapter2/Problem2_16_3.lean               :1051  finrank_g_three = 6                       (#6340, claimed 6d)
1  Chapter4/Problem4_12_8.lean               :1274  so3_classification_aux (5-way assembly)   (#6836 arc; residuals #6924, #6864)
2  Chapter6/Problem6_1_3_continued_tildeE.lean
   :2749  affine_two_branch_deleted_isD (Dₖ reattach crux)   (#6922, blocked+replan)
   :3456  affine_one_branch_arm_layout  (three-arm layout)   (#6919, has-pr → PR #6937)
1  Chapter8/ExtAbelianComparison.lean        :84    extAbelianIsoExtₖ `map_smul'` obligation  (#6920 replan → #6935; PR #6936 reduces it)
1  Chapter8/Problem8_2_8.lean                :254   Problem_8_2_8_ext (Ext Künneth assembly)  (#6898, unclaimed)
```

Per-chapter genuine sorries (from the Lean source, authoritative): Ch2 = 1,
Ch4 = 1, Ch6 = 2, Ch8 = 2; Ch0/1/3/5/7/9 = 0. **Chapter 9 is now
source-sorry-free**: the last Ch9 sorry, `simple_iff_triv_or_std`
(`Problem9_5_3_S3Char2.lean`), landed via #6886 (merged 2026-07-16 23:39Z).

### Honesty note on the Ch8 `ExtAbelianComparison.lean:84` sorry

This sorry sits **inside** `noncomputable def extAbelianIsoExtₖ`, but it is a
**proof obligation, not a data sorry**: the underlying data (the additive
equivalence `extAbelianAddEquivExtₖ`, supplied via `__ :=`) is real and
sorry-free; only the `map_smul'` field (`k`-linearity of the four-step
comparison chain) is deferred. This is a permitted in-definition obligation
(the mathematical object exists), tracked as the residual crux `key123` in
#6935. PR #6936 (open) reduces `map_smul'` to `key123` structurally.

### items.json status distribution (592 items)

**No status corrections were applied this window** (see the audit note below).

| Status | Count |
|--------|------:|
| `sorry_free` | 554 |
| `statement_formalized` | 11 |
| `proved` | 8 |
| `accepted` | 6 |
| `formalized` | 4 |
| `proof_complete` | 3 |
| `partially_formalized` | 2 |
| `partially_proved` | 2 |
| `sorry` | 1 |
| `non_formalizable` | 1 |
| **total** | **592** |

Reproduce:
```bash
python3 -c "import json,collections; d=json.load(open('progress/items.json')); \
print(collections.Counter(it.get('status') for it in d))"
```

**Status audit this window (deliverable 2): 0 corrections.** Every one of the
5 sorry-bearing source files maps to an item already held `statement_formalized`
(Ch2 2.16.3, Ch4 4.12.8, Ch6 6.1.3_continued_tildeE, Ch8 8.2.8 — the
`ExtAbelianComparison` sorry is part of the 8.2.8 arc), so no `sorry_free` item
has a sorried source (no regression to fix), and no item is held
`statement_formalized` *solely* because of a live sorry that has since cleared
(the 2.16.4 / 5.24.2 pattern the prior session corrected does not recur).

**Blob-audit candidates flagged, not reclassified.** Six `statement_formalized`
items now have **fully sorry-free source** yet are held for reasons other than a
sorry, so the sorry counter alone does not license reclassifying them —
following the prior session's guidance to apply a blob check rather than trust
the counter:

- `Chapter9/Problem9.5.3` — source now fully sorry-free (all five char-2 k[S₃]
  classification results plus the block bijection engine proved). Its
  `coverage_note` still lists `algebra_decomposition` and `blocks_equiv…` as
  "remaining sorry", which is **stale prose**: the comment-stripped counter
  reports 0 for all of Ch9. A blob audit should decide whether the item's book
  deliverable (parts i–iii) is now fully met → `sorry_free`.
- `Chapter9/Problem9.4.6` — likewise source-sorry-free; its `coverage_note`
  lists `hasHomologicalDimensionLE_pathAlgebra_one` and
  `homologicalDimension_…_eq_one` as sorry, again stale relative to the counter.
  Was a deliberate hold (9.4.6(ii)); needs a blob check.
- `Chapter6/Problem6.1.3_continued_E7_E8` — carried over from the prior doc
  (sorry-free source, fragment of the still-incomplete 6.1.3-g arc).
- `Chapter2/Problem2.16.5`, `Chapter4/Problem4.12.11`, `Chapter6/Problem6.1.6` —
  the remaining 06:14 deliberate holds (unstated classification parts /
  crux-as-hypothesis / Prop-def-only). Unchanged; source sorry-free.

Future summarize sessions should resolve the Ch9 pair (9.5.3, 9.4.6) with a
proper blob audit — their coverage notes are the most out-of-date and both look
close to `sorry_free`.

### Per-chapter picture

Columns: total items, `sorry_free`, `statement_formalized`, other statuses, and
**genuine sorries in the Lean source** (comment-stripped). The item counts use a
heuristic chapter binning (first `Chapter N` marker in the `id`; id-less items
bin to ch0) and differ by a handful from prior docs (notably the ch0/ch5 split).
The **status-distribution totals and the genuine-sorry column are
authoritative**; the per-chapter item split is indicative.

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/back) | 15 | 6 | 1 | 8 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 117 | 111 | 2 | 4 | 1 |
| 3 | 58 | 58 | 0 | 0 | 0 |
| 4 | 60 | 54 | 2 | 4 | 1 |
| 5 | 157 | 150 | 0 | 7 | 0 |
| 6 | 64 | 59 | 3 | 2 | 2 |
| 7 | 59 | 59 | 0 | 0 | 0 |
| 8 | 24 | 22 | 1 | 1 | 2 |
| 9 | 35 | 32 | 2 | 1 | 0 |
| **total** | **592** | **554** | **11** | **27** | **6** |

## What changed since 2026-07-16 21:47 (the 23 merges that landed)

By chapter, net source-sorry movement:

- **Chapter 6 — 4 → 2 (tree case largely assembled; layout residuals surfaced).**
  Twelve merges drove the affine-Dynkin ⟹ direction. The four prior tree-case
  sorries (`affine_tree_branch_count` #6890, `affine_tree_two_branch_iso`,
  `affine_tree_one_branch_iso`, `affine_dynkin_classification`) all **closed**:
  the degenerate arm-length analysis (#6895), the `affine_arm_length_solutions`
  equality Diophantine (#6908), the reciprocal core of
  `affine_tree_one_arm_reciprocal` (#6914), the ⟹ direction of
  `affine_dynkin_classification` (#6916), `affine_two_fork_reindex` (#6912),
  `affine_arm_walk` per-arm engine (#6929), `affine_tree_two_branch_iso` → D̃ₙ
  (#6923), `affine_one_branch_three_arms` component partition (#6932), and
  `affine_tree_one_branch_iso` → Ẽ₆/Ẽ₇/Ẽ₈ (#6930). Two **new residual layout
  sorries** surfaced in `_tildeE.lean`: `affine_two_branch_deleted_isD` (the
  finite-Dₖ reattach crux, #6922 — **blocked+replan**) and
  `affine_one_branch_arm_layout` (the three-arm sort/reindex, #6919 — **open
  PR #6937**). A related arithmetic core, `affine_two_branch_pinch`, landed on
  a branch (open PR #6934, feeds the two-branch fork discriminator #6933).
- **Chapter 8 — 2 → 2 (Künneth machinery advanced; Ext bridge surfaced).**
  Seven merges. `Problem_8_2_8_extₖ`, the k-linear Künneth core, landed and its
  residual was decomposed into #6897/#6898 (#6899); `fullSummandIso` naturality
  (#6903), the degreewise sign-twist core (#6905) and assembly (#6915) of
  `homComplexHomologyAddEquivₖ`, `rearrangeHomComplexXIso_inv_comm` (#6909,
  which **cleared** the old `RearrangeHomComplex.lean` sorry), the
  `extAbelianAddEquivExtₖ` + `extAbelianIsoExtₖ` shell (#6921), and the finite
  bar-resolution `Module.Finite` instances (#6931, deliverable 1 of #6898). The
  net count held at 2 because a **new** sorry surfaced — the
  `extAbelianIsoExtₖ` `map_smul'` obligation (`ExtAbelianComparison.lean:84`,
  from the #6921 shell) — while `Problem_8_2_8_ext` (`Problem8_2_8.lean:254`)
  still awaits final assembly (#6898).
- **Chapter 9 — 1 → 0 (source-sorry-free).** `simple_iff_triv_or_std`, the
  exactly-two-simples classification of char-2 k[S₃]-modules (#6886), cleared
  the last Ch9 sorry. Ch9 source is now entirely sorry-free (see the blob-audit
  note above — several Ch9 `coverage_note`s are now stale).
- **Chapter 4 — 1 → 1 (SO(3) frontier moved deeper).** The `so3_cyclic_of_poleData`
  cyclic disjunct landed (#6927) and milestone (ii) `isCyclic_stabilizer_pole`
  (#6892). The single sorry `so3_classification_aux` (`Problem4_12_8.lean:1274`)
  remains — its residual is now the **dihedral** disjunct (#6924, unclaimed) and
  the **polyhedral A₄/S₄/A₅ + final assembly** (#6864, unclaimed, *large*).
- **Chapter 2 — 1 → 1.** `finrank_g_three = 6` (the G₂ positive-nilpotent
  finrank, `Problem2_16_3.lean:1051`, #6340) unchanged.
- **Chapters 1, 3, 5, 7 — unchanged, source-sorry-free.**

## In-flight chains (open issues / PRs as of this snapshot)

The frontier is **6 sorries across 4 active problems**, all tracked:

- **Ch6 Problem 6.1.3-g affine ⟹ (tree case)** — two residual **layout** sorries
  in `_tildeE.lean`, both being worked. `affine_one_branch_arm_layout` (#6919)
  has **open PR #6937** (sort three arm lengths + build σ + `armAdjIdx` iff).
  `affine_two_branch_deleted_isD` (#6922) is **blocked+replan** — the finite-Dₖ
  reattach crux, the deepest remaining piece of the two-branch → D̃ₙ line; also
  in flight is `affine_two_branch_pinch` (open **PR #6934**), its arithmetic
  core, which feeds the fork discriminator #6933. Do not attempt the top-level
  6.1.3-g assembly before these land.
- **Ch8 Problem 8.2.8-Ext** — two sorries forming the Ext-side capstone.
  `extAbelianIsoExtₖ` `map_smul'` (`ExtAbelianComparison.lean:84`) is the
  bridge's k-linearity; **PR #6936** reduces it to the crux `key123` (#6935,
  unclaimed — genuinely hard, needs `CohomologyClass`/`homologyAddEquiv`
  target-naturality infra Mathlib does not package). The final
  `Problem_8_2_8_ext` assembly (`Problem8_2_8.lean:254`, #6898, unclaimed)
  consumes both the bridge (#6921, landed as real data with the single residual
  `map_smul'`) and `Problem_8_2_8_extₖ`; deliverable 1 (fg resolutions) already
  landed (#6931).
- **Ch4 Problem 4.12.8-a-iv `so3_classification_aux`** — the #6836 arc. Two
  unclaimed residuals feed the assembly sorry (`Problem4_12_8.lean:1274`):
  **#6924** (dihedral disjunct, geometric ρ/s extraction from {2,2,k} pole data,
  *hard geometry*) and **#6864** (polyhedral A₄/S₄/A₅ realizations + final
  five-way disjunction, flagged *large*, expects decomposition). The cyclic
  disjunct and the algebraic recognition cores already merged.
- **Ch2 2.16.3(a) `finrank_g_three = 6`** — **#6340 (claimed 6 days)**. Verify
  liveness / consider release if stale.

## Ranked shortlist of tractable next targets

"Single sorry" ≠ cheap. Honest tractability read:

**Tier 0 — housekeeping, not a proof:**

1. **Ch9 blob audit (9.5.3 and 9.4.6).** No Lean proving needed — both items are
   `statement_formalized` with fully sorry-free source and stale `coverage_note`s.
   A summarize/planner session should read `blobs/Chapter9/Problem9.5.3.md` and
   `blobs/Chapter9/Problem9.4.6.md`, confirm the book deliverables are met (not
   crux-as-hypothesis), and reclassify to `sorry_free` / `proved` if so. Highest
   value-per-effort: it corrects the project's completion picture.

**Tier 1 — narrow, concrete, high-confidence (but currently in flight):**

2. **Ch6 `affine_one_branch_arm_layout`** (`_tildeE.lean:3456`, #6919). Has
   **open PR #6937** — do not re-claim unless it stalls. A structural
   arm-sorting/reindex layout, the last piece unblocking `affine_tree_one_branch_iso`
   (already assembled around it).
3. **Ch2 `finrank_g_three = 6`** (`Problem2_16_3.lean:1051`, #6340, *claimed 6
   days*). A concrete finrank computation for the type-G₂ positive part;
   surrounding 2.16.3(b) machinery is fully proved in the same file. The
   long-held claim is the concern — **verify liveness / release if stale**.

**Tier 2 — substantial but concrete book route, currently unclaimed:**

4. **Ch4 `so3_dihedral_of_poleData`** (#6924). Extract the rotation angle and the
   order-2 flip from the {2,2,k} pole data and feed the merged dihedral
   recognition core `mulEquiv_dihedralGroup_of_conj_inv`. Geometry-heavy but the
   algebraic core exists and the cyclic sibling (#6927) is a template.
5. **Ch6 `affine_two_branch_deleted_isD`** (#6922, *blocked+replan*). The
   finite-Dₖ reattach crux; needs the affine-degeneracy argument ruling out
   E-types plus localizing the Dₖ reattach point. Deep graph theory — check the
   `blocked` dependency and #6934/#6933 status before claiming.

**Tier 3 — deep assembly / large classification:**

6. **Ch8 `Problem_8_2_8_ext`** (#6898). The four-step Ext Künneth assembly; fg
   resolutions (#6931) landed and the bridge (#6921) is real data. Best claimed
   *after* the `map_smul'`/`key123` residual (#6935 / PR #6936) settles, so the
   bridge is fully k-linear.
7. **Ch8 `key123` / `extAbelianIsoExtₖ` `map_smul'`** (#6935). Genuinely hard:
   needs target-naturality of `CohomologyClass`/`homologyAddEquiv` under a
   morphism `θ = r • 𝟙 N`, infrastructure Mathlib does not package. Consider the
   split the issue proposes (repo-local `homComplexHomologyAddEquivₖ` naturality
   vs the two Mathlib-side naturality steps).
8. **Ch4 `so3_classification_aux` polyhedral + assembly** (#6864, *large*). The
   A₄/S₄/A₅ realizations and final five-way disjunction; expects careful
   per-family decomposition (tetrahedral / octahedral / icosahedral).

The Ch6 top-level `affine_dynkin_classification` ⟹ direction is now **landed**
(#6916); the remaining 6.1.3-g work is the two layout residuals above plus the
overall problem's backward direction / assembly. The Ch8 Ext capstone (#6898)
and the Ch4 polyhedral classification (#6864) remain the deepest live arcs.

## Method notes

- Counts are comment-stripped genuine sorries against `origin/main` HEAD
  `f3721e82`; the reproducer command above is authoritative. A cross-check with
  a sorry-*tactic* pattern grep (`:= sorry`, `exact sorry`, standalone `sorry`)
  agreed at 6 (two extra raw hits were `"sorry-free"` prose in comments).
- `proof_wanted` gaps (2 declarations: `Remark2_9_3.lean` `ado`,
  `Remark5_23_3.lean` `sl_finiteDimensional_completely_reducible`) are *not*
  counted in the 6 but are real unproved surface — noted for honesty. No
  in-definition **data** obligations remain; the one in-`def` sorry
  (`extAbelianIsoExtₖ` `map_smul'`) is a proof obligation over real data.
- **Status audit (deliverable 2): 0 corrections.** No `sorry_free` item has a
  sorried source (no regression), and no `statement_formalized` item is held
  solely for a now-cleared sorry. Six sorry-free-source `statement_formalized`
  items are **flagged for a blob audit** (Ch9 9.5.3 & 9.4.6 most urgently — stale
  coverage notes; plus the carried-over E7_E8 fragment and the three 06:14
  deliberate holds 2.16.5 / 4.12.11 / 6.1.6). The counter alone does not license
  reclassifying deliberate holds; a blob check must confirm the book deliverable.
- The per-chapter *item* split uses a heuristic marker-based binning and may
  differ by a few from prior docs; the status-distribution totals (592, and the
  554/11/8/… breakdown) and the source sorry counts are exact.
- Merged-PR list obtained via
  `gh pr list --state merged --json number,title,mergedAt` filtered to
  `mergedAt > 2026-07-16T21:47:07Z` (23 results).

# Sorry Landscape Analysis — post-24-merge refresh

Generated 2026-07-16 21:47 UTC by summarize session (issue #6871, branch
`agent/70007d78`) against `origin/main` at HEAD `40317cf7`. **Supersedes
`progress/2026-07-16T11-17-43Z-sorry-landscape.md`** (issue #6786, HEAD
`dbc9994f`), which reported **6 genuine sorries in 6 files**; the current count
is **9 in 6 files**. Since that snapshot closed (2026-07-16 13:05:53Z), **24 PRs
merged to `main`** (the issue #6871 body counted 16 at the time it was written
at 20:09; 8 more landed while it sat in the queue). The merges concentrated in
five threads — Ch4 Problem 4.12.8 finite-SO(3)-subgroup pole-counting, Ch6
Problem 6.1.3-g affine-Dynkin tree case, Ch8 Problem 8.2.8-Ext Künneth,
Ch9 Problem 9.5.3-iii k[S₃] char-2 block structure, and Ch5 FFT/GL — and the
frontier **shifted** rather than shrank: two whole problems closed out
(2.16.4 upper bound, 5.24.2 FFT core) while three fresh single-file streams
opened their skeletons with sorries (Ch4 `so3_classification_aux`, the Ch6
tree-case sub-lemmas, the Ch8 `RearrangeHomComplex` cochain machinery, Ch9
`simple_iff_triv_or_std`). Net sorry count went 6 → 9, but this reflects newly
*surfaced* sub-structure, not regression: every new sorry is a spec-first
skeleton with its assembly already stated.

## Headline: 9 genuine sorries across 6 files

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **9 genuine proof-gap `sorry`
tactics in 6 files** — up from 6/6. There are **no `axiom` declarations and no
`admit`s** (every `axiom`/`admit` string hit is English prose inside
docstrings). Two files record book-unproved statements via **`proof_wanted`**
rather than `sorry` — **2** `proof_wanted` declarations, down from 3:
`Chapter2/Remark2_9_3.lean:47` (`ado`, Ado's theorem) and
`Chapter5/Remark5_23_3.lean:209` (`sl_finiteDimensional_completely_reducible`).
The third prior `proof_wanted` (`algIrrepGL_finrank_constShift`,
`Remark5_23_3.lean`) was **converted to a real theorem** by #6857 this window.
These `proof_wanted` gaps are genuine unproved surface the comment-stripped
counter does **not** see, so "9 sorries" slightly understates the unproved
frontier.

Reproduce the headline count (comment-stripping `awk` depth-counter, then
whole-word `sorry` on surviving code) against a clean `origin/main` checkout:
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 9 across 6 files at HEAD 40317cf7
```

Per-file genuine-sorry tally (comment-stripped), with the enclosing declaration
and tracking issue/PR:
```
1  Chapter2/Problem2_16_3.lean          :1051  finrank_g_three = 6                    (#6340, claimed 5d)
1  Chapter4/Problem4_12_8.lean          :1195  so3_classification_aux (assembly)      (#6836 arc; feeds #6864/#6877)
4  Chapter6/Problem6_1_3_continued_tildeE.lean
   :2101  affine_tree_branch_count       (#6880, claimed)
   :2118  affine_tree_two_branch_iso     (#6881, unclaimed)
   :2134  affine_tree_one_branch_iso     (#6882, unclaimed)
   :2163  affine_dynkin_classification (⟹ assembly, dispatches to the 3 above)  (#6793 / #6785)
1  Chapter8/Problem8_2_8.lean           :177   Problem_8_2_8_ext (Ext Künneth assembly)  (#6818, waits on rearrange chain)
1  Chapter8/RearrangeHomComplex.lean    :89    rearrangeHomComplexXIso_inv_comm       (#6884, claimed)
1  Chapter9/Problem9_5_3_S3Char2.lean   :283   simple_iff_triv_or_std                 (#6859, open PR #6886)
```

Per-chapter genuine sorries (from the Lean source, authoritative): Ch2 = 1,
Ch4 = 1, Ch6 = 4, Ch8 = 2, Ch9 = 1; Ch0/1/3/5/7 = 0. Two files that carried
the frontier's only sorry in their chapter last window are now **sorry-free**:
`Chapter2/Problem2_16_4.lean` (the `finrank_irreducible_le_char` upper bound
landed, closing 2.16.4 alongside the merged `exists_irreducible_dim_char`) and
`Chapter5/Problem5_24_2_Bridge.lean` (`reynolds_injective`, the FFT reductivity
heart, landed via #6839). Both residual raw-`grep` `sorry` hits in those files
(`Problem2_16_4.lean:30`, `Problem5_24_2_Bridge.lean:41`) are prose inside
comments, confirmed by the comment-stripped counter reporting 0 for each.

### items.json status distribution (592 items)

After **2 status corrections applied this window** (see below):

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

**Status corrections made this window (2, deliverable 2):** `Chapter2/Problem2.16.4`
and `Chapter5/Problem5.24.2` were reclassified `statement_formalized → sorry_free`.
Both were held `statement_formalized` in the prior landscape **solely because
their source carried a live sorry** (the 11:17 doc explicitly listed 2.16.4 and
5.24.2 among "the 6 sorry-carrying files [that] maps to a `statement_formalized`
item"). Those sorries cleared this window (2.16.4 via the upper-bound proof;
5.24.2 via `reynolds_injective`, all four `Problem5_24_2*.lean` files now
sorry-free), and neither item is in the prior audit's deliberate-hold list, so
the label was stale. Net: `statement_formalized` 13 → 11, `sorry_free` 552 → 554.
(The 5.24.2 item's free-text `coverage_note` still ends "Sorry proof." — left
unedited to keep the diff minimal; the `status` field is authoritative.)

**Not reclassified, flagged for a future blob audit:** `Chapter6/Problem6.1.3_continued_E7_E8`
is `statement_formalized` with fully sorry-free source. It is a sub-file (Cartan
determinants, tree/degree structural lemmas) of the **still-incomplete** 6.1.3-g
classification whose ⟹ direction is the four live sorries in the companion
`_tildeE` file. Holding it `statement_formalized` until the whole 6.1.3-g arc
closes is defensible; a proper blob audit should decide whether the E7_E8 item
represents a self-standing deliverable or a fragment of 6.1.3. The five
deliberate holds from the 06:14 audit (6.1.6(d), 9.4.6(ii), 9.5.3(iii), 2.16.5,
4.12.11(b) — crux-as-hypothesis / Prop-def-only / unstated parts) are unchanged.

### Per-chapter picture

Columns: total items, `sorry_free`, `statement_formalized`, other statuses, and
**genuine sorries in the Lean source** (comment-stripped). The item counts use a
heuristic chapter binning (items assigned by the first `Chapter N` marker in
their `id`); it differs by a handful from prior docs' binning (notably it splits
the ch0 front/back-matter bucket differently). The **status-distribution totals
and the genuine-sorry column are authoritative**; the per-chapter item split is
indicative.

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/back) | 13 | 6 | 0 | 7 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 117 | 111 | 2 | 4 | 1 |
| 3 | 58 | 58 | 0 | 0 | 0 |
| 4 | 60 | 54 | 2 | 4 | 1 |
| 5 | 159 | 150 | 1 | 8 | 0 |
| 6 | 64 | 59 | 3 | 2 | 4 |
| 7 | 59 | 59 | 0 | 0 | 0 |
| 8 | 24 | 22 | 1 | 1 | 2 |
| 9 | 35 | 32 | 2 | 1 | 1 |
| **total** | **592** | **554** | **11** | **27** | **9** |

## What changed since 2026-07-16 11:17 (the 24 merges that landed)

By thread:

- **Chapter 4 — 1 → 1 (frontier moved deeper).** A **newly-opened
  Problem 4.12.8 finite-SO(3)-subgroup pole-counting classification arc**. The
  old single sorry `so3_finite_subgroup_classification` is now **sorry-free** —
  it delegates to a new `so3_classification_aux` which carries the sorry. Landed:
  scaffold (#6837), `exists_fixed_vector` rotation axis (#6840),
  `pole_order_diophantine` with corrected `{2,2,k}` dihedral case (#6846),
  `isCyclic_of_common_fixed_vector` (#6850), the SO(3) unit-sphere `MulAction` +
  pole set foundation (#6870), the Burnside pole-counting reduction
  `2(1-1/n)=∑(1-1/mᵢ)` (#6875), and the dihedral recognition algebraic core
  `mulEquiv_dihedralGroup_of_conj_inv` (#6878). Residual 1: the full
  `so3_classification_aux` disjunction (cyclic / dihedral / A₄ / S₄ / A₅).
- **Chapter 6 — 1 → 4 (tree case decomposed and skeletoned).** The
  Problem 6.1.3-g affine-Dynkin **tree case** was scaffolded. Landed:
  `affine_vertexDegree_le_four` (#6856), minimality of proper induced subgraphs
  (#6806), the 2-regular ⟹ Ãₙ combinatorial core (#6860) + degree-2 reduction
  assembly (#6872), the degree-4 dichotomy → D̃₄ or degrees ≤ 3 (#6866), and the
  **sorry-free branch-count dispatch skeleton** (#6883) that reduced the tree ⟹
  direction to three sub-lemmas. Residual 4: `affine_tree_branch_count` (#6880),
  `affine_tree_two_branch_iso` → D̃ₙ (#6881), `affine_tree_one_branch_iso` →
  Ẽ₆/Ẽ₇/Ẽ₈ (#6882), and the top-level `affine_dynkin_classification` assembly
  that dispatches to them (#6793/#6785).
- **Chapter 8 — 1 → 2 (Ext Künneth machinery surfaced).** The Problem 8.2.8-Ext
  cochain-rearrangement stream. Landed: left-module external-tensor projective
  resolution (#6838), the cohomological bidegree bifunctor natural iso (#6849),
  `summandIso` per-summand Hom bridge (#6869), the degreewise iso
  `Hom(⊕…,N₁⊗N₂) ≅ ⊕ Hom⊗Hom` (#6876), and `rearrangeHomComplex` assembled via
  `isoOfComponents` (#6885). Residual 2: `rearrangeHomComplexXIso_inv_comm`, the
  differential-commutation lemma in the new `RearrangeHomComplex.lean` (#6884,
  claimed), and the final `Problem_8_2_8_ext` assembly (#6818) that consumes it.
- **Chapter 9 — 0 → 1 (k[S₃] char-2 surfaced).** The Problem 9.5.3-iii block
  structure. Landed: `trivMod`/`stdMod` simplicity (#6858),
  `not_areLinked_triv_std` + `block_card_eq_two` via the (123)+(132) central
  idempotent (#6874), and `algebra_decomposition` k[S₃] ≅ M₂(k) × k[t]/(t²)
  (#6879). Residual 1: `simple_iff_triv_or_std` in
  `Problem9_5_3_S3Char2.lean` (#6859), which has **open PR #6886** in flight.
- **Chapter 2 — 2 → 1.** The 2.16.4 **upper-bound half** landed
  (`finrank_irreducible_le_char`), closing Problem 2.16.4 (reclassified
  `sorry_free`). Residual 1: `finrank_g_three = 6` (`Problem2_16_3.lean:1051`,
  the G₂ positive-nilpotent finrank, #6340).
- **Chapter 5 — 1 → 0.** `reynolds_injective` (the FFT reductivity heart, #6839)
  cleared the last sorry in `Problem5_24_2_Bridge.lean`, closing Problem 5.24.2
  (reclassified `sorry_free`); plus `algIrrepGL_finrank_constShift` converted
  from `proof_wanted` to theorem (#6857). Ch5 is now source-sorry-free.
- **Chapters 1, 3, 7 — unchanged, source-sorry-free.**

## In-flight chains (open issues / PRs as of this snapshot)

The frontier is **9 sorries across 5 active problems**, all tracked:

- **Ch4 Problem 4.12.8-a-iv `so3_classification_aux`** — the #6836 arc. The
  assembly sorry (`Problem4_12_8.lean:1195`) waits on two unclaimed sub-issues:
  **#6864** (polyhedral A₄/S₄/A₅ realizations + final assembly, flagged *large*)
  and **#6877** (geometric extraction of dihedral/cyclic generators from pole
  data — enrich `pole_order_data`). The algebraic cores (Burnside reduction,
  dihedral recognition) already merged; the residual is geometry + assembly.
- **Ch6 Problem 6.1.3-g affine ⟹ (tree case)** — four sorries forming one chain
  in `_tildeE.lean`. `affine_tree_branch_count` is **#6880 (claimed)**;
  `affine_tree_two_branch_iso` (→ D̃ₙ) is **#6881 (unclaimed)**;
  `affine_tree_one_branch_iso` (→ Ẽ₆/Ẽ₇/Ẽ₈, via the affine arm-length
  Diophantine) is **#6882 (unclaimed)**; the top-level assembly is #6793/#6785.
  The three sub-lemmas are independent and can be worked in parallel; the
  assembly closes once all three land.
- **Ch8 Problem 8.2.8-Ext** — two sorries. `rearrangeHomComplexXIso_inv_comm`
  (`RearrangeHomComplex.lean:89`) is **#6884 (claimed)** — a narrow
  differential-commutation lemma that the file's comment says "reduces to the
  two #6843 naturality lemmas". The final `Problem_8_2_8_ext` assembly
  (`Problem8_2_8.lean:177`) is **#6818 (unclaimed)** and consumes the completed
  `rearrangeHomComplex`; effectively downstream of #6884.
- **Ch9 Problem 9.5.3-iii `simple_iff_triv_or_std`** — **#6859**, with **open
  PR #6886** (`agent/bb51f4e6`). Being handled; do not re-plan unless the PR
  stalls.
- **Ch2 2.16.3(a) `finrank_g_three = 6`** — **#6340 (claimed 5 days)**. Verify
  liveness / consider release if stale.

## Ranked shortlist of tractable next targets

"Single sorry" ≠ cheap. Honest tractability read:

**Tier 1 — narrow, concrete, high-confidence:**

1. **Ch8 `rearrangeHomComplexXIso_inv_comm`** (`RearrangeHomComplex.lean:89`,
   #6884, *claimed*). The file comment states it reduces to two already-merged
   #6843 naturality lemmas plus biproduct relations — a bounded diagram chase,
   not new mathematics. If the claim goes stale, this is the single most
   tractable unblock, and it directly frees the Ch8 Ext capstone #6818.
2. **Ch2 2.16.3(a) `finrank_g_three = 6`** (`Problem2_16_3.lean:1051`, #6340,
   *claimed 5 days*). A concrete finrank computation for the type-G₂ positive
   part; surrounding 2.16.3(b) machinery is fully proved in the same file. The
   long-held claim is the concern — **verify liveness / release if stale**.

**Tier 2 — substantial but concrete book route, currently unclaimed:**

3. **Ch6 `affine_tree_two_branch_iso`** (#6881) and
   **`affine_tree_one_branch_iso`** (#6882). Each mirrors the finite
   `tree_branch_iso` (~170 lines) plus spine/fork extraction; #6882 additionally
   needs an equality-case Diophantine solver (affine analogue of the merged
   `arm_length_solutions`). The book gives an explicit route for both. Two
   independent leaf lemmas — good parallel work.
4. **Ch4 `so3_cyclic_of_poleData` / `so3_dihedral_of_poleData`** (#6877). Enrich
   `pole_order_data` to expose orbit representatives + stabilizer generators,
   then feed the merged dihedral/cyclic recognition lemmas. Geometry-heavy but
   the algebraic cores already exist.

**Tier 3 — deep assembly / large classification:**

5. **Ch8 `Problem_8_2_8_ext`** (#6818). The four-step Ext Künneth assembly; all
   named building blocks exist except the #6884 rearrange lemma it waits on.
   Best claimed *after* #6884 lands.
6. **Ch4 `so3_classification_aux` polyhedral + assembly** (#6864, flagged
   *large*). The A₄/S₄/A₅ realizations and final five-way disjunction; expects
   careful decomposition.

The Ch6 top-level `affine_dynkin_classification` (#6793/#6785) and the whole
6.1.3-g ⟹ direction remain the deepest live arc — do not attempt the assembly
before the three tree-case sub-lemmas (#6880/#6881/#6882) close.

## Method notes

- Counts are comment-stripped genuine sorries against `origin/main` HEAD
  `40317cf7`; the reproducer command above is authoritative.
- `proof_wanted` gaps (2 declarations: `Remark2_9_3.lean` `ado`,
  `Remark5_23_3.lean` `sl_finiteDimensional_completely_reducible`) are *not*
  counted in the 9 but are real unproved surface — noted for honesty. Down from
  3 (`algIrrepGL_finrank_constShift` promoted to theorem by #6857). No
  in-definition obligations remain.
- **A partial status re-audit was performed this window** (deliverable 2): two
  stale `statement_formalized` labels (2.16.4, 5.24.2) corrected to `sorry_free`
  after confirming the source is fully sorry-free and honest (main theorems
  present, not crux-as-hypothesis). The five 06:14 deliberate holds were left
  intact; `Chapter6/Problem6.1.3_continued_E7_E8` was flagged (sorry-free source,
  fragment of an incomplete arc) but not changed pending a full blob audit.
  Future summarize sessions should keep applying the blob check rather than
  trusting the sorry counter alone.
- The per-chapter *item* split uses a heuristic marker-based binning and may
  differ by a few from prior docs; the status-distribution totals (592, and the
  554/11/8/… breakdown) and the source sorry counts are exact.
- Merged-PR list obtained via
  `gh pr list --state merged --json number,title,mergedAt` filtered to
  `mergedAt > 2026-07-16T13:05:53Z` (24 results).

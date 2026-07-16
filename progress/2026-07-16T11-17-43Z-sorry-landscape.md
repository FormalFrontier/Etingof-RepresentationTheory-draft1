# Sorry Landscape Analysis — post-25-merge refresh

Generated 2026-07-16 11:17 UTC by summarize session (issue #6786, branch
`agent/b6660447`) against `origin/main` at HEAD `dbc9994f`. **Supersedes
`progress/2026-07-16T06-14-26Z-sorry-landscape.md`** (issue #6733, HEAD
`a78b010b`), which reported **27 genuine sorries in 9 files**; the current count
is **6 in 6 files**. Since that snapshot closed (2026-07-16 06:24:41Z), **25 PRs
merged to `main`** (the issue #6786 body counted 18 at the time it was written,
07 more landed while it sat in the queue). The merges concentrated in three
threads — Ch6 Dynkin/affine-Dynkin classification, Ch8 Problem 8.2.8 `Tor`/Künneth,
and Ch5 Problem 5.24.1-b + 5.24.2 FFT — and thinned the frontier by **21 sorries
and 3 whole files** in a single window.

## Headline: 6 genuine sorries across 6 files, one per file

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **6 genuine proof-gap `sorry`
tactics in 6 files** — down from 27/9. Each of the 6 files now holds exactly one
sorry. There are **no `axiom` declarations and no `admit`s** (every `axiom`/`admit`
string hit is English prose inside docstrings). Two files still record
book-unproved statements via **`proof_wanted`** rather than `sorry` — 3
`proof_wanted` declarations in total: `Chapter2/Remark2_9_3.lean:47` (`ado`,
Ado's theorem), `Chapter5/Remark5_23_3.lean:110` (`algIrrepGL_finrank_constShift`)
and `:129` (`sl_finiteDimensional_completely_reducible`). These are genuine gaps
the comment-stripped counter does **not** see, so "6 sorries" slightly understates
the unproved surface.

**Both in-definition obligations from the prior landscape are now discharged.**
The 06:14 doc flagged two proof obligations *inside definition bodies*
(`Problem5_24_1_b.lean:57` and `ExternalTensorResolution.lean:102`, the `quasiIso`
field of a `ProjectiveResolution`). `Problem5_24_1_b.lean` is now fully sorry-free,
and `ExternalTensorResolution.lean`'s `quasiIso` field was filled by #6777
(the tensor-cokernel augmentation iso). So **all 6 remaining sorries are
top-level proof gaps** — there are no in-definition obligations left.

Reproduce the headline count (comment-stripping `awk` depth-counter, then
whole-word `sorry` on surviving code) against a clean `origin/main` checkout:
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 6 across 6 files at HEAD dbc9994f
```

Per-file genuine-sorry tally (comment-stripped) — one sorry each:
```
1  Chapter2/Problem2_16_3.lean                    finrank_g_three = 6              (#6340, claimed)
1  Chapter2/Problem2_16_4.lean                    finrank_irreducible_le_char     (#6801, claimed)
1  Chapter4/Problem4_12_8.lean                    so3_finite_subgroup_classification (#6802, unclaimed)
1  Chapter5/Problem5_24_2_Bridge.lean             FFT core (exists_endTensorEval_equivariant_section) (#6789, claimed)
1  Chapter6/Problem6_1_3_continued_tildeE.lean    affine_dynkin_classification (⟹ dir) (#6785, blocked)
1  Chapter8/Problem8_2_8.lean                     Problem_8_2_8_ext (Ext Künneth) (#6803, unclaimed)
```

Per-chapter genuine sorries (from the Lean source, authoritative): Ch2 = 2,
Ch4 = 1, Ch5 = 1, Ch6 = 1, Ch8 = 1; Ch0/1/3/7/9 = 0. The prior landscape's
largest block — Ch6 Dynkin/lattice (14) — has collapsed to a single sorry: the
E7/E8 file (`Problem6_1_3_continued_E7_E8.lean`, was 9) is now fully sorry-free,
and the affine-Ẽ file (`Problem6_1_3_continued_tildeE.lean`, was 5) is down to
the one deep ⟹ direction.

### items.json status distribution (592 items)

| Status | Count |
|--------|------:|
| `sorry_free` | 552 |
| `statement_formalized` | 13 |
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

Change vs the 06:14 doc (was 552 / 14 / 7 / …): **one item was reclassified
`statement_formalized` → `proved`** (net: stmt 14→13, proved 7→8), tracking the
Ch5 Problem 5.24.1-b completion this window. The heterogeneous legacy labels
(`proved`, `formalized`, `accepted`, `proof_complete`, `partially_*`) persist
from earlier pipeline stages and are **flagged but not mass-rewritten** here, per
the standing landscape convention. No `sorry_free`-labelled item hides a live
source sorry: every one of the 6 sorry-carrying files maps to a
`statement_formalized` item (2.16.3, 2.16.4, 4.12.8, 5.24.2, 6.1.3_continued_tildeE,
8.2.8).

### Per-chapter picture

Columns: total items, `sorry_free`, `statement_formalized`, other statuses, and
**genuine sorries in the Lean source** (comment-stripped). The item counts below
use a heuristic chapter binning (items are assigned by the first `ChapterN` /
`N.M` marker in their `id`/`derived_from`/`lean_file`); it differs by a handful
from the 06:14 doc's binning (notably it pushes derived/discussion blobs out of
the ch0 bucket into their referenced chapter). The **status-distribution totals
and the genuine-sorry column are authoritative**; the per-chapter item split is
indicative.

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/back) | 6 | 6 | 0 | 0 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 118 | 110 | 3 | 5 | 2 |
| 3 | 58 | 58 | 0 | 0 | 0 |
| 4 | 60 | 54 | 2 | 4 | 1 |
| 5 | 163 | 149 | 2 | 12 | 1 |
| 6 | 64 | 59 | 3 | 2 | 1 |
| 7 | 61 | 59 | 0 | 2 | 0 |
| 8 | 24 | 22 | 1 | 1 | 1 |
| 9 | 35 | 32 | 2 | 1 | 0 |
| **total** | **592** | **552** | **13** | **27** | **6** |

## What changed since 2026-07-16 06:14 (the 25 merges that landed)

By thread (net sorry deltas vs the prior landscape):

- **Chapter 6 — 14 → 1.** The biggest mover. The **Dynkin / affine-Dynkin
  Problem 6.1.3 classification arc** essentially closed out. Landed:
  `cycle_cartan_mulVec_one_eq_zero` + `cycle_cartan_det_zero` (#6746),
  `marks_pos` + `cartan_det_zero` (affine Cartan matrices singular via the marks
  kernel, #6759), `det_cartan_A` (=n+1) / `det_cartan_D` (=4) via cofactor
  recursion (#6761), `isDynkinDiagram_degree_le_three` (#6770),
  `isDynkinDiagram_A`/`_D` (#6771), `isAffineDynkinDiagram_of_type` (#6772),
  `isDynkinDiagram_isTree` (#6773), `isDynkinDiagram_unique_degree_three` (#6778),
  the affine-classification backward direction + reindexing lemma (#6781), and
  `affineNullVector_pos` (discrete Perron–Frobenius, step 1 of #6785, #6799). The
  E7/E8 Cartan file (`Problem6_1_3_continued_E7_E8.lean`, was 9) is now fully
  sorry-free. Residual 1: the **⟹ direction of `affine_dynkin_classification`**
  in `Problem6_1_3_continued_tildeE.lean` (was 5).
- **Chapter 8 — 3 → 1.** The **Problem 8.2.8 `Tor`/Künneth** stream landed its
  capstone. `rearrangeBifunctorNatIso` packaging (#6758), positive-degree
  acyclicity + `[Field k]` fix (#6757), `rearrangeComplex` final assembly (#6763),
  reduction of `quasiIso` to a single degree-0 goal (#6764), the degree-0
  augmentation iso filling `extTensorProjectiveResolution.quasiIso` (#6777), and
  finally `Problem_8_2_8_tor` proved sorry-free with its RHS corrected to the
  `k`-linear `⊗_k` (#6804). This cleared both the `Problem8_2_8.lean` Tor sorry
  and the `ExternalTensorResolution.lean` in-definition obligation. Residual 1:
  the **`Ext` half `Problem_8_2_8_ext`** (`Problem8_2_8.lean:162`).
- **Chapter 5 — 6 → 1.** The **5.24.1-b sign-twist / conjugate-partition** thread
  finished: three elementary sorries (#6753), `signTwist_map_leftIdeal` + reusable
  symmetrizer lemmas (#6776), and `spechtModule_signTwist_iso_conjugate`
  (`V_λ ⊗ ℂ_- ≅ V_{λ*}`, #6782) — clearing all 5 sorries from
  `Problem5_24_1_b.lean` (Problem 5.24.1 reclassified to `proved`). The **5.24.2
  FFT** thread advanced heavily but is not yet closed: `symGroupImage` =
  GL-invariant tensors (#6798), `endTensorEval` GL-equivariance (#6800),
  surjectivity onto degree-d polynomials (#6805), and the invariant-range
  identification assembly (#6808). Residual 1: the FFT reductivity core inside
  `exists_endTensorEval_equivariant_section` (`Problem5_24_2_Bridge.lean:291`).
- **Chapter 2 — 3 → 2.** The **sl₂ char-p sharpness half** landed:
  `exists_irreducible_dim_char` constructs the p-dimensional simple sl(2)-module
  L(p−1) (#6794). Residual 2: the **upper-bound half `finrank_irreducible_le_char`**
  (`Problem2_16_4.lean:513`) and `finrank_g_three = 6` (`Problem2_16_3.lean:1051`,
  the G₂ positive-nilpotent finrank).
- **Chapters 3, 4, 7, 9 — unchanged.** Ch3/7/9 remain source-sorry-free; Ch4
  still holds its single `so3_finite_subgroup_classification` sorry.

## In-flight chains (open issues / PRs as of this snapshot)

The frontier is now down to **6 distinct single-sorry theorems**, each already
tracked by an issue:

- **Ch6 Problem 6.1.3-g affine classification ⟹** — **#6785** (`blocked` on
  **#6792** cyclic case / **#6793** tree case). Step 2 (minimality) is **#6791**,
  with open PR **#6806** (`agent/c9ea1cf1`). Step 1 `affineNullVector_pos` already
  merged (#6799). This is the deepest live sorry: the full ⟹ direction of the
  affine Dynkin classification.
- **Ch8 Problem 8.2.8 Ext** — **#6803** (unclaimed, **now unblocked**): the Ext
  half of the Künneth iso `Extⁱ_{A₁⊗A₂}(M₁⊗M₂,N₁⊗N₂) ≅ ⨁_{j+m=i} Extʲ ⊗_k Extᵐ`.
  Its dependency #6796 (the `⊗_k` Tor half + shared Künneth machinery) merged as
  #6804, so #6803 is ready to claim.
- **Ch5 Problem 5.24.2 FFT core** — **#6789** (claimed): the equivariant section
  `polyToEndTensor` closing `weightedHomogeneous_invariant_mem_range_endTensorEval`.
  Verify liveness; much of the surrounding range-identification infra just landed
  (#6798/#6800/#6805/#6808).
- **Ch2 2.16.4 upper bound** — **#6801** (claimed, recent):
  `finrank_irreducible_le_char` (every irreducible sl(2) rep in char p>2 has
  dimension ≤ p), complementing the merged `exists_irreducible_dim_char`.
- **Ch2 2.16.3(a)** — **#6340** (claimed 5 days): `finrank_g_three = 6`. Long-held
  claim; verify liveness / consider release if stale.
- **Ch4 4.12.8(a)** — **#6802** (unclaimed): `so3_finite_subgroup_classification`
  via pole-counting. A genuinely large classical formalization behind a single
  sorry; the issue expects worker-led decomposition.

## Ranked shortlist of tractable next targets

"Single sorry" ≠ cheap — every one of the 6 is now a whole-theorem gap.

**Tier 1 — self-contained, concrete:**

1. **Ch2 2.16.3(a) `finrank_g_three = 6`** (`Problem2_16_3.lean:1051`, #6340). A
   concrete finrank computation for the type-`G₂` positive part; surrounding
   2.16.3(b) machinery is fully proved in the same file. Claimed 5 days — verify
   liveness before re-planning.
2. **Ch2 2.16.4 upper bound** (`finrank_irreducible_le_char`, #6801). The sharpness
   half already landed (#6794), so this closes out 2.16.4. Claimed recently.

**Tier 2 — unblocked, substantial:**

3. **Ch8 8.2.8 Ext** (`Problem_8_2_8_ext`, #6803, unclaimed). Now unblocked by the
   merged `⊗_k` Tor half; reuses `extTensorProjectiveResolution` and the
   `ExternalTensor*` machinery. The crux is the finite-dimensional
   `Hom`-tensor iso in each degree, then cohomological Künneth.
4. **Ch5 5.24.2 FFT core** (#6789, claimed). Deep Schur–Weyl / First Fundamental
   Theorem, but the range-identification scaffolding just landed — the residual is
   the equivariant section.

**Tier 3 — deep classification arcs:**

5. **Ch4 4.12.8(a)** (`so3_finite_subgroup_classification`, #6802, unclaimed) —
   pole-counting classification of finite subgroups of SO(3). Large; expects
   decomposition.
6. **Ch6 6.1.3-g affine ⟹** (`affine_dynkin_classification`, #6785, blocked on
   #6792/#6793, PR #6806 in flight for step 2). The single hardest live sorry.

## Method notes

- Counts are comment-stripped genuine sorries against `origin/main` HEAD
  `dbc9994f`; the reproducer command above is authoritative.
- `proof_wanted` gaps (3 declarations across 2 files: `Remark2_9_3.lean`,
  `Remark5_23_3.lean`) are *not* counted in the 6 but are real unproved surface —
  noted for honesty. No in-definition obligations remain (both prior ones cleared).
- **No status re-audit was performed this window.** The 06:14 doc did a full
  blob-audit of the `statement_formalized` residue and deliberately kept 5 items
  `statement_formalized` despite sorry-free source (6.1.6(d), 9.4.6(ii), 9.5.3(iii),
  2.16.5, 4.12.11(b) — crux-as-hypothesis, `Prop`-def-only, or unstated parts).
  This refresh did not re-run that audit; the 552 `sorry_free` count therefore
  still reflects the 06:14 audited baseline plus the mechanical arithmetic of the
  25 merges. Future summarize sessions should keep applying the blob check rather
  than trusting the sorry counter alone.
- The per-chapter *item* split uses a heuristic marker-based binning and may differ
  by a few from the 06:14 doc's split; the status-distribution totals (592, and the
  552/13/8/… breakdown) and the source sorry counts are exact.
- Merged-PR list obtained via
  `gh pr list --state merged --json number,title,mergedAt` filtered to
  `mergedAt > 2026-07-16T06:24:41Z` (25 results).

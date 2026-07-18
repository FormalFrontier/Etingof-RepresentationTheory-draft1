# Sorry Landscape Analysis — post-20-merge refresh (project tail)

Generated 2026-07-18 16:29 UTC by summarize session (issue #6976, branch
`agent/72fd7506`) against `origin/main` at HEAD `7337d8e3`. **Supersedes
`progress/2026-07-17T22-15-58Z-sorry-landscape.md`** (issue #6917, HEAD
`f3721e82`), which reported **6 genuine sorries in 5 files**; the current count
is **4 in 3 files**. Since that snapshot's HEAD `f3721e82`, **20 PRs merged to
`main`** (13 of them after #6917 *closed* at 2026-07-18T05:53:59Z — the count the
#6976 issue body cites; the other 7 landed in the gap between the prior doc's
generation at 22:16Z and #6917's close). The merges concentrated in the three
active threads —
**Ch6 Problem 6.1.3-g** (the two affine-Dynkin tree-case layout residuals both
closed → Ch6 source-sorry-free), **Ch8 Problem 8.2.8-Ext** (the `Ext ≃ Extₖ`
bridge crux `key123` / `map_smul'` closed by #6968 → `ExtAbelianComparison.lean`
now sorry-free), and **Ch4 Problem 4.12.8-a-iv** (the single abstract
`so3_classification_aux` sorry was assembled into a five-way dispatch; the
cyclic, dihedral and tetrahedral disjuncts landed sorry-free, leaving the two
hardest — octahedral and icosahedral — as explicit geometric cruxes).

As in every prior window the frontier **shifted** as much as it shrank: the net
fall 6 → 4 masks whole sub-arcs going sorry-free (Ch6 tree case, Ch8 Ext bridge)
while the abstract Ch4 classification sorry split into two concrete disjunct
cruxes. The project is at its **tail**: every one of the 4 live sorries is a
spec-first skeleton whose assembly is already stated, and every one is covered
by a claimed or in-flight issue (nothing on the frontier is unowned).

## Headline: 4 genuine sorries across 3 files

After stripping every block comment (`/- … -/`, nesting-aware) and line comment
(`-- …`), the `EtingofRepresentationTheory/` tree contains **4 genuine
proof-gap `sorry` tactics in 3 files** — down from 6/5. There are **no `axiom`
declarations and no `admit`s** (the sole `^axiom` grep hit is English prose
inside a `Remark2_9_3.lean` docstring). Two files record book-*disavowed*
statements via **`proof_wanted`** rather than `sorry` — **2** `proof_wanted`
declarations, unchanged: `Chapter2/Remark2_9_3.lean:47` (`ado`, Ado's theorem)
and `Chapter5/Remark5_23_3.lean:209` (`sl_finiteDimensional_completely_reducible`).
These `proof_wanted` gaps are genuine unproved surface the comment-stripped
counter does **not** see, so "4 sorries" slightly understates the unproved
frontier (the book explicitly disavows both, so they are not project debt).

Reproduce the headline count (nesting-aware comment strip, then whole-word
`sorry` on surviving code) against a clean `origin/main` checkout at HEAD
`7337d8e3`:
```bash
python3 - <<'PY'
import re, glob
def strip(s):
    out=[]; i=0; n=len(s); d=0
    while i<n:
        if d>0:
            if s[i:i+2]=='/-': d+=1; i+=2; continue
            if s[i:i+2]=='-/': d-=1; i+=2; continue
            i+=1; continue
        if s[i:i+2]=='/-': d+=1; i+=2; continue
        if s[i:i+2]=='--':
            j=s.find(chr(10),i)
            if j==-1: break
            i=j; continue
        out.append(s[i]); i+=1
    return ''.join(out)
tot=0
for f in glob.glob('EtingofRepresentationTheory/**/*.lean', recursive=True):
    m=re.findall(r'(?<![\w.])sorry(?![\w])', strip(open(f).read()))
    if m: print(len(m), f); tot+=len(m)
print('TOTAL', tot)   # -> 4 across 3 files at HEAD 7337d8e3
PY
```

Per-file genuine-sorry tally (comment-stripped), with the enclosing declaration
and tracking issue/PR:
```
1  Chapter2/Problem2_16_3.lean  :1051  finrank_g_three = 6 (G₂ positive nilpotent, dim 6)   (#6340, claimed)
2  Chapter4/Problem4_12_8.lean  :1736  so3_octahedral_of_poleData  ({2,3,4} ⟹ G ≃* S₄)       (#6972; reduction PRs #6974/#6977)
                                :1753  so3_icosahedral_of_poleData ({2,3,5} ⟹ G ≃* A₅)       (#6971; reduction PR #6973)
1  Chapter8/Problem8_2_8.lean   :291   Problem_8_2_8_ext (Ext Künneth final assembly)        (#6898, claimed)
```

Per-chapter genuine sorries (from the Lean source, authoritative): Ch2 = 1,
Ch4 = 2, Ch8 = 1; **Ch0/1/3/5/6/7/9 = 0**. Two whole chapters went
source-sorry-free this window: **Ch6** (both `_tildeE.lean` affine-layout
residuals closed) and, already clear since the prior window, **Ch9**.

### Honesty note on the two Ch4 sorries and the in-flight reductions

On `main` the two Ch4 sorries are the *entire* proof bodies of
`so3_octahedral_of_poleData` (line 1736) and `so3_icosahedral_of_poleData`
(line 1753) — bare `sorry`s returning `Nonempty (G ≃* Equiv.Perm (Fin 4))` and
`Nonempty (G ≃* alternatingGroup (Fin 5))` from the `{2,3,4}` / `{2,3,5}` pole
data. Three open PRs (#6974, #6977 for octahedral; #6973 for icosahedral)
perform the *reduction*: they prove the counting (`|G| = 24` / `60`) and the
`S₄` / `A₅`-landing cardinality assembly sorry-free, isolating the geometric
core as a single named crux — `exists_octahedral_faithful_hom` (#6972) and
`so3_icosahedral_exists_faithful_perm5` (#6971), a faithful `G`-action on the 4
body diagonals / the 5 inscribed tetrahedra. **These reduction PRs leave that
crux as `sorry`.** So when they merge the source count stays at 4 (2 in Ch4) —
the sorry merely relocates from the `_of_poleData` theorem body into the named
crux theorem. The actual crux proofs (#6971, #6972) are the substantive
remaining geometry and are open, unclaimed feature issues.

### items.json status distribution (592 items, post-reconciliation)

Figures below are **after** this session's 5 status corrections (deliverable 2,
detailed in the reconciliation section); pre-reconciliation values in parens.

| Status | Count |
|--------|------:|
| `sorry_free` | 559 (was 554) |
| `proved` | 8 |
| `statement_formalized` | 7 (was 11) |
| `accepted` | 6 |
| `formalized` | 4 |
| `proof_complete` | 3 |
| `partially_formalized` | 2 |
| `partially_proved` | 1 (was 2) |
| `sorry` | 1 |
| `non_formalizable` | 1 |
| **total** | **592** |

Reproduce:
```bash
python3 -c "import json,collections; d=json.load(open('progress/items.json')); \
print(collections.Counter(it.get('status') for it in d))"
```

### Status reconciliation (deliverable 2): 5 corrections + 5 confirmed holds

A comment-stripped scan flagged **10** non-`sorry_free` items whose source Lean
file is now sorry-free. Per the prior doc's discipline — *a zero-sorry scan
alone does not license reclassifying, because several `statement_formalized`
items are deliberate holds* — each was blob-audited (read the book deliverable's
full set of parts, then the item's theorem/def signatures across its files) to
decide whether every part is actually stated **and** proved. Result: **5
reclassified to `sorry_free`**, **5 confirmed as genuine holds** and left as-is.

**Reclassified `→ sorry_free` (full book deliverable met, source sorry-free):**

| Item | was | Evidence (proved parts) |
|------|-----|-------------------------|
| `Chapter6/Problem6.9.2` | `partially_proved` | (a) ℤ-basis `α_isBasis`, (b) E₈ Gram `α_gram_is_E8`, (c) `E6/E7Lattice` coordinate-equal subsets, (d) root counts 240/126/72 — all proved |
| `Chapter9/Problem9.5.3` | `statement_formalized` | (i) `blocks_equiv_indecomposableCentralIdempotents`, (ii) `hom_subsingleton_of_not_linked`, (iii) char-2 k[S₃] `algebra_decomposition`/`simple_iff_triv_or_std` (in `Problem9_5_3_S3Char2.lean`) — the "(iii) deferred" docstring note is **stale** |
| `Chapter6/Problem6.1.3_continued_tildeE` | `statement_formalized` | (e) `cartan_det_zero`, (f) `dynkin_classification`, (g) `affine_dynkin_classification` (full iff to Ãₙ/D̃ₙ/Ẽ₆₋₈) — all proved; the two prior-window layout sorries closed this window |
| `Chapter6/Problem6.1.3_continued_E7_E8` | `statement_formalized` | (a)–(d) `det_cartan_A/D/E6/E7/E8` + `isDynkinDiagram_*` tree/degree lemmas — all proved |
| `Chapter5/GL2ConjugacyClassCount` (derived) | `statement_formalized` | four per-type counts + `card_conjClasses_eq_sum` partition + grand total q²−1 — all proved; its `note` (which still listed 3 counts as "remaining sorries") was corrected in the same edit |

**Confirmed genuine holds — NOT reclassified** (source sorry-free but the book
deliverable is incomplete; the counter would overstate completion here):

- `Chapter6/Problem6.9.3` (**stays `partially_proved`**) — (a) `ext1_source`/`ext1_sink`
  proved, but (b) the Jordan–Hölder series is only a `Prop` stub `IsJordanHolderData`
  (composition-series notion not yet in the project), so part (b) is unproved.
- `Chapter9/Problem9.4.6` (**stays `statement_formalized`**) — (i) homological
  dimension `= 1` proved, but (ii) `cartanMatrix_pathAlgebra_eq_pathCount` passes
  the path-counting crux as the hypothesis `hcover` (crux-as-hypothesis). This is
  live claimed work: **#6975** is discharging exactly that `hcover`.
- `Chapter2/Problem2.16.5` (**stays `statement_formalized`**) — the #6976 issue
  body *suggested* this one for reclassification, but the audit found the
  classification of irreducibles (root-of-unity and non-root-of-unity cases) is
  explicitly deferred; only the highest-weight-vector existence + dimension bound
  are proved. Honoring "verify each before editing / do not invent statuses", it
  is **kept held** against the issue's heuristic suggestion.
- `Chapter4/Problem4.12.11` (**stays `statement_formalized`**) — irreducibility of
  V, W is proved over ℝ but the book's part-(b) requirement of irreducibility
  *after complexification* is recorded only in a docstring, not a theorem.
- `Chapter6/Problem6.1.6` (**stays `statement_formalized`**) — (a),(b),(c),(e)
  proved, but (d) the group↔diagram McKay correspondence is only a `Prop` stub
  `McKayCorrespondence`.

Post-reconciliation distribution (592 items): `sorry_free` **554 → 559**,
`statement_formalized` **11 → 7**, `partially_proved` **2 → 1**; all other
statuses unchanged. Reproduce with the `collections.Counter` one-liner above.
The remaining 4 held `statement_formalized` items with sorry-free source
(2.16.5, 4.12.11, 6.1.6, 9.4.6) are **correctly held** — each has a concrete
unproved book part (deferred classification, complexified irreducibility, or a
`Prop`-stub correspondence/series), not a stale status; future sessions should
**not** reclassify them on a sorry-scan alone.

## What changed since 2026-07-17 22:16 (the 20 merges since HEAD f3721e82)

By chapter, net source-sorry movement:

- **Chapter 6 — 2 → 0 (tree case fully assembled; source-sorry-free).** The two
  residual layout sorries in `_tildeE.lean` both closed:
  `affine_one_branch_arm_layout` (the three-arm sort/reindex onto `armAdjIdx`)
  by **#6937**, and `affine_two_branch_deleted_isD` (the finite-Dₖ reattach
  crux, #6922) by **#6956** (delete leaf, transport w's two leaves, classify and
  rule out E/A via #6939, localize the Dₖ reattach point), with supporting
  arithmetic/discriminator infra landing alongside (`affine_two_branch_pinch`
  #6934, `affine_arm_walk'` #6942, the type-D discriminator #6945,
  `affine_two_branch_fork_leaves` #6949). Chapter 6 source is now entirely
  sorry-free.
- **Chapter 8 — 2 → 1 (Ext bridge sorry closed).** Seven merges drove the
  `Ext ≃ₗ[k] Extₖ` comparison to completion. The prior window's in-`def`
  `extAbelianIsoExtₖ` `map_smul'` obligation (`ExtAbelianComparison.lean:84`) was
  reduced to the crux `key123` (#6936), then `key123` was discharged: the `hnat`
  generator-crux reduction (#6948), `homCochainComplexPostcomp` (#6954), the
  HomComplex postcomposition endo + `homologyAddEquiv` naturality (#6958), and
  finally **#6968** — the tower naturality of `homComplexHomologyAddEquivₖ` that
  **closed the crux #6951**, making `extAbelianIsoExtₖ` (and all of
  `ExtAbelianComparison.lean`) sorry-free. Module reconciliation deliverable 2
  landed (#6964). The single remaining Ch8 sorry is `Problem_8_2_8_ext`
  (`Problem8_2_8.lean:291`), the four-step Ext Künneth final assembly (#6898,
  claimed).
- **Chapter 4 — 1 → 2 (abstract sorry split into two concrete cruxes).** The
  lone `so3_classification_aux` sorry of the prior window was **assembled** into
  a five-way dispatch by **#6963**; the cyclic + dihedral disjuncts landed
  (`so3_dihedral_of_poleData` + ρ-extraction #6947, `exists_dihedral_swap`
  #6955, audit #6959) and the **tetrahedral** realization
  `so3_tetrahedral_of_poleData` ({2,3,3} ⟹ A₄) landed sorry-free (#6965). What
  remains are the two hardest disjuncts, now explicit: `so3_octahedral_of_poleData`
  and `so3_icosahedral_of_poleData`. Net +1 sorry, but this is the frontier
  moving *deeper* — one abstract dispatch sorry became two concrete geometric
  realization cruxes.
- **Chapter 2 — 1 → 1.** `finrank_g_three = 6` (the type-G₂ positive-nilpotent
  finrank, `Problem2_16_3.lean:1051`, #6340) unchanged.
- **Chapters 1, 3, 5, 7, 9 — unchanged, source-sorry-free.**

## In-flight chains (open issues / PRs as of this snapshot)

The frontier is **4 sorries across 4 problems**, all owned:

- **Ch4 Problem 4.12.8-a-iv — octahedral (#6972) & icosahedral (#6971).** Both
  `_of_poleData` disjuncts have open *reduction* PRs (#6974 & #6977 octahedral,
  #6973 icosahedral) that discharge the counting + cardinality assembly and
  isolate the geometric crux; **the crux proofs themselves (#6971, #6972) are
  open, unclaimed feature issues** — construct a faithful `G`-action on the 4
  body diagonals (→ S₄) and on the 5 inscribed tetrahedra (→ A₅), then prove no
  nontrivial rotation fixes them all. These are the deepest live Ch4 geometry;
  they depend on their reduction PRs landing first (the crux theorem statements
  are introduced by those PRs). Sub-issues of the polyhedral arc #6864.
- **Ch8 Problem 8.2.8-Ext `Problem_8_2_8_ext` (#6898, claimed).** The four-step
  Ext Künneth assembly, `Problem8_2_8.lean:291`. Its inputs are now all real
  data: the `Ext ≃ₗ[k] Extₖ` bridge is sorry-free (#6968), fg resolutions
  (#6931) and module reconciliation (#6964) landed. The capstone of the Ch8 arc.
- **Ch2 2.16.3(a) `finrank_g_three = 6` (#6340, claimed).** A concrete finrank
  computation for the type-G₂ positive part; surrounding 2.16.3(b) machinery is
  fully proved in the same file. A long-standing claim — verify liveness.

Adjacent claimed work not on the sorry frontier: **#6975** (Ch9 9.4.6-ii —
discharge the `hcover` hypothesis to make `cartanMatrix_pathAlgebra_eq_pathCount`
unconditional; the file is sorry-free but 9.4.6(ii) is still *conditional*, so
9.4.6 is not yet a completed deliverable — see reconciliation below).

## Method notes

- Counts are comment-stripped genuine sorries against `origin/main` HEAD
  `7337d8e3` (== this session's branch base); the Python reproducer above is
  authoritative. The strip is block-comment-nesting-aware and drops `--` line
  comments. Cross-checked against a raw `grep -n '\bsorry\b'`: the only extra
  raw hits are `"sorry"`/`"sorry-free"` prose inside docstrings.
- `proof_wanted` gaps (2 declarations: `Remark2_9_3.lean` `ado`,
  `Remark5_23_3.lean` `sl_finiteDimensional_completely_reducible`) are *not*
  counted in the 4 but are real (book-disavowed) unproved surface — noted for
  honesty. No in-`def`/`instance` **data** sorries remain: the prior window's
  one in-`def` obligation (`extAbelianIsoExtₖ` `map_smul'`) is now discharged.
- Merge set: `git log --oneline f3721e82..HEAD` = **20 squash-merges** since the
  prior doc's HEAD (Ch4 ×5, Ch6 ×6, Ch8 ×7, plus the #6938 summarize doc and the
  #6967 review close-out). Of these, `gh pr list --state merged` filtered
  to `mergedAt > 2026-07-18T05:54:00Z` gives the **13** the issue body cites; the
  other 7 landed between the prior doc's 22:16Z generation and #6917's 05:54Z
  close.

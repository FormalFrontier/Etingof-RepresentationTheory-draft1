# Sorry Landscape Analysis — post-115-merge refresh

Generated 2026-07-16 06:14 UTC by summarize session (issue #6733, branch
`agent/24e13a6f`) against `origin/main` at HEAD `a78b010b`. **Supersedes
`progress/2026-07-13T14-47-37Z-sorry-landscape.md`** (issue #6498, HEAD
`1d954f7a`), which reported **81 genuine sorries in 23 files**; the current count
is **27 in 9 files**. Since that snapshot closed (2026-07-13 14:53:19Z), **115
PRs merged to `main`**, spread broadly across chapters — merge counts by chapter
are Ch8 (23), Ch9 (21), Ch6 (18), Ch5 (15), Ch2 (10), Ch3 (9), Ch4 (8), Ch7 (5).
The frontier thinned by **54 sorries and 14 whole files** — the largest single
window in the project's recorded history, driven by the Ch5 orbit-method, Ch6
McKay/Dynkin, Ch8 Tor/Ext, and Ch9 path-algebra threads all converging at once.

## Headline: 27 genuine sorries across 9 files, concentrated in Chapters 5, 6, 8

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **27 genuine proof-gap `sorry`
tactics in 9 files** — down from 81/23. There are **no `axiom` declarations and
no `admit`s** (every `axiom`/`admit` string hit is English prose inside
docstrings, e.g. "axiom is introduced", "admit a unitary structure"). Two files
still record book-unproved statements via **`proof_wanted`** rather than `sorry`
(`Chapter2/Remark2_9_3.lean` — Ado's theorem; `Chapter5/Remark5_23_3.lean`);
these are genuine gaps the comment-stripped counter does **not** see, so "27
sorries" slightly understates the unproved surface. Two of the 27 are proof
obligations *inside a definition's body/`where` region* rather than top-level
proof gaps — permitted by project rules but still real obligations:
`Problem5_24_1_b.lean:57` and `ExternalTensorResolution.lean:102` (the `quasiIso`
field of a `ProjectiveResolution`).

Reproduce the headline count (comment-stripping `awk` depth-counter, then
whole-word `sorry` on surviving code) against a clean `origin/main` checkout:
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 27 across 9 files at HEAD a78b010b
```

Per-file genuine-sorry tally (comment-stripped, descending):
```
9  Chapter6/Problem6_1_3_continued_E7_E8.lean
5  Chapter6/Problem6_1_3_continued_tildeE.lean
5  Chapter5/Problem5_24_1_b.lean
2  Chapter8/Problem8_2_8.lean
2  Chapter2/Problem2_16_4.lean
1  Chapter8/ExternalTensorResolution.lean
1  Chapter5/Problem5_24_2_Bridge.lean
1  Chapter4/Problem4_12_8.lean
1  Chapter2/Problem2_16_3.lean
```

Per-chapter: Ch2 = 3, Ch4 = 1, Ch5 = 6, Ch6 = **14 (largest block)**, Ch8 = 3;
Ch3 = Ch7 = Ch9 = 0. The Ch6 Dynkin/lattice block (E7/E8 + affine Ẽ) is now the
clear centre of gravity, holding more than half of all remaining sorries.

### items.json status distribution (592 items)

After this session's status reconciliation (see "Status corrections" below):

| Status | Count |
|--------|------:|
| `sorry_free` | 552 |
| `statement_formalized` | 14 |
| `proved` | 7 |
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

The heterogeneous legacy labels (`proved`, `formalized`, `accepted`,
`proof_complete`, `partially_formalized`, `partially_proved`) persist from
earlier pipeline stages. They are **flagged but not mass-rewritten** here, per the
issue's instruction. A future housekeeping pass could canonicalize the sorry-free
legacy labels (`proved`/`formalized`/`accepted`/`proof_complete`) to `sorry_free`,
but that is cosmetic and out of scope for a landscape refresh.

### Per-chapter picture (after corrections)

Columns: total items, `sorry_free`, `statement_formalized`, other statuses, and
**genuine sorries in the Lean source** (comment-stripped). The sorry count can
differ from the `statement_formalized` count in both directions: one item may
span several sorried helper files, and — importantly this window — several
`statement_formalized` items are now *source*-sorry-free but were **kept**
`statement_formalized` because a book part is still assumed-as-hypothesis, stated
only as a bare `Prop` def, or entirely unstated (see "Status corrections").

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/derived) | 15 | 6 | 1 | 8 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 117 | 110 | 3 | 4 | 3 |
| 3 | 58 | 58 | 0 | 0 | 0 |
| 4 | 60 | 54 | 2 | 4 | 1 |
| 5 | 157 | 149 | 2 | 6 | 6 |
| 6 | 64 | 59 | 3 | 2 | 14 |
| 7 | 59 | 59 | 0 | 0 | 0 |
| 8 | 24 | 22 | 1 | 1 | 3 |
| 9 | 35 | 32 | 2 | 1 | 0 |
| **total** | **592** | **552** | **14** | **26** | **27** |

## Status corrections applied this session

**Method.** Every one of the 9 sorry-carrying files maps to an item whose status
is *not* `sorry_free` (verified: 2.16.3, 2.16.4, 4.12.8, 5.24.1, 5.24.2, 8.2.8,
6.1.3_E7_E8, 6.1.3_tildeE — all `statement_formalized`), so there are **no
`sorry_free`-labelled items hiding a live sorry**. The reverse direction —
`statement_formalized` items whose Lean source is now sorry-free — produced 11
candidates. Rather than mechanically flip all 11 (the rule prior landscapes used),
each was audited against its book blob to check whether the file is a *genuinely
complete* formalization or merely happens to contain no `sorry`.

**Key honesty finding: sorry-free source ≠ complete.** Five of the 11 candidates
are sorry-free yet do not fully formalize their book problem, so were **kept
`statement_formalized`**:

| Item | file | why NOT sorry_free |
|------|------|--------------------|
| `Chapter6/Problem6.1.6` | `Problem6_1_6.lean` | part (d) group↔diagram correspondence is only a bare `def … : Prop`, never proved |
| `Chapter9/Problem9.4.6` | `Problem9_4_6.lean` | part (ii) Cartan-counts-paths assumes its crux `hcover` (Hom(Pᵢ,Pⱼ) ≅ paths) as a hypothesis |
| `Chapter9/Problem9.5.3` | `Problem9_5_3.lean` | part (iii) blocks of `k[S₃]` in char 2 is entirely unstated |
| `Chapter2/Problem2.16.5` | `Problem2_16_5.lean` | the classification is replaced by structural lemmas (HW-vector existence + a dim bound); neither case is actually classified |
| `Chapter4/Problem4.12.11` | `Problem4_12_11.lean` | the "irreducible even after complexification" clause of (b) is asserted only in the docstring, proved only over ℝ |

The remaining **6 candidates are genuinely complete and were corrected to
`sorry_free`**:

| Item | file | was | now | closed by (window) |
|------|------|-----|-----|--------------------|
| `Chapter3/Problem3.8.5` | `Problem3_8_5.lean` | statement_formalized | sorry_free | Krull–Schmidt-failure: A,M indecomposable + A≇M, A²≅M² all proved |
| `Chapter3/Problem3.9.5` | `Problem3_9_5.lean` | statement_formalized | sorry_free | Clifford algebra even/odd matrix-algebra + semisimple⇔nondeg |
| `Chapter4/Problem4.12.7` | `Problem4_12_7.lean` | statement_formalized | sorry_free | all six parts (a)–(f), incl. SU(2)→SO(3) surjection with kernel {±1} |
| `Chapter5/Problem5.11.1` | `Problem5_11_1.lean` | statement_formalized | sorry_free | all A₅ induced-rep decompositions via Frobenius reciprocity |
| `Chapter8/Problem8.2.6` | `Problem8_2_6.lean` | statement_formalized | sorry_free | all Tor/Ext properties (i)–(v), incl. the balancing theorem |
| `Chapter8/Problem8.2.7` | `Problem8_2_7.lean` | statement_formalized | sorry_free | Tor/Ext for ℤ (i) and k[x] (ii), all vanishing + gcd identifications |

**6 items corrected** (`statement_formalized` → `sorry_free`); **5 items audited
and deliberately left** `statement_formalized`. Note the two stale docstrings
found during the audit: `Problem3_9_5.lean` and `Problem9_5_3.lean` still carry
"proofs are left as `sorry`" text from an earlier statement-pass; the code is in
fact fully proved (9.5.3 modulo part (iii), which is genuinely absent). These are
comment-only and were left untouched (this issue does not modify Lean sources).

## What changed since 2026-07-13 14:47 (the 115 merges that landed)

By chapter (only threads that moved; net sorry deltas vs the prior landscape):

- **Chapter 6 — 31 → 14.** The biggest mover. The **McKay-graph thread (6.1.6)**
  closed out its sorries: `mckay_connected` (#6655), the `mckay_isAffineDynkin`
  assembly from Cartan positive-semidefiniteness + not-positive-definiteness
  (#6675, #6637), dimension-vector-spans-kernel (#6628), and the no-self-loop
  `mckayAdj_no_selfLoop` cyclic/central-neg dichotomy and Frobenius `dim ∣ |G|`
  route (#6695, #6699, #6701, #6711, #6714, #6715, #6716, #6722, #6724, and the
  final `mckay_isAffineDynkin` axiom check #6748). `Problem6_1_6.lean` is now
  source-sorry-free (item kept `statement_formalized` — part (d) unproved, above).
  The residual 14 are the **Dynkin/lattice classification block**: E7/E8 Cartan
  work (`Problem6_1_3_continued_E7_E8.lean`, 9) and affine Ẽ
  (`Problem6_1_3_continued_tildeE.lean`, 5); the 6.9.2 E8-lattice file that held 8
  is now sorry-free (`Problem6.9.2` is `partially_proved`). Chip-away in flight
  via #6745 (`cycle_cartan_*`, open PR #6746).
- **Chapter 5 — 17 → 6.** `Problem5_11_1.lean` (A₅ induced reps, was 9) is fully
  proved and **corrected to `sorry_free`** this session. The Exercise 5.27.2
  orbit-method assemblies (dihedral/affine) and 5.27.3 landed sorry-free. Residual
  6: `Problem5_24_1_b.lean` (5, incl. one in-definition obligation) and the FFT
  bridge `Problem5_24_2_Bridge.lean` (1, `weightedHomogeneous_invariant_mem_range_endTensorEval`
  — the deep Schur–Weyl / First Fundamental Theorem core).
- **Chapter 8 — 8 → 3.** **8.2.6** (Tor/Ext properties, was 2) and **8.2.7**
  (Tor/Ext for ℤ and k[x], was 4) both completed and **corrected to `sorry_free`**.
  The active stream is now **Problem 8.2.8 `Tor` / Künneth**: `Problem8_2_8.lean`
  (2) plus `ExternalTensorResolution.lean` (1, the `quasiIso` resolution field).
  Landed infra this window: external tensor bifunctor/module `extTensorModule`
  (#6685, #6708), external tensor complex + augmentation (#6719), degreewise
  projectivity and `extTensorProjectiveResolution` (#6721, #6731), k-linear
  `tensorRightFunctorₖ` (#6728), and rearrangement milestones (a)/(b) (#6697,
  #6720).
- **Chapter 9 — 5 → 0.** Fully sorry-free at the source level. The path-algebra
  9.4.6 thread (`freePathEquiv` #6645; hom-dim invariance #6638/#6654; hom-dim of
  a path algebra with an edge #6623) and the 9.5.3 blocks↔idempotents thread
  (#6619/#6622, dévissage/splitting #6455) both discharged their sorries — though
  9.4.6 (part ii assumes `hcover`) and 9.5.3 (part iii absent) are **kept
  `statement_formalized`**, and 9.6.5 is `proved`.
- **Chapter 3 — 9 → 0.** `Problem3_8_5.lean` (Krull–Schmidt failure, was 4) and
  `Problem3_9_5.lean` (Clifford algebra, was 5) both completed and **corrected to
  `sorry_free`**.
- **Chapter 2 — 6 → 3.** 2.16.5 (q-enveloping-algebra, was 3) is now source-
  sorry-free (kept `statement_formalized` — classification deferred, above).
  Residual 3: sl₂ char-p `Problem2_16_4.lean` (2) and `Problem2_16_3.lean` (1,
  `finrank_g_three`).
- **Chapter 4 — 5 → 1.** `Problem4_12_7.lean` (SU(2)/ℍ/SO(3), was 1) completed and
  **corrected to `sorry_free`**; `Problem4_12_11.lean` (elasticity, was 3) is now
  source-sorry-free (kept `statement_formalized` — complexified-irreducibility
  clause omitted, above). Residual 1: `Problem4_12_8.lean` (classification of
  finite subgroups of SO(3)/SU(2)).
- **Chapter 7 — 0 → 0.** Remains fully sorry-free.

## In-flight chains (open issues / PRs as of this snapshot)

- **Ch8 Problem 8.2.8 `Tor` / Künneth** — the dominant active stream, decomposed
  across: assembler **#6657** (Künneth for Tor over A₁⊗A₂, `blocked`), the
  milestone-(c) complex-iso chain **#6742 / #6743 / #6744** (steps 2/1/3 of #6727;
  #6743 claimed, #6744 blocked, #6742 has partial PR **#6747** and is flagged
  `replan` — a `Module k` instance diamond on the `tensorOver` carriers), the
  restriction-commutation iso **#6738**, and the quasiIso glue **#6735**
  (`blocked`). Sorries: `Problem8_2_8.lean` (2) + `ExternalTensorResolution.lean`
  (1, `quasiIso` field). Deep — needs the restriction-of-scalars commutation iso
  plus Ch7 Künneth acyclicity.
- **Ch6 Problem 6.1.3-c Dynkin** — **#6745** (`cycle_cartan_mulVec_one_eq_zero` +
  `cycle_cartan_det_zero`, open PR **#6746**), chipping into the E7/E8 + affine-Ẽ
  block.
- **Ch2 sl₂ char-p** — **#6732** (unclaimed: `exists_irreducible_dim_char`, the
  sharpness half of 2.16.4, with a fully-worked L(p−1) construction route in the
  issue body) and **#6340** (claimed: `finrank_g_three = 6` for 2.16.3a). Verify
  #6340 liveness before planning.

## Ranked shortlist of tractable next targets

Honest tractability, seeding future planners. "Single sorry" ≠ cheap — several
one-sorry files below are deep whole-theorem gaps.

**Tier 1 — genuinely tractable, high value:**

1. **Ch2 2.16.4 sharpness** (`Problem2_16_4.lean`, `exists_irreducible_dim_char`;
   issue **#6732**, unclaimed). The p-dimensional simple sl₂-module L(p−1). The
   issue body gives the full construction (carrier `Fin p → k`, explicit e/f/h
   action, structure constants units mod p). Concrete and self-contained. The
   sibling `finrank_irreducible_le_char` (the dimension *bound*) is explicitly out
   of scope and stays sorried.
2. **Ch2 2.16.3(a) `finrank_g_three = 6`** (`Problem2_16_3.lean`, 1 sorry). A
   concrete finrank computation for the type-`G₂` positive part; surrounding
   2.16.3(b) machinery is fully proved in the same file. **Already claimed
   (#6340)** — verify liveness before planning.

**Tier 2 — self-contained but non-trivial:**

3. **Ch4 4.12.8** (`Problem4_12_8.lean`, 1 sorry): classification of finite
   subgroups of SO(3)/SU(2). A substantial group-theory statement despite the
   single sorry, but 4.12.7 (its SU(2)/SO(3) prerequisite) is now fully proved,
   which unblocks the geometry.
4. **"Complete the `statement_formalized` residue"** — the 5 items kept
   `statement_formalized` this window are each *one honest gap* away from
   `sorry_free`, and each gap is a well-scoped follow-up: 6.1.6(d) group↔diagram
   correspondence, 9.4.6(ii) discharge `hcover`, 9.5.3(iii) blocks of k[S₃] in
   char 2, 2.16.5 the actual U_q(sl₂) classification, 4.12.11(b) complexified
   irreducibility. These are high-value because they convert "looks done" into
   "is done". 9.5.3(iii) and 4.12.11(b) look the most tractable; 2.16.5 is the
   deepest (a genuine classification, not a lemma).

**Tier 3 — deep; do not mistake a low sorry count for low effort:**

5. **Ch8 8.2.8 Tor/Künneth** (2 + 1 sorries, chain #6657/#6727/#6729) — the
   restriction-of-scalars commutation iso + Ch7 Künneth; already decomposed but
   blocked on a `Module k` instance diamond (#6742/#6747).
6. **Ch5 5.24.2 FFT core** (`Problem5_24_2_Bridge.lean`, 1 sorry) — Schur–Weyl /
   double-centralizer First Fundamental Theorem; the deepest single sorry in the
   tree. Needs decomposition.
7. **Ch5 5.24.1(b)** (`Problem5_24_1_b.lean`, 5 sorries incl. one in-definition
   obligation) — `V'_λ ≅ V_λ` and `V_λ ⊗ C₋ ≅ V_{λ*}` for the symmetric group.
8. **Ch6 Dynkin/lattice block** (14 sorries across the two 6.1.3-continued files) —
   E7/E8 and affine-Ẽ Cartan/root-system combinatorics. Largest chapter block;
   genuinely hard, though 6.9.2 (E8 lattice) and 6.1.6 (McKay) both cleared this
   window, so the block is no longer monolithic.

## Method notes

- Counts are comment-stripped genuine sorries against `origin/main` HEAD
  `a78b010b`; the reproducer command above is authoritative.
- `proof_wanted` gaps (2 files) and the two in-definition obligations
  (`Problem5_24_1_b.lean:57`, `ExternalTensorResolution.lean:102`) are *not*
  counted in the 27 but are real unproved surface — noted for honesty.
- **Status reconciliation was blob-audited, not mechanical.** The prior rule
  "`statement_formalized` + sorry-free source → `sorry_free`" would have wrongly
  flipped 5 of 11 candidates whose files are sorry-free but do not fully formalize
  their book problem (crux-as-hypothesis, `Prop`-def-only, or unstated parts). The
  552 `sorry_free` count therefore reflects *audited* completeness for the 6
  corrected items; it does not certify that every one of the 552 pre-existing
  `sorry_free` items is free of the same "sorry-free but incomplete" pattern — a
  full re-audit of all 552 was out of scope. Future summarize sessions should keep
  applying the blob check rather than trusting the sorry counter alone.
- Merged-PR list obtained via
  `gh pr list --state merged --json number,title,mergedAt` filtered to
  `mergedAt > 2026-07-13T14:53:19Z` (115 results).

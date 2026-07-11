# Sorry Landscape Analysis — post-32-merge refresh

Generated 2026-07-11 03:21 UTC by summarize session (issue #6434, branch
`agent/2130d40a`) against `origin/main` at HEAD `03cddff5`. **Supersedes
`progress/2026-07-11T00-49-00Z-sorry-landscape.md`** (issue #6358, HEAD
`5d7d16f9`), which reported **108 genuine sorries in 30 files**; the current
count is **90 in 29 files**. Since that snapshot closed (2026-07-11 01:01:50Z),
**32 PRs merged to `main`** across Chapters 2, 3, 4, 5, 7, 8, 9 (plus three
skill/chore PRs), thinning the frontier by 18 sorries.

## Headline: 90 genuine sorries across 29 files, spread over Chapters 2–9

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **90 genuine proof-gap `sorry`
tactics in 29 files** — down from 108/30. There are **no `axiom` declarations
and no `admit`s** (every `axiom`/`admit` string hit is English prose inside
docstrings, e.g. "admit a unitary structure", "Module axiom helpers"). Two files
record book-unproved statements via **`proof_wanted`** rather than `sorry`
(`Chapter2/Remark2_9_3.lean` — Ado's theorem; `Chapter5/Remark5_23_3.lean`);
these are genuine gaps that the comment-stripped `sorry` counter does **not**
see, so "90 sorries" slightly understates the unproved surface.

Reproduce the headline count (comment-stripping `awk` depth-counter, then
whole-word `sorry` on surviving code) against a clean `origin/main` checkout:
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 90 across 29 files at HEAD 03cddff5
```

### items.json status distribution (592 items)

After this session's status reconciliation (see "Status corrections" below):

| Status | Count |
|--------|------:|
| `sorry_free` | 542 |
| `statement_formalized` | 28 |
| `accepted` | 6 |
| `formalized` | 4 |
| `proved` | 4 |
| `proof_complete` | 3 |
| `partially_formalized` | 2 |
| `sorry` | 1 |
| `non_formalizable` | 1 |
| `partially_proved` | 1 |
| **total** | **592** |

Reproduce:
```bash
python3 -c "import json,collections; d=json.load(open('progress/items.json')); \
print(collections.Counter(it.get('status') for it in d))"
```

### Per-chapter picture

Columns: total items, `sorry_free`, `statement_formalized`, other statuses, and
**genuine sorries in the Lean source** (comment-stripped; may differ from the
`statement_formalized` count because one item can span several sorried helper
files, and a few multi-part items are still `statement_formalized` while one of
their files is sorry-free).

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/derived) | 15 | 6 | 1 | 8 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 117 | 109 | 4 | 4 | 7 |
| 3 | 58 | 56 | 2 | 0 | 9 |
| 4 | 60 | 53 | 3 | 4 | 5 |
| 5 | 157 | 146 | 7 | 4 | 22 |
| 6 | 64 | 59 | 4 | 1 | 31 |
| 7 | 59 | 59 | 0 | 0 | 0 |
| 8 | 24 | 20 | 3 | 1 | 9 |
| 9 | 35 | 31 | 4 | 0 | 7 |
| **total** | **592** | **542** | **28** | **22** | **90** |

Per-chapter genuine-sorry tally (from the per-file counts):
Ch2 = 7 (`2_16_5`:3, `2_16_4`:2, `2_16_3`:1, `2_7_5`:1),
Ch3 = 9 (`3_9_5`:5, `3_8_5`:4),
Ch4 = 5 (`4_12_11`:3, `4_12_8`:1, `4_12_7`:1),
Ch5 = 22 (`5_11_1`:9, `5_24_1_b`:5, `Ex5_27_3`:2, `5_24_2`/`5_16_3`/`5_1_2`/`Ex5_27_2_{Heisenberg,Dihedral,Affine}`:1 each),
Ch6 = 31 (`6_1_3_E7_E8`:13, `6_9_2`:8, `6_1_6`:5, `6_1_3_tildeE`:5),
Ch7 = 0, Ch8 = 9 (`8_2_7`:4, `8_2_6`:3, `8_2_8`:2),
Ch9 = 7 (`9_4_6`:3, `9_5_3`:2, `9_6_5`:1, `9_4_5`:1).

## What changed since 2026-07-11 00:49 (the 32 merges that landed)

By chapter (only threads that moved):

- **Chapter 2 — 8 → 7 sorries.** Problem 2.16.3(b) `not_finiteDimensional_g_four`
  is now **fully proved**: the char ≠ 3 twisted-loop witness (#6402), the char = 3
  witness (`sl₃`-loop collapses mod 3, new representation needed, #6417), the
  reduction infra (#6390), and the final char-case split (#6431) all landed.
  Chapter 2's remaining 7 sorries are Problems 2.16.4/2.16.5 (char-p Lie infra,
  2+3) and the single-sorry 2.7.5 (q-Weyl centre) and 2.16.3 residual (1).
- **Chapter 3 — 15 → 9.** Problem 3.8.5 closure obligations discharged so
  `periodicSubalg`/`antiperiodicSubmod` are genuine objects (#6430); the four
  Krull–Schmidt-failure theorems (Möbius/Picard argument) remain (4 sorries).
  Problem 3.9.5 (Clifford, 5) unchanged.
- **Chapter 4 — 11 → 5.** Problem 4.12.11 SO(3) elasticity gained its invariant
  decomposition `End(V)=ℝ⊕V⊕W`, `S²V=ℝ⊕W` with dims 1,3,5 (#6365); 3 sorries
  remain there, plus one each in 4.12.7(f) (SU(2)→SO(3) surjection) and 4.12.8
  (finite SO(3)/SU(2) subgroup classification).
- **Chapter 5 — 23 → 22.** The 5.1.2(a) End-algebra type-iso chain **fully
  landed**: complex (prior), real `End_ℝ[G]V ≃ₐ Mat₂(ℝ)` (#6391) and
  quaternionic `≃ₐ ℍ` (#6418), plus the `j`-operator helpers (#6380). The 5.16.3(b)
  branching bridge (#6393) and "modulo combinatorics" assembly (#6427) landed;
  the residual combinatorial `sorry` (D3, content/corner) is issue #6424.
  Exercise 5.27.3 part (i) irreducibility landed (#6428/#6397); parts (ii)+(iii)
  are open (#6426, #6396). Problem 5.11.1 (A₅ induced reps, 9) unchanged; the
  bulk of Ch5's 22 is 5.11.1 (9) + 5.24.1(b) (5).
- **Chapter 6 — 31 → 31 (unchanged, largest block).** No Ch6 merges this window.
  The 31 sorries are the Dynkin/affine/lattice classifications: 6.1.3-cont E7/E8
  (13), 6.9.2 E8 lattice (8), 6.1.6 McKay (5), 6.1.3-cont tilde-E (5).
- **Chapter 7 — 1 → 0. Fully sorry-free.** Problem 7.8.7 Künneth final assembly
  landed (#6364), closing the last Ch7 sorry.
- **Chapter 8 — 9 → 9 (net unchanged).** The bar-resolution chain advanced:
  `barComplex` with `d∘d=0` assembled (#6401) and the augmentation chain map
  `barπChainMap` (ε∘d₀=0, #6416) landed, but the remaining Problem 8.2.6/8.2.7/8.2.8
  sorries (3/4/2) — exactness/packaging, higher Tor/Ext, projective-lift — persist.
- **Chapter 9 — 10 → 7.** Heavy homological-dimension + block-theory activity:
  9.4.5 `homologicalDimension(k[t]/tⁿ)=⊤` via 2-periodic syzygy (#6400/#6394),
  9.4.6 Cartan-matrix packaging (#6377/#6411/#6422), and the 9.5.3 block-linking
  chain — block orthogonality (#6363), Ext¹-vanishing base case (#6407),
  split-from-Ext¹-vanishing (#6409), and the dévissage `ext_subsingleton` (#6413).
  Remaining: 9.4.6 (3), 9.5.3 (2), 9.4.5 (1), 9.6.5 Morita quasi-inverse (1).

## Active frontier — in-flight chains a planner should keep sequencing

1. **Ch5 Exercise 5.27.3** completeness: part (ii) pairwise non-iso (#6426) →
   part (iii) sum-of-squares dimension count (#6396, depends on ii). Part (i)
   already merged.
2. **Ch5 5.16.3(b)** last combinatorial sorry: #6424 (content-constant ⇔
   rectangular; corner/content combinatorics).
3. **Ch8 bar resolution → Ext** (Problem 8.2.6): `barComplex` + augmentation now
   on `main`; next is exactness/packaging → `Ext¹ ≃ cocycle Ext¹`.
4. **Ch9 blocks** (9.5.3ii): `compositionFactors_areLinked` assembly (#6405) from
   the merged dévissage + splitting infra.
5. **Ch2 2.7.5**: q-Weyl centre at a root of unity (#6437, single sorry).
6. **Ch5 Exercise 5.27.2** classification trio (#6435 dihedral; Heisenberg/affine).

## Biggest single-file proof targets (by genuine sorry count)

High count ≠ high priority — most are self-contained multi-part problems — but
these are the largest remaining chunks:

| sorries | file | item |
|--------:|------|------|
| 13 | `Chapter6/Problem6_1_3_continued_E7_E8.lean` | E7/E8 Dynkin-diagram parts |
|  9 | `Chapter5/Problem5_11_1.lean` | decompose induced reps from subgroups of A₅ |
|  8 | `Chapter6/Problem6_9_2.lean` | E8 lattice and root systems |
|  5 | `Chapter6/Problem6_1_6.lean`, `Chapter6/Problem6_1_3_continued_tildeE.lean`, `Chapter5/Problem5_24_1_b.lean`, `Chapter3/Problem3_9_5.lean` | McKay graph, affine Dynkin, Problem 5.24.1(b), Clifford |
|  4 | `Chapter8/Problem8_2_7.lean`, `Chapter3/Problem3_8_5.lean` | higher Tor/Ext; Krull–Schmidt failure |
|  3 | `Chapter9/Problem9_4_6.lean`, `Chapter8/Problem8_2_6.lean`, `Chapter4/Problem4_12_11.lean`, `Chapter2/Problem2_16_5.lean` | Cartan matrix, bar resolution, elasticity, Lie char-p |

## Ranked shortlist of tractable next targets

Single-sorry files are the cheapest wins; several reuse infrastructure that
already landed. Ranked by tractability × value, with honesty about which
"single sorry" hides real depth:

1. **`Chapter2/Problem2_7_5.lean`** — `center_of_isOfFinOrder` (q-Weyl centre at a
   root of unity). Mirrors merged 2.7.4c dimension work. Open as #6437. *Cheap.*
2. **`Chapter5/Exercise5_27_2_{Dihedral,Affine,Heisenberg}.lean`** — three
   classification theorems, one sorry each; the Chapter-4 inputs (4.12.1(a),
   4.12.2, 4.12.6) are proved. Good parallel throughput. Dihedral is #6435.
   *Moderate — the orbit-method classification is real work but self-contained.*
3. **`Chapter5/Problem5_24_2.lean`** — `invariantSubalgebra_eq_adjoin_traceWord`,
   one self-contained theorem. *Moderate.*
4. **`Chapter5/Exercise5_27_3.lean`** (2 sorries) — parts (ii)+(iii); part (iii)
   is a sum-of-squares completeness count reusing Theorem 5.27.1's strategy.
   *Moderate; (iii) depends on (ii).*
5. **`Chapter5/Problem5_16_3.lean`** — last sorry #6424 (corner/content
   combinatorics). *Moderate combinatorics.*
6. **`Chapter4/Problem4_12_7.lean`** — part (f) `exists_surjective_hom_to_SO3`
   (SU(2)→SO(3) double cover). *Deep — do not mistake for cheap.*
7. **`Chapter9/Problem9_6_5.lean`** — `exists_quasiInverse_tensor_functor`
   (Morita, Theorem 9.6.4). Single sorry but **genuinely deep**.
8. **`Chapter5/Problem5_24_2.lean` / `Problem5_1_2.lean`** residuals. *Mixed.*

Deliberately **not** "tractable": `Chapter4/Problem4_12_8.lean` (finite subgroups
of SO(3)/SU(2) — the full ADE classification behind one sorry),
`Chapter5/Problem5_24_2.lean`'s FFT/Schur–Weyl flavour where applicable, and the
multi-sorry Chapter-6 Dynkin/lattice files (large combinatorial efforts).

## Status corrections applied this session

Policy: promote an item to `sorry_free` **only** when (a) its current status
signals an *incomplete proof* (`statement_formalized` or `proof_partial`),
(b) *all* Lean files covering the item have 0 genuine sorries, (c) no covering
file uses `proof_wanted`, and (d) no sibling file for the same problem carries a
sorry. This targets exactly the planner-misleading "still has work" statuses
while refusing to guess about terminal-vocab or coverage-partial statuses.

**7 items upgraded** `statement_formalized`/`proof_partial` → `sorry_free`
(count 535 → 542; `statement_formalized`/`proof_partial` drained accordingly):

| id | old status | evidence |
|----|-----------|----------|
| `Chapter7/Problem7.8.7` | statement_formalized | Künneth assembly landed (#6364); file sorry-free |
| `Chapter2/Problem2.7.4` | proof_partial | file sorry-free, no `proof_wanted` |
| `Chapter3/Remark3.1.3` | proof_partial | file sorry-free |
| `Chapter4/Remark4.5.3` | proof_partial | file sorry-free |
| `Chapter5/Remark5.2.8` | proof_partial | file sorry-free |
| `Chapter5/Theorem5.23.2` | proof_partial | all three `Theorem5_23_2*` files sorry-free, none `proof_wanted` |
| `Chapter9/Introduction_9.7` | proof_partial | both `Introduction_9_7*` files sorry-free |

**Left unflipped (audit candidates), files sorry-free but status not
`sorry_free`** — deliberately not guessed at, matching the prior session's
caution:

- **Terminal-vocab items** whose status already asserts completion but uses a
  legacy word: `proved` (`Chapter4/Problem4.12.6`, `Chapter4/Problem4.12.9`,
  `Chapter5/Exercise5.3.3`, `Chapter8/Example8.1.7`), `proof_complete`
  (`Chapter2/Problem2.13.1`, `Chapter4/Theorem4.6.2`,
  `Chapter4/Discussion_after_Theorem4.6.2`), `formalized`
  (`Chapter2/Problem2.3.16`). These do not mislead a planner (they signal done);
  normalizing all 8 to `sorry_free` would move the count to ~550. A schema owner
  should decide whether `sorry_free` is canonical.
- **`Chapter6/Problem6.9.3`** (`partially_proved`) and the `accepted`
  `Chapter5/Discussion5_11_S4S3` — file sorry-free, but `partially_proved`/
  `accepted` may signal a *coverage* gap (statements omitted, not sorried), which
  the sorry counter cannot see. Left for a human/planner audit.
- **`Chapter5/Problem5.24.1`** (`statement_formalized`) — its own file is
  sorry-free but the sibling `Problem5_24_1_b.lean` carries **5 sorries**, so the
  item is genuinely incomplete. Correctly left as `statement_formalized`.
- One `statement_formalized` item with **no `id`/`title`** points at
  `Chapter5/GL2ConjugacyClassCount.lean` (sorry-free). Left untouched: editing a
  malformed entry blind is riskier than the drift it fixes; flagged here instead.
- **`Chapter2/Remark2.9.3`** keeps status `sorry` — it records Ado's theorem via
  `proof_wanted` (book-unproved, not in Mathlib). This is intentional, not a gap
  the counter should "fix". Same for `Chapter5/Remark5_23_3.lean`.

The reverse direction is clean: every one of the 29 sorry-bearing files maps to
an item still marked `statement_formalized` (or a multi-part item), so no
`sorry_free` item hides a genuine `sorry`.

## One-glance status

- **Genuine sorries:** 90 in 29 files, Chapters 2–9. **Axioms/admits:** 0.
  **`proof_wanted` (unproved, sorry-invisible):** 2 files (Remark 2.9.3, 5.23.3).
- **`items.json`:** 542 sorry_free / 28 statement_formalized / 22 other of 592
  (after +7 corrections this session).
- **Frontier shape:** still broad-and-shallow, thinning steadily. No single deep
  crux; the largest concentration is Chapter 6 Dynkin/lattice combinatorics
  (31 sorries, unchanged — a good candidate for a dedicated planner push).
  **Chapter 7 is now fully sorry-free.**
- **Active in-flight chains:** Ch5 5.27.3 ii/iii (#6426→#6396), Ch5 5.16.3b
  #6424, Ch8 bar resolution → Ext, Ch9 9.5.3ii #6405, Ch2 2.7.5 #6437, Ch5
  5.27.2 trio (#6435 +).
- **Cheapest next wins:** single-sorry files — Ch2 2.7.5, Ch5 Exercise 5.27.2
  trio, 5.24.2 (see shortlist). Note 4.12.7(f) and 9.6.5 are single-sorry but
  **deep**.
- **Main health:** no evidence `main` is broken; auto-merge cadence intact
  (32 PRs in ~2.3 hours of window).
</content>
</invoke>

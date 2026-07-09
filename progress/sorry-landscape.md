# Sorry Landscape Analysis — broad statement-pass proof-fill wave

Generated 2026-07-09 04:01 UTC by summarize session (issue #6003, branch
`agent/306db375`) at HEAD `c761a482` ("Fix PathAlgebra abbrev leaking
Finsupp.instMul", #5995). **Supersedes the 2026-06-22 snapshot**, which was
completely obsolete: it described a "4 real sorries, all in Chapter 5"
Schur-Weyl endgame that no longer exists. Since then **200+ PRs merged** (the
`gh` merged-PR window since 2026-06-22 is saturated at its 200 cap), the entire
Chapter 5 Schur-Weyl / Specht crux was resolved, and the project ran a broad
**statement pass** that formalized theorem *statements* across every chapter
with their proofs left as `sorry`. The frontier is now wide and shallow, not
narrow and deep.

## Headline: 254 genuine sorries across 74 files, spread over Chapters 2–9

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **254 genuine proof-gap `sorry`
tactics in 74 files**. There are **no `axiom` declarations and no `admit`s**.
This is the opposite shape from the last snapshot: instead of 4 deep cruxes in
one chapter, we have a broad backlog of formalized-but-unproved exercises and
problems distributed across the whole book.

> **The old Schur-Weyl narrative is dead.** Every item the 2026-06-22 doc
> flagged is gone from the sorry list: `CauchyDetQuotient`,
> `SchurWeylFormalCharacterIso`, `SchurWeylSimplesClassification`,
> `SpechtModuleBasis` are all sorry-free now. Threads A/B/C/D and the
> in-flight PRs it tracked (#4997, #5021/#5022 "broken main", #4946/#4976,
> #4721/#4994) have all landed or closed. Do not chase them.

### items.json status distribution (592 items)

| Status | Count |
|--------|------:|
| `sorry_free` | 494 |
| `statement_formalized` | 73 |
| `proof_partial` | 8 |
| `accepted` | 6 |
| `formalized` | 4 |
| `proof_complete` | 2 |
| `partially_formalized` | 2 |
| `proved` | 1 |
| `sorry` | 1 |
| `non_formalizable` | 1 |
| **total** | **592** |

Reproduce:
```bash
python3 -c "import json,collections; d=json.load(open('progress/items.json')); \
print(collections.Counter(it.get('status') for it in d))"
```

### Per-chapter picture

Columns: total items, `sorry_free`, `statement_formalized`, other statuses, and
**genuine sorries in the Lean source** (comment-stripped, may exceed the
`statement_formalized` count because one item can span several sorried helper
lemmas or files).

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/derived) | 15 | 6 | 1 | 8 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 117 | 102 | 11 | 4 | 43 |
| 3 | 58 | 49 | 6 | 3 | 33 |
| 4 | 60 | 44 | 13 | 3 | 46 |
| 5 | 157 | 135 | 17 | 5 | 36 |
| 6 | 64 | 58 | 6 | 0 | 36 |
| 7 | 59 | 54 | 5 | 0 | 9 |
| 8 | 24 | 15 | 8 | 1 | 36 |
| 9 | 35 | 28 | 6 | 1 | 15 |
| **total** | **592** | **494** | **73** | **25** | **254** |

Genuine-sorry counting method (an `awk` `/- … -/` depth counter that also
truncates at `--`, then whole-word `sorry` on surviving code only):
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 254 across 74 files
```
A bare `grep -rc sorry` is still misleading here (the project documents where
sorries are and are not in prose), but the noise factor is far smaller than in
the last era because the sorries are now real code, not comment references.

## The frontier: a top-down statement pass awaiting proof fill

The dominant pattern is exactly the top-down development the project prescribes:
statements were pushed out project-wide (many via the "Statement pass" PRs
#5954/#5955 and the Chapter-2/3/4 waves), and the proofs are now the work. The
73 `statement_formalized` items are the primary worker queue. There is **no
single deep crux** blocking everything; most items are independent and
worker-sized.

### Biggest single-file proof targets (by genuine sorry count)

These are the files where the most proof work is concentrated. High count does
not mean high priority — some are self-contained multi-part problems — but they
are the largest chunks:

| sorries | file | item |
|--------:|------|------|
| 16 | `Chapter8/Problem8_2_7.lean` | Tor/Ext for abelian groups & polynomial modules |
| 13 | `Chapter6/Problem6_1_3_continued_E7_E8.lean` | E7/E8 Dynkin-diagram parts |
| 11 | `Chapter5/Problem5_11_1.lean` | decompose induced reps from subgroups of A5 |
| 10 | `Chapter3/Problem3_8_5.lean` | failure of Krull–Schmidt (infinite-dim) |
|  9 | `Chapter4/Problem4_12_11.lean` | elasticity / Hooke's law application |
|  9 | `Chapter2/Problem2_8_6.lean` | path-algebra generators & relations |
|  8 | `Chapter8/Problem8_2_6.lean` | properties of Tor and Ext |
|  8 | `Chapter6/Problem6_9_2.lean` | E8 lattice and root systems |
|  8 | `Chapter2/Problem2_8_11.lean` | Hilbert series of graded algebras |
|  6 | `Chapter4/Problem4_12_2/_6.lean`, `Chapter3/Problem3_9_5.lean`, `Chapter2/Problem2_7_5.lean` | Heisenberg / affine-group reps, Clifford algebra, q-Weyl algebra |

### The 73 `statement_formalized` backlog by chapter

Full list so planners can target the next feature waves. Reproduce with:
```bash
python3 -c "import json,re,collections; d=json.load(open('progress/items.json')); \
print([it['id'] for it in d if it.get('status')=='statement_formalized' and it.get('id')])"
```

- **Chapter 2 (11):** Problem2.7.5, 2.8.6, 2.8.11, Exercise2.9.11, Problem2.13.1,
  2.14.3, 2.16.1, 2.16.2, 2.16.3, 2.16.4, 2.16.5.
  Themes: q-Weyl algebra, path algebras, Hilbert series, Lie's theorem, sl(2) in
  char p, quantum U_q(sl(2)).
- **Chapter 3 (6):** Problem3.8.4 (Noether–Deuring), 3.8.5 (Krull–Schmidt
  failure), 3.9.2, 3.9.3, 3.9.4 (formal deformations), 3.9.5 (Clifford algebra).
  Ext¹ / deformation cluster.
- **Chapter 4 (13):** Exercise4.2.3, 4.3.1, Problem4.5.2, 4.12.1 (dihedral),
  4.12.2 (Heisenberg), 4.12.4, 4.12.5 (A5 on icosahedron), 4.12.6 (affine group),
  4.12.7 (SU(2)/SO(3)), 4.12.8 (finite subgroups of SO(3)/SU(2)), 4.12.9, 4.12.10,
  4.12.11 (elasticity). The §4.12 problem set is the bulk.
- **Chapter 5 (17):** Problem5.1.2, Example5.1.3, Exercise5.1.7, 5.3.3,
  Problem5.8.4 (induction transitivity), Exercise5.8.5, Theorem5.9.1 (Frobenius
  formula), Problem5.11.1, 5.12.5, 5.16.1–3 (branching, Young-diagram content),
  Proposition5.22.2, Problem5.24.1, 5.24.2, Exercise5.27.2, 5.27.3.
- **Chapter 6 (6):** Problem6.1.3 (+E7_E8, +tildeE continuations), 6.1.6 (McKay
  graph), 6.9.2 (E8 lattice), 6.9.3 (Ext / Jordan–Hölder for Dynkin quivers).
- **Chapter 7 (5):** Problem7.7.3, Exercise7.8.4 (exact sequences split),
  Problem7.8.5 (long exact sequence), 7.8.7 (Künneth), Exercise7.9.8 (reflection
  functors adjoint pair).
- **Chapter 8 (8):** Problem8.1.3 (flat modules), Exercise8.1.4, 8.2.2
  (projective resolutions exist), Problem8.2.5, 8.2.6, 8.2.7, 8.2.8, Exercise8.2.9.
  The Tor/Ext homological-algebra core.
- **Chapter 9 (6):** Problem9.4.2, 9.4.5, 9.4.6 (homological dimension / Cartan
  matrix), 9.5.3 (blocks & central idempotents), Exercise9.6.3, Problem9.6.5
  (Theorem 9.6.4 via quasi-inverse functors).

### Prioritisation guidance (mathematical, not graph-derived)

The `dependencies/internal.json` graph is still the **conservative linear chain**
(every item has in-degree ≈1 — per CLAUDE.md, transitive/real deps are trimmed
later), so it yields no useful "most-depended-on" ranking. Prioritise instead by
mathematical foundation:

1. **Chapter 7–8 homological-algebra infrastructure first.** Exercise7.8.4
   (exact sequences of vector spaces split), Exercise8.2.2 (existence of
   projective resolutions), Problem8.2.5 (Tor/Ext independence of resolution) are
   the substrate the rest of Chapters 8–9 (Tor/Ext computations, homological
   dimension, Cartan matrices) build on. Proving these unblocks the widest
   downstream set even though the linear-chain graph doesn't show it.
2. **Chapter 4 §4.12 group-representation problems** are numerous and mostly
   self-contained (dihedral, Heisenberg, SU(2)/SO(3)); good parallel throughput.
   Note Chapter 5 Exercise5.27.2 explicitly "redoes 4.12.1(a), 4.12.2, 4.12.6",
   so proving those Chapter 4 items first is the natural order.
3. **Chapter 2 algebra-structure problems** (path algebras #2.8.6, Hilbert series
   #2.8.11, q-Weyl #2.7.5) are independent and sized for one session each.

## Known-good infrastructure landed recently

- **PathAlgebra `*` scoping fix (#5987 → #5995, at current HEAD).** A reducible
  `abbrev` over `Finsupp` was leaking `Finsupp.instMul` (pointwise multiplication)
  and hijacking `*` in downstream files, silently falsifying Problem 2.8.6
  relations (3),(4). Fixed in #5995 (the HEAD commit). This is the latest
  statement-fidelity landmine class the project watches for (cf. the `/review`
  focus on statement fidelity — issue #5998).
- Chapter 2 tensor-product / base-change items landed with partial proofs:
  Problem 2.11.3(a)(b)(c)(g) (#5993), Exercise 2.11.5 (#5994) — under review in
  #5998. Problem 2.7.4(b) (x^p, y^p central in the char-p Weyl algebra, #5989).

## Status-vs-source discrepancies (for planners to reconcile)

Cross-checking `items.json` status against actual comment-stripped sorry counts
surfaced items whose recorded status lags the source. **None** of the 494
`sorry_free` items has a hidden sorry (clean — verified by id→file match). The
mismatches are all in the *conservative* direction (status understates progress):

**`statement_formalized` items whose file is now sorry-free — verify not
vacuous, then upgrade to `sorry_free`:**
- `Chapter2/Exercise2.9.11` (`Exercise2_9_11.lean`)
- `Chapter5/Example5.1.3` (`Example5_1_3.lean`)
- `Chapter5/Theorem5.9.1` (`Theorem5_9_1.lean` — Frobenius formula)
- `Chapter5/Proposition5.22.2` (`Proposition5_22_2.lean`)

**Other-status items whose file is sorry-free — candidates to mark `sorry_free`:**
- `Chapter2/Problem2.3.16` (`formalized`), `Chapter3/Remark3.1.3`,
  `Chapter4/Remark4.5.3`, `Chapter4/Theorem4.6.2` (`proof_complete`),
  `Chapter4/Discussion_after_Theorem4.6.2`, `Chapter5/Remark5.2.8`,
  `Chapter5/Theorem5.23.2`, `Chapter8/Example8.1.7` (`proved`),
  `Chapter9/Introduction_9.7`.

**Accurately still-partial** (proof_partial with real sorries): Problem2.7.4
(4), Problem3.3.3 (3), Problem3.9.1 (2). `Chapter2/Remark2.9.3` (Ado's theorem)
carries status `sorry` but has no genuine sorry in source — it is a
statement/discussion the book itself leaves unproved; treat as intentional, not
a gap.

Three `statement_formalized`/`formalized` items map to no single obvious file
(`Chapter5/Problem5.2.7`, `Chapter5/Problem5.10.2`,
`Chapter5/Discussion_Problem5.10.2_parts`) — they live in differently-named or
multi-part files and were not auto-matched; a planner should locate them by hand.

## One-glance status

- **Genuine sorries:** 254 in 74 files, across Chapters 2–9. **Axioms/admits:** 0.
- **`items.json`:** 494 sorry_free / 73 statement_formalized / 25 other of 592.
- **Frontier shape:** broad statement-pass proof-fill wave, no single deep crux.
  Every item is roughly worker-sized; most are independent.
- **Highest-leverage next work:** Chapter 7–8 homological-algebra foundations
  (Exercise7.8.4, Exercise8.2.2, Problem8.2.5), then Chapter 4 §4.12 group-rep
  problems, then Chapter 2 algebra-structure problems.
- **Main health:** no evidence `main` is broken — the last *completed* CI run on
  `main` succeeded (2026-07-08 04:01 UTC); later runs are the usual
  rapid-merge cancellations, with one run in progress at snapshot time. (The
  2026-06-22 "main is broken / #5022" emergency is long resolved.)
- **Bookkeeping:** ~13 items are proved-but-mislabeled (see discrepancies
  above); reconciling them would move the `sorry_free` count from 494 toward 507.
</content>

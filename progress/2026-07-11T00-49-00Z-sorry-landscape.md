# Sorry Landscape Analysis — proof-fill wave, mid-frontier

Generated 2026-07-11 00:49 UTC by summarize session (issue #6358, branch
`agent/6a743b93`) at HEAD `5d7d16f9` ("land progress-handoff PR after
decompose-and-exit", #6361). **Supersedes `progress/sorry-landscape.md`** (the
2026-07-09 04:01 UTC snapshot at HEAD `c761a482`, issue #6003), which is now
badly stale: it reported **254 genuine sorries in 74 files**; the current count
is **108 in 30 files**. Since that snapshot **170 PRs merged to `main`** (26 on
2026-07-09, 136 on 2026-07-10, 8 on 2026-07-11) — the broad "statement pass"
backlog it described has been proof-filled at scale across every chapter.

## Headline: 108 genuine sorries across 30 files, spread over Chapters 2–9

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **108 genuine proof-gap `sorry`
tactics in 30 files** — down from 254/74. There are **no `axiom` declarations
and no `admit`s** (the only `axiom`/`admit` string hits are English prose inside
docstrings). The frontier is still broad-and-shallow rather than one deep crux,
but it has thinned dramatically: 44 of the 74 previously-sorried files are now
sorry-free, and the remaining sorries concentrate in a handful of genuinely
combinatorial or homological multi-part problems.

### items.json status distribution (592 items)

After this session's status reconciliation (see "Status corrections" below):

| Status | Count |
|--------|------:|
| `sorry_free` | 535 |
| `statement_formalized` | 29 |
| `proof_partial` | 6 |
| `accepted` | 6 |
| `formalized` | 4 |
| `proved` | 4 |
| `proof_complete` | 3 |
| `partially_formalized` | 2 |
| `partially_proved` | 1 |
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
**genuine sorries in the Lean source** (comment-stripped; may differ from the
`statement_formalized` count because one item can span several sorried helper
lemmas or files, and a few multi-part items are still `statement_formalized`
while their file is sorry-free).

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/derived) | 15 | 6 | 1 | 8 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 117 | 108 | 4 | 5 | 8 |
| 3 | 58 | 55 | 2 | 1 | 15 |
| 4 | 60 | 52 | 3 | 5 | 11 |
| 5 | 157 | 144 | 7 | 6 | 23 |
| 6 | 64 | 59 | 4 | 1 | 31 |
| 7 | 59 | 58 | 1 | 0 | 1 |
| 8 | 24 | 20 | 3 | 1 | 9 |
| 9 | 35 | 30 | 4 | 1 | 10 |
| **total** | **592** | **535** | **29** | **28** | **108** |

Genuine-sorry counting method (an `awk` `/- … -/` depth counter that also
truncates at `--`, then whole-word `sorry` on surviving code only):
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 108 across 30 files
```

## What changed since 2026-07-09 (the threads that landed)

The 170 merges resolved most of the statement-pass backlog. By chapter:

- **Chapter 2 — down to 8 sorries.** The Problem 2.8.11 Hilbert-series suite
  landed in full (free/exterior/polynomial-algebra series #6268/#6272/#6278, and
  #6262 path-count = adjacency-power); q-Weyl dimension #6320. The `𝔤ₙ` positive
  nilpotent `finrank` chain (Problem 2.16.3a) proved n=1,2,3 (#6341/#6348/#6339);
  n=4 (infinite-dimensional, affine) is the in-flight #6359.
- **Chapter 3 — down to 15.** Problem 3.9.2 formal-deformation cluster landed
  (Ext¹ computations #6277/#6287, infinitely-many-indecomposables #6258); Clifford
  algebra of the zero form ≅ ⋀V (#6280). Remaining bulk is Problem 3.8.5
  (Krull–Schmidt failure, 10 sorries) and 3.9.5 (5).
- **Chapter 4 — down to 11.** The §4.12 group-rep set was proof-filled heavily:
  Problem 4.12.5 A₅/icosahedral decomposition engine and all four
  vertices/edges/faces decompositions + dimension table + completeness
  (#6241/#6251/#6252/#6264/#6270/#6293/#6296/#6322); affine group irreducibility
  and dimension (#6236/#6303/#6316); SU(2) real irreducibility + quaternion
  facts + SU(2)≅unit-quaternions (#6250/#6288); Heisenberg characters (#6257).
  Remaining: Problem 4.12.11 (elasticity, 9), plus one sorry each in 4.12.7(f)
  and 4.12.8 (finite SO(3)/SU(2) subgroup classification — deep).
- **Chapter 5 — down to 23.** Frobenius–Schur / Schur-dichotomy machinery
  landed (real-or-quaternionic dichotomy #6238, the ∑χ(g²)=|G| crux #6261,
  odd-order no-quaternionic #6249, Exercise 5.1.7 #6302). Problem 5.12.5 (all Sₙ
  irreps real) #6259. Problem 5.11.1 A₅ induced reps: indZ2_triv/indZ2_sign
  landed (#6292/#6305) but the file still carries 9 sorries. Problem 5.16.1
  branching is **fully proved** now (both restriction #6321 and induction #6301
  character identities) — note issue #6286's claim that "5.16.1 proofs are sorry"
  is stale. Problem 5.16.3a integer-content-eigenvalue core landed
  (#6290/#6313/#6338). **In-flight:** the 5.1.2 End-algebra type-iso chain
  (complex case #6350 merged; real #6327 and quaternionic #6328 open), and the
  module-level `Sₙ↓Sₙ₋₁` branching needed for 5.16.3b (#6356 general
  character⇒multiplicity bridge → #6357 C_{n-1} spectrum → #6286).
- **Chapter 6 — down to 31, the largest remaining block.** Cartan-matrix basics
  (#6256) and McKay-multiplicity symmetry (#6325) landed, and Problem 6.9.3(a)
  Ext-vanishing at sources/sinks (#6289). The 31 sorries are the Dynkin/affine
  combinatorial classifications: Problem 6.1.3 continued E7/E8 (13),
  Problem 6.9.2 E8 lattice/root system (8), Problem 6.1.6 McKay graph (5),
  6.1.3 continued tilde-E (5).
- **Chapter 7 — down to 1.** Problem 7.8.7 Künneth: parts (ii) acyclic-tensor
  (#6309), (iii) field-splitting (#6275), and (iv) zero-diff tensor homology
  (#6349) + biproduct distributor (#6352) all landed. The single remaining sorry
  is the final assembly Problem_7_8_7_iv, **in the open PR #6364** (about to land).
- **Chapter 8 — down to 9.** Problem 8.2.7 Tor/Ext for ℤ and k[x] modules landed
  substantially (#6269/#6308/#6329, 4 sorries left); the Ch8 §6184 horseshoe /
  ProjectiveResolution assembly closed (#6227). **In-flight:** the bar-resolution
  chain for Problem 8.2.6 — barDiff sorry-free def (#6347), terms+augmentation
  (#6319), face-map primitives (#6342); next is #6336 (barComplex + d∘d=0) →
  #6318 (exactness/packaging) → #6298 (assemble Ext¹ ≃ cocycle Ext¹).
- **Chapter 9 — down to 10.** Block theory (Problem 9.5.3) is active:
  block-orthogonality half + composition-factor infra landed, the
  `exists_block_of_indecomposable` half is open (issue #6362, PR #6363 carries
  the linked infra). Homological-dimension items 9.4.5/9.4.6 (3 each) and the
  Morita quasi-inverse 9.6.5 (1) remain.

### Active frontier — the in-flight chains (as of this snapshot)

Six threads are mid-construction; a planner should keep sequencing these before
opening new fronts:

1. **Ch8 bar resolution → Ext** (Problem 8.2.6): #6336 → #6318 → #6298.
2. **Ch5 5.1.2 End-algebra type isos**: real #6327, quaternionic #6328
   (blocked on #6327).
3. **Ch5 5.16.3b module branching**: #6356 → #6357 → #6286 (all still needed;
   the character-level 5.16.1 is already done).
4. **Ch7 7.8.7 Künneth**: final assembly in open PR #6364.
5. **Ch2 2.16.3 `𝔤ₙ` finrank**: n=4 infinite-dimensional case #6359.
6. **Ch9 blocks** (9.5.3): #6362 / PR #6363.

## Biggest single-file proof targets (by genuine sorry count)

High count does not mean high priority — most are self-contained multi-part
problems — but these are the largest remaining chunks:

| sorries | file | item |
|--------:|------|------|
| 13 | `Chapter6/Problem6_1_3_continued_E7_E8.lean` | E7/E8 Dynkin-diagram parts |
| 10 | `Chapter3/Problem3_8_5.lean` | failure of Krull–Schmidt (infinite-dim) |
|  9 | `Chapter5/Problem5_11_1.lean` | decompose induced reps from subgroups of A₅ |
|  9 | `Chapter4/Problem4_12_11.lean` | elasticity / Hooke's-law application |
|  8 | `Chapter6/Problem6_9_2.lean` | E8 lattice and root systems |
|  5 | `Chapter6/Problem6_1_6.lean`, `Chapter6/Problem6_1_3_continued_tildeE.lean`, `Chapter5/Problem5_24_1_b.lean`, `Chapter3/Problem3_9_5.lean` | McKay graph, affine Dynkin, Problem 5.24.1(b), Clifford |
|  4 | `Chapter8/Problem8_2_7.lean` | higher Tor/Ext for cyclic modules |
|  3 | `Chapter9/Problem9_5_3.lean`, `Chapter9/Problem9_4_6.lean`, `Chapter9/Problem9_4_5.lean`, `Chapter8/Problem8_2_6.lean`, `Chapter5/Problem5_1_2.lean`, `Chapter2/Problem2_16_5.lean` | blocks, homological dim, bar resolution, End-algebra isos, Lie char-p |

## Ranked shortlist of tractable next targets (self-contained, single-sorry)

These are the files carrying exactly one genuine sorry — the cheapest wins, and
several reuse infrastructure that already landed. Ranked by tractability × value:

1. **`Chapter7/Problem7_8_7.lean` — `Problem7_8_7_iv`** (Künneth final assembly).
   Already in open PR #6364; verify it lands rather than re-claiming.
2. **`Chapter5/Exercise5_27_2_{Dihedral,Affine,Heisenberg}.lean`** — three
   classification theorems, one sorry each. The old landscape noted 5.27.2
   "redoes 4.12.1(a), 4.12.2, 4.12.6", and those Chapter-4 items are now proved
   (#6236, #6257), so the inputs exist. Good parallel throughput.
3. **`Chapter5/Exercise5_27_3.lean`** — single deduction building on 5.27.2.
4. **`Chapter5/Problem5_24_2.lean`** — `invariantSubalgebra_eq_adjoin_traceWord`,
   one self-contained theorem.
5. **`Chapter2/Problem2_7_5.lean`** — `center_of_isOfFinOrder` (q-Weyl centre when
   q has finite order); mirrors the merged 2.7.4c dimension result.
6. **`Chapter4/Problem4_12_7.lean`** — part (f) `exists_surjective_hom_to_SO3`
   (parts a–e already proved; this is the surjection SU(2)→SO(3)).
7. **`Chapter9/Problem9_6_5.lean`** — `exists_quasiInverse_tensor_functor`
   (Morita, Theorem 9.6.4). Single sorry but genuinely deep; lower on the list.

Deliberately **not** recommended as "tractable": `Chapter4/Problem4_12_8.lean`
(finite subgroups of SO(3)/SU(2) — the full ADE classification behind one sorry)
and the multi-sorry Chapter-6 Dynkin/lattice files, which are large combinatorial
efforts.

## Status corrections applied this session

Cross-checking `items.json` status against comment-stripped source found **13
items marked `statement_formalized` whose Lean file is now genuinely sorry-free
and non-vacuous** (no `: True` placeholders); all 13 were upgraded to
`sorry_free`. This moved the `sorry_free` count from 522 to **535** and
`statement_formalized` from 42 to **29**.

Upgraded ids:
`Chapter2/Problem2.8.11`, `Chapter2/Exercise2.9.11`, `Chapter3/Problem3.9.2`,
`Chapter3/Problem3.9.3`, `Chapter4/Problem4.12.5`, `Chapter5/Example5.1.3`,
`Chapter5/Exercise5.1.7`, `Chapter5/Theorem5.9.1`, `Chapter5/Problem5.12.5`,
`Chapter5/Problem5.16.1`, `Chapter5/Proposition5.22.2`, `Chapter6/Problem6.1.3`,
`Chapter9/Exercise9.6.3`.

The reverse direction is **clean**: every one of the 30 sorry-bearing files maps
to an item still marked `statement_formalized` (or a multi-part item), so no
`sorry_free` item hides a sorry.

**Not** reclassified (left as-is, flagged for a planner): a cluster of items in
terminal-ish non-`sorry_free` statuses whose files are also sorry-free —
`proved` (`Chapter4/Problem4.12.6`, `Chapter4/Problem4.12.9`,
`Chapter5/Exercise5.3.3`, `Chapter8/Example8.1.7`), `proof_complete`
(`Chapter2/Problem2.13.1`, `Chapter4/Theorem4.6.2`,
`Chapter4/Discussion_after_Theorem4.6.2`), and `formalized`
(`Chapter2/Problem2.3.16`, `Chapter5/Problem5.10.2`). These use a different,
possibly intentional status vocabulary; a survey session should not guess their
intent. Reconciling them (if `sorry_free` is meant to be canonical) would move
the count further toward ~544. `Chapter2/Remark2.9.3` keeps status `sorry` but
has no genuine sorry in source — it is a book-unproved statement recorded via
`proof_wanted`; treat as intentional, not a gap.

## One-glance status

- **Genuine sorries:** 108 in 30 files, across Chapters 2–9. **Axioms/admits:** 0.
- **`items.json`:** 535 sorry_free / 29 statement_formalized / 28 other of 592
  (after +13 `statement_formalized`→`sorry_free` corrections this session).
- **Frontier shape:** thinned proof-fill wave. No single deep crux; the largest
  concentration is Chapter 6 Dynkin/lattice combinatorics (31 sorries).
- **Active in-flight chains:** Ch8 bar resolution (#6336→#6318→#6298), Ch5 5.1.2
  End-isos (#6327/#6328), Ch5 5.16.3b branching (#6356→#6357→#6286), Ch7 7.8.7
  assembly (PR #6364), Ch2 2.16.3 g₄ (#6359), Ch9 blocks (#6362/PR #6363).
- **Cheapest next wins:** the single-sorry files — Ch5 Exercise 5.27.2 trio +
  5.27.3, Problem 5.24.2, Problem 2.7.5, Problem 4.12.7(f) (see shortlist).
- **Main health:** no evidence `main` is broken; the rapid-merge cadence
  (170 PRs in ~3 days) continued through the snapshot with auto-merge intact.
</content>
</invoke>

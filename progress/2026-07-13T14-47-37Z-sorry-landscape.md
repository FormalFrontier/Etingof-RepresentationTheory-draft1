# Sorry Landscape Analysis — post-24-merge refresh

Generated 2026-07-13 14:47 UTC by summarize session (issue #6498, branch
`agent/ab35012f`) against `origin/main` at HEAD `1d954f7a`. **Supersedes
`progress/2026-07-11T03-21-52Z-sorry-landscape.md`** (issue #6434, HEAD
`03cddff5`), which reported **90 genuine sorries in 29 files**; the current
count is **81 in 23 files**. Since that snapshot closed (2026-07-11 04:02:07Z),
**24 PRs merged to `main`**, concentrated in Chapters 5, 8, and 9 (plus one Ch2
merge), thinning the frontier by 9 sorries and, more significantly, by 6 whole
files.

## Headline: 81 genuine sorries across 23 files, spread over Chapters 2–9

After stripping every block comment (`/- … -/`) and line comment (`-- …`), the
`EtingofRepresentationTheory/` tree contains **81 genuine proof-gap `sorry`
tactics in 23 files** — down from 90/29. There are **no `axiom` declarations and
no `admit`s** (every `admit` string hit is English prose inside docstrings, e.g.
"admit a unitary structure"). Two files still record book-unproved statements via
**`proof_wanted`** rather than `sorry` (`Chapter2/Remark2_9_3.lean` — Ado's
theorem; `Chapter5/Remark5_23_3.lean`); these are genuine gaps the
comment-stripped `sorry` counter does **not** see, so "81 sorries" slightly
understates the unproved surface. One of the 81 (`Problem5_24_1_b.lean:57`) is a
proof obligation *inside a definition's `where`/body region* rather than a
top-level proof gap — permitted by project rules, but still a real obligation.

Reproduce the headline count (comment-stripping `awk` depth-counter, then
whole-word `sorry` on surviving code) against a clean `origin/main` checkout:
```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b'
done | awk '{s+=$1}END{print s}'   # -> 81 across 23 files at HEAD 1d954f7a
```

### items.json status distribution (592 items)

After this session's status reconciliation (see "Status corrections" below):

| Status | Count |
|--------|------:|
| `sorry_free` | 546 |
| `statement_formalized` | 23 |
| `accepted` | 6 |
| `proved` | 5 |
| `formalized` | 4 |
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

The heterogeneous legacy labels (`proved`, `formalized`, `accepted`,
`proof_complete`, `partially_formalized`, `partially_proved`) persist from
earlier pipeline stages. They are **flagged but not mass-rewritten** here — each
was spot-checked and none is factually wrong against source (the `proved` /
`proof_complete` / `accepted` items are all sorry-free; `sorry` on
`Chapter2/Remark2.9.3` correctly marks the `proof_wanted` Ado gap;
`non_formalizable` on `Chapter2/Remark2.9.14` is a prose remark). A future
housekeeping pass could canonicalize the sorry-free legacy labels to `sorry_free`,
but that is cosmetic.

### Status corrections applied this session (3)

Three items were marked `statement_formalized` but their Lean source is now
genuinely sorry-free (the residual sorries were discharged by merges in this
window); corrected to `sorry_free`:

| Item | file | was | now | closed by |
|------|------|-----|-----|-----------|
| `Chapter5/Problem5.1.2` | `Problem5_1_2.lean` | statement_formalized | sorry_free | #6494 (5.1.2(b) real-form) |
| `Chapter5/Problem5.16.3` | `Problem5_16_3.lean` | statement_formalized | sorry_free | residual D3 combinatorics (was issue #6424) |
| `Chapter9/Problem9.4.5` | `Problem9_4_5.lean` | statement_formalized | sorry_free | #6474 (Euler-char induction, cartan_det) |

The reverse direction was also audited: every one of the 23 files carrying a
genuine sorry maps to an item whose status is *not* `sorry_free`, so there are no
`sorry_free`-labelled items hiding a live sorry.

### Per-chapter picture (after corrections)

Columns: total items, `sorry_free`, `statement_formalized`, other statuses, and
**genuine sorries in the Lean source** (comment-stripped; may differ from the
`statement_formalized` count because one item can span several sorried helper
files, and a few multi-part items are still `statement_formalized` while some of
their files are already sorry-free).

| Chapter | items | sorry_free | stmt_formalized | other | genuine sorries |
|--------:|------:|-----------:|----------------:|------:|----------------:|
| 0 (front/derived) | 15 | 6 | 1 | 8 | 0 |
| 1 | 3 | 3 | 0 | 0 | 0 |
| 2 | 117 | 110 | 3 | 4 | 6 |
| 3 | 58 | 56 | 2 | 0 | 9 |
| 4 | 60 | 53 | 3 | 4 | 5 |
| 5 | 157 | 148 | 4 | 5 | 17 |
| 6 | 64 | 59 | 4 | 1 | 31 |
| 7 | 59 | 59 | 0 | 0 | 0 |
| 8 | 24 | 20 | 3 | 1 | 8 |
| 9 | 35 | 32 | 3 | 0 | 5 |
| **total** | **592** | **546** | **23** | **22** | **81** |

Per-file genuine-sorry tally (comment-stripped, descending):
```
13  Chapter6/Problem6_1_3_continued_E7_E8.lean
 9  Chapter5/Problem5_11_1.lean
 8  Chapter6/Problem6_9_2.lean
 5  Chapter6/Problem6_1_6.lean
 5  Chapter6/Problem6_1_3_continued_tildeE.lean
 5  Chapter5/Problem5_24_1_b.lean
 5  Chapter3/Problem3_9_5.lean
 4  Chapter8/Problem8_2_7.lean
 4  Chapter3/Problem3_8_5.lean
 3  Chapter9/Problem9_4_6.lean
 3  Chapter4/Problem4_12_11.lean
 3  Chapter2/Problem2_16_5.lean
 2  Chapter8/Problem8_2_8.lean
 2  Chapter8/Problem8_2_6.lean
 2  Chapter2/Problem2_16_4.lean
 1  Chapter9/Problem9_6_5.lean
 1  Chapter9/Problem9_5_3.lean
 1  Chapter5/Problem5_24_2.lean
 1  Chapter5/Exercise5_27_2_Dihedral.lean
 1  Chapter5/Exercise5_27_2_Affine.lean
 1  Chapter4/Problem4_12_8.lean
 1  Chapter4/Problem4_12_7.lean
 1  Chapter2/Problem2_16_3.lean
```

Per-chapter: Ch2 = 6, Ch3 = 9, Ch4 = 5, Ch5 = 17, Ch6 = **31 (largest block)**,
Ch7 = 0, Ch8 = 8, Ch9 = 5.

## What changed since 2026-07-11 03:21 (the 24 merges that landed)

By chapter (only threads that moved; net sorry deltas vs the prior landscape):

- **Chapter 5 — 22 → 17.** The busiest window. (a) The **orbit-method engine for
  Theorem 5.27.1** matured: induced-rep dimension formula `finrank(V χ U) =
  (stab χ).index · finrank U` (#6453), reusable simple-FDRep classification for
  finite-abelian `G` as characters `G →* ℂˣ` (#6459), ℤ/N inversion-orbit
  combinatorics (#6460), forward functoriality of `inducedRepV` (#6470), and
  basepoint-independence / central-transport conjuncts (#6488). (b) On that
  engine, **Exercise 5.27.2** assemblies landed: Heisenberg
  (`heisenberg_classification`, #6483 + #6489) is now sorry-free; the **dihedral**
  (#6472 reduces to `semidirect_classification`, #6477 dual-action/stabilizer)
  and **affine** (#6487 partial dual-`Kˣ`-orbit) threads are in flight —
  `Exercise5_27_2_Dihedral.lean` and `Exercise5_27_2_Affine.lean` each retain
  their single top-level assembly `sorry`. (c) **Exercise 5.27.3** completed:
  parts (ii) non-iso (#6456) and (iii) sum-of-squares count (#6466) — file now
  sorry-free. (d) **Problem 5.1.2** real-form characterization
  `isRealType_iff_exists_real_form` (#6494) closed the last 5.1.2 sorry. (e)
  **Problem 5.24.2 (FFT)** was reduced from the raw invariant-inclusion to a
  single multihomogeneous Schur–Weyl core (#6486 elementary inclusion + FFT
  reduction, #6493 reduce-to-core); one deep `sorry`
  (`weightedHomogeneous_invariant_mem_adjoin`) remains — this is issue **#6492**.
  Ch5's residual 17 is dominated by 5.11.1 (9) + 5.24.1(b) (5).
- **Chapter 8 — 9 → 8.** The Tor/Ext thread advanced: `barResolution :
  ProjectiveResolution` assembled from the k-linear contraction (#6454), and
  **8.2.6(ii)** `Ext¹ ≃+ Ext1` discharged via the degree-1 `CohomologyClass` crux
  (#6465 reduction + #6468 crux). Residual 8 sorries: 8.2.7 (Tor/Ext for abelian
  groups, 4), 8.2.8 (Tor/Ext for tensor-product algebras, 2), 8.2.6 (long-exact
  Tor sequence + left-derived identification, 2).
- **Chapter 9 — 7 → 5.** **9.4.5(i)** completed: Krull–Schmidt integer
  class-vector `homClassVector_projective_eq_mulVec` (#6467) + Euler-characteristic
  induction discharging `cartan_det` (#6474) — file now sorry-free. **9.5.3(ii)**
  `compositionFactors_areLinked` assembled from dévissage + splitting (#6455),
  leaving 9.5.3 with its single (i) blocks↔idempotents sorry. New Ch9 infra for
  the 9.4.6 path-algebra thread: induction functor `A ⊗_S −` with projectivity
  preservation (#6473) and the arrow S-bimodule `V` of a path algebra (#6482).
  9.4.6 itself still carries 3 sorries (hom-dim ≤ 1 for path/free algebras).
- **Chapter 2 — 7 → 6.** Problem 2.7.5 `center_of_isOfFinOrder` (root-of-unity
  centre = `adjoin{xⁿ,x⁻ⁿ,yⁿ,y⁻ⁿ}`, #6461) landed, closing the q-Weyl-centre
  sorry. Residual 6: 2.16.5 (q-enveloping-algebra irreps, 3), 2.16.4 (sl₂ char-p,
  2), 2.16.3(a) `finrank_g_three` (1).
- **Chapters 3, 4, 6, 7 — unchanged this window.** Ch3 = 9 (3.9.5 Clifford 5,
  3.8.5 Krull–Schmidt-failure 4), Ch4 = 5 (4.12.11 SO(3) elasticity 3, 4.12.7(f)
  SU(2)→SO(3) 1, 4.12.8 finite SO(3) subgroups 1), Ch6 = 31 (unchanged, the
  Dynkin/lattice classification block: 6.1.3-cont E7/E8 13, 6.9.2 E8 lattice 8,
  6.1.6 McKay 5, 6.1.3-cont tilde-E 5), Ch7 = 0 (fully sorry-free).

## In-flight chains (unclaimed or open-PR as of this snapshot)

- **Ch5 5.24.2 Schur–Weyl / FFT core** — issue **#6492** (unclaimed). Single
  remaining sorry `weightedHomogeneous_invariant_mem_adjoin`, but this is
  genuinely the FFT for `GL_N` (Schur–Weyl / double-centralizer, Theorem 5.18.4).
  Deep; the issue itself expects self-decomposition into ~4 sub-issues.
- **Ch5 Exercise 5.27.2 affine** — issue **#6490** (unclaimed; NB: issue body is
  empty, title only). #6487 landed the partial dual-`Kˣ`-orbit analysis.
- **Ch5 Exercise 5.27.2 semidirect/dihedral residual** — issue **#6471**
  (`semidirect_classification`, open PR **#6496**, CI failing → repair territory).
- **Ch9 9.4.6(i) standard resolution** — chain **#6480 → #6481 → #6438** (#6481
  and #6438 `blocked`; #6480 has open PR **#6495**, CI failing → repair territory).

## Ranked shortlist of tractable next targets

Honest tractability, seeding future planners. "Single sorry" ≠ cheap — several
one-sorry files below are deep whole-theorem gaps.

**Tier 1 — genuinely tractable, high value (pattern or infra already exists):**

1. **Ch5 Exercise 5.27.2 dihedral & affine assemblies**
   (`Exercise5_27_2_Dihedral.lean`, `Exercise5_27_2_Affine.lean`, 1 sorry each).
   The orbit-method assembly pattern is *proven* — the Heisenberg twin
   (`heisenberg_classification`) landed this window using exactly the
   Simple/non-iso/complete conjunct structure these two now sorry. The dihedral
   dual-action helpers (#6477) and affine orbit analysis (#6487) already landed.
   Highest-leverage next proofs, though partly tracked by in-flight #6471/#6490 —
   coordinate rather than duplicate.
2. **Ch2 2.16.3(a) `finrank_g_three = 6`** (`Problem2_16_3.lean`, 1 sorry). A
   concrete finrank computation for the type-`G₂` positive part; the surrounding
   2.16.3(b) machinery is fully proved in the same file. **Already claimed
   (#6340)** — verify liveness before planning.

**Tier 2 — self-contained but non-trivial:**

3. **Ch8 8.2.8** (`Problem8_2_8.lean`, 2 sorries): Tor and Ext for tensor products
   of algebras. Two parallel statements; leverages the Tor/Ext infra just built in
   8.2.6.
4. **Ch8 8.2.7** (`Problem8_2_7.lean`, 4 sorries): computing Tor/Ext for abelian
   groups and `k[x]/(xⁿ)` — concrete homological computations.
5. **Ch3 3.8.5** (`Problem3_8_5.lean`, 4 sorries): the four Krull–Schmidt-failure
   theorems (Möbius/Picard argument) over the already-constructed
   `periodicSubalg`/`antiperiodicSubmod`.

**Tier 3 — deep; do not mistake a low sorry count for low effort:**

6. **Ch5 5.24.2 FFT core** (#6492, 1 sorry) — Schur–Weyl / double-centralizer;
   the deepest single sorry in the tree. Needs decomposition.
7. **Ch9 9.4.6(i)** (`Problem9_4_6.lean`, 3 sorries) — path-algebra homological
   dimension ≤ 1; blocked on the standard-resolution middle-exactness chain
   (#6481 → #6438).
8. **Ch9 9.6.5 / 9.5.3(i)** (1 sorry each) — whole-theorem gaps: 9.6.5 defers the
   entire `P ⊗_B −` quasi-inverse functor construction; 9.5.3(i) is the
   blocks↔indecomposable-central-idempotents bijection.
9. **Ch4 4.12.7(f) / 4.12.8** (1 sorry each) — SU(2)→SO(3) surjection with kernel
   `{±1}`, and the classification of finite subgroups of SO(3). Both are
   substantial geometry/group-theory statements despite the single sorry.
10. **Ch6 Dynkin/lattice block** (31 sorries across 4 files) — E7/E8 and affine
    Dynkin classification, E8 lattice, McKay graph. Largest chapter block, no
    movement in the last two windows; genuinely hard root-system combinatorics.

## Method notes

- Counts are comment-stripped genuine sorries against `origin/main` HEAD
  `1d954f7a`; the reproducer command above is authoritative.
- `proof_wanted` gaps (2 files) and the one in-definition obligation
  (`Problem5_24_1_b.lean:57`) are *not* counted in the 81 but are real unproved
  surface — noted for honesty.
- Merged-PR list obtained via
  `gh pr list --state merged --json number,title,mergedAt` filtered to
  `mergedAt > 2026-07-11T04:02:07Z` (24 results).
</content>

# Sorry Landscape Analysis — proof-completeness milestone reached (0 genuine sorries)

Generated 2026-07-22 05:58 UTC by summarize session (issue #7262, branch
`agent/fe6f515c`) against `origin/main` at HEAD
`36586e188f70f081f734ab29c32c0a27aba50c8a` (`36586e18`). **Supersedes
`progress/2026-07-21T02-23-07Z-sorry-landscape.md`** (issue #7087, HEAD
`6c4f00db`), which reported **1 genuine sorry in 1 file** (`finrank_g_three`,
Problem 2.16.3(a), owned by #7084).

**Headline milestone: #7084 has landed and the tree is now genuinely
sorry-free.** The nesting-aware comment-stripping depth counter reports **0
genuine `sorry` tactics across the entire `EtingofRepresentationTheory/` tree**.
The formalization of Etingof's *Introduction to Representation Theory* is
**proof-complete**: every formalized statement has a real proof, modulo two
book-*disavowed* `proof_wanted` assertions (not project debt) and zero
axioms/admits/`True`-stubs.

Since the 02-23 snapshot, **86 PRs merged to `main`**. Unlike that window (a
docstring-fidelity sweep collapsing the last sorries), this wave is dominated by
**two genuine feature streams** — Chapter 4 dihedral irreps and Chapter 5
finite-group / GL₂(𝔽_q) representation theory — layered under the ongoing
**Stage 3.7 statement-fidelity audit sweep**.

## Headline: 0 genuine sorries across 0 files

After stripping every block comment (`/- … -/`, nesting-aware) and truncating at
the first line comment (`--`), then matching whole-word `sorry` on the surviving
code, the tree contains **0 genuine proof-gap `sorry` tactics**. The counter,
re-run at authoring time against `origin/main` HEAD `36586e18`, prints nothing:

```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  n=$(awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b')
  if [ "$n" -gt 0 ]; then echo "$n $f"; fi
done   # -> (no output: 0 genuine sorries)
```

**Do not use a bare `grep -c sorry`.** The tree is saturated with the word
"sorry" in prose ("proved sorry-free", "the sole remaining sorry", "rather than a
`sorry`"), which inflates a naive count to ~165 false positives. The counter
above is authoritative.

### How the last sorry closed

The single survivor from the 02-23 snapshot was `finrank_g_three` (Problem
2.16.3(a) — the third G₂ positive-nilpotent Lie algebra `𝔤₃` has dimension 6).
It landed via **#7084 / PR #7102** (`feat(Ch2 #Problem2.16.3a): prove
finrank_g_three = 6 over char ≠ 2`). The proof carries the hypothesis
`(hk : (2 : k) ≠ 0)` — a genuine and documented restriction: the statement is
false in characteristic 2 (the reason #6340 was routed to replan as #7084). The
whole of Problem 2.16.3 is now covered sorry-free:

- Part (a): `finrank_g_one = 3`, `finrank_g_two = 4`, `finrank_g_three = 6`
  (`Chapter2/Problem2_16_3.lean:284,483,1374`).
- Part (b): `not_finiteDimensional_g_four` (`:1044`).

### The remaining unproved surface, in full

The zero `sorry` count is the whole proof-gap picture, but for completeness two
book-*disavowed* statements are recorded via **`proof_wanted`** (which the
comment-stripped counter does not see). Both are unchanged from every prior
snapshot and are **not project debt** — the book explicitly declines to prove
them:

- `Chapter2/Remark2_9_3.lean:47` — `ado` (Ado's theorem).
- `Chapter5/Remark5_23_3.lean:208` — `sl_finiteDimensional_completely_reducible`.

There are **no `axiom` declarations, no `admit`s, and no `theorem … : True`
stubs**. The only `^axiom`/`\badmit\b`/`: True` grep hits are the English words
appearing in prose inside docstrings (e.g. "may fail to admit a unitary
structure" in `Remark4_6_4.lean`, "axiom is introduced" in `Remark2_9_3.lean`).

So the complete honest picture: **0 genuine `sorry`** + **2 book-disavowed
`proof_wanted`** (not debt) + **0 axioms/admits/`True`-stubs**.

## `items.json` status snapshot

`progress/items.json` tracks **592 items**. Status distribution (after this
turn's one stale-status correction, below):

| status | count |
|---|---|
| `sorry_free` | 572 |
| `proved` | 8 |
| `proof_complete` | 3 |
| `accepted` | 2 |
| `partially_formalized` | 2 |
| `partially_proved` | 2 |
| `formalized` | 1 |
| `non_formalizable` | 1 |
| `proof_wanted` | 1 |

The non-`sorry_free` labels are largely historical vocabulary variants
(`proved`, `proof_complete`, `formalized`, `accepted`) applied by different
threads over the project's life; they do **not** indicate open proof gaps (all
the underlying files pass the comment-stripped counter at 0). The two
`partially_proved` Ch6 items (Problem 6.1.6 McKay-graph, Problem 6.9.3
Ext/Jordan-Hölder) and the two `partially_formalized` Ch5 items (Problem 5.2.7,
Discussion 5.10.2) record deliberate partial *book-coverage*, not
`sorry`-carrying source.

### This turn's one `items.json` edit

The previous snapshot's `statement_formalized` on **`Chapter2/Problem2.16.3`**
was held *solely* because it carried the `finrank_g_three` sorry (its
`coverage_note` read "Sole remaining genuine `sorry` … GENUINE OPEN GAP …
tracked by claimed issue #6340"). With #7084 landed and the file sorry-free,
that status and note are stale. This turn flips the item to `sorry_free` and
rewrites the note to record the discharged proof (over `char ≠ 2`). This is the
one non-fabricated, wave-driven reconciliation; no other status was touched. In
particular, the four `partially_*` items are deliberate holds that require a
per-part blob check, not a bulk relabel, so no speculative reclassification was
performed.

### Fidelity-column snapshot (Stage 3.7)

The Stage 3.7 statement-fidelity audit sweep records a `fidelity` value per item.
Current distribution:

| fidelity | count |
|---|---|
| `verified` | 288 |
| `faithful` | 3 |
| `unchecked` | 1 |
| (none) | 300 |

The sweep has now audited **292 of 592 items (~49%)**. Two notable movements
since the 02-23 doc (which predates the fidelity column entirely):

- **The two recorded `gap`s are both resolved — there are now 0 open fidelity
  gaps.** The Problem 4.12.1(a) dihedral-classification gap (audited GAP in
  #7223, because the headline had proved only the dimension dichotomy
  `finrank ∈ {1,2}`, not the full odd/even classification) was closed by the
  feature wave #7222 → #7248 → #7250: the explicit 2-dim family `Vrep N j`,
  exhaustiveness (`simple_iso_char_or_Vrep`), non-isomorphism, and the
  odd/even count headlines are now formalized sorry-free. Its fidelity was
  reset to **`unchecked`** pending a fresh Stage 3.7 re-audit of the completed
  statement — this is the sole `unchecked` item.
- The `faithful` label sits on three items (`Chapter2/Problem2.16.2`,
  `Chapter4/Problem4.12.2`, `Chapter5/Theorem5.10.1`) — a near-synonym of
  `verified` retained from earlier audit vocabulary.

### Per-chapter picture

| Ch | items | `sorry_free` | other statuses | fidelity verified | fidelity none | genuine sorries |
|---|---|---|---|---|---|---|
| 1 | 3 | 3 | — | 0 | 3 | 0 |
| 2 | 117 | 114 | proof_wanted 1, non_formalizable 1, proof_complete 1 | 58 | 58 | 0 |
| 3 | 58 | 58 | — | 39 | 19 | 0 |
| 4 | 60 | 56 | proof_complete 2, proved 2 | 25 | 33 (+1 unchecked) | 0 |
| 5 | 157 | 150 | partially_formalized 2, proved 4, formalized 1 | 71 | 85 | 0 |
| 6 | 64 | 62 | partially_proved 2 | 36 | 28 | 0 |
| 7 | 59 | 59 | — | 31 | 28 | 0 |
| 8 | 24 | 23 | proved 1 | 10 | 14 | 0 |
| 9 | 35 | 34 | proved 1 | 18 | 17 | 0 |
| (derived) | 15 | 13 | accepted 2 | 0 | 15 | 0 |
| **total** | **592** | **572** | **20** | **288** | **300 (+1 unchecked, +3 faithful)** | **0** |

## What changed since 2026-07-21T02:23

The 86 merges break down into two feature streams plus the fidelity sweep:

- **Chapter 4 — dihedral irreps / Problem 4.12.1(a).** Construction of the
  2-dim irreps `Vrep N j` (irreducibility `Vrep_irreducible`, character
  `Vrep_trace_r`, pairwise non-isomorphism `Vrep_not_iso`; #7222/#7226), the
  full exhaustiveness classification (`simple_iso_char_or_Vrep`, via a
  sum-of-`dim²` = 2N pigeonhole; #7248/#7250), and the one-dimensional character
  counts (`one_dim_reps_card_odd = 2`, `one_dim_reps_card_even = 4`; #7249) plus
  the total-irrep count headlines (`two_dim_simples_card_odd/_even`,
  `total_irreps_card_odd/_even`, `irreps_sum_sq`). This turned the standing
  4.12.1(a) fidelity gap into a complete, sorry-free classification.

- **Chapter 5 — finite-group representation theory.** Two arcs:
  - **GL₂(𝔽_q):** the irreducible families and completeness-by-counting —
    the class-count claim discharged and completeness proved by counting
    (#7252/#7255).
  - **Center-dimension bridges** toward
    `#(irreducible ℂ-reps of finite G) = #(ConjClasses G)`:
    `finrank Z(k[G]) = #ConjClasses` via the class-sum center basis (#7260),
    and `finrank Z(semisimple algebra) = #(Wedderburn factors)` (#7257/#7261).
    These assemble the chain #7257 → #7258 → #7259. **#7257 has merged**;
    **#7258** (assembling the two bridges) is in review as open PR #7263;
    **#7259** (discharging the final hypothesis) remains `blocked` on #7258.

- **Stage 3.7 statement-fidelity audit sweep.** Report-only review PRs recording
  `fidelity: verified` (e.g. Problem 2.3.18 Dixmier Schur-lemma #7256, Problem
  4.12.7 SU(2)↔quaternions #7217) and reconciling stale `accepted` derived items
  (#7253). Verified count moved 286 → 288; the two prior gaps closed (one via
  the 4.12.1 feature arc above, now `unchecked`); ~300 items still `(none)`.

- Assorted feature exposures (e.g. Problem 5.16.3(b) corner-content scalar
  #7247, Problem 4.12.2(d) Heisenberg irrep classification #7218,
  `schurPoly_eval_one_eq_weylDimension` #7224) and the **#7084 landing** that
  closed the last sorry.

**Frontier trajectory.** The genuine-sorry count has fallen
6 (2026-07-17) → 4 (2026-07-18) → 3 (2026-07-20) → 1 (2026-07-21) → **0
(2026-07-22)**. The 02-23 window was a clean collapse to a single owned sorry;
this window discharges it. The project has crossed from "proof-complete modulo
one owned sorry" to **fully proof-complete**.

## Project status / remaining work

With the formalization proof-complete (0 sorries, 0 axioms/admits/`True`-stubs,
2 book-disavowed `proof_wanted`), the remaining work is **not broad new
formalization**. It is audit/exposure plus a small amount of targeted feature
work:

1. **Stage 3.7 fidelity audits — the main live frontier.** ~300 items still
   carry `fidelity: (none)` and 1 is `unchecked` (Problem 4.12.1, awaiting a
   re-audit of its now-complete classification). Two such review issues are
   open and unclaimed as of this turn: **#7244** (Problem 4.5.2 central
   idempotents) and **#7265** (Problem 4.12.4 graph-automorphism eigenvalue).
   This is the dominant remaining thread — statement-fidelity/non-vacuity
   verification, not proof work.

2. **Zero open fidelity gaps.** Both previously-recorded gaps are resolved. The
   only residual is re-auditing Problem 4.12.1 (fidelity `unchecked`) now that
   the classification is complete.

3. **Chapter 5 completeness chain.** The targeted feature frontier:
   **#7258** (assemble `#irreps = #ConjClasses` from the two center-dimension
   bridges) is in review as PR #7263; **#7259** (discharge the final
   completeness hypothesis) is `blocked` on it. This is the one bounded piece of
   genuinely new formalization still in flight.

4. **Optional consistency polish (not a correctness gap).** The residual
   historical `items.json` status vocabulary (`proved` / `proof_complete` /
   `formalized` / `accepted`, ~17 items) could be normalized to a single
   canonical label if a planner decides it is worth a dedicated reconciliation
   issue.

For the next planner: the formalization is at its terminus — fully
proof-complete. Prioritize the Stage 3.7 fidelity sweep (#7244, #7265, and the
~300 `(none)` items), re-audit Problem 4.12.1, and land the Chapter 5
completeness chain (#7258 → #7259). No broad new formalization remains.

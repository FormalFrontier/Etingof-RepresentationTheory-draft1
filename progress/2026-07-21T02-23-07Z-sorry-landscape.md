# Sorry Landscape Analysis — proof-completeness milestone (single genuine sorry)

Generated 2026-07-21 02:23 UTC by summarize session (issue #7087, branch
`agent/8094a0bd`) against `origin/main` at HEAD `6c4f00db`. **Supersedes
`progress/2026-07-18T16-29-26Z-sorry-landscape.md`** (issue #6976, HEAD
`7337d8e3`), which reported **4 genuine sorries in 3 files**. The current count
is **1 genuine sorry in 1 file**. Since that snapshot, **73 PRs merged to
`main`** (the #7087 issue body cites 71 — the two most recent, review PR #7090
and doc PR #7091, landed after the issue was filed). The window is dominated by
the **docstring-fidelity sweep** — 33 PRs that corrected stale
"deferred / not yet formalized / BLOCKED / left as sorry" claims on files whose
proofs had in fact already landed sorry-free — layered on top of the genuine
feature/infra PRs that discharged the last few real sorries.

**Headline milestone: the formalization is now proof-complete except for a
single genuine `sorry`.** That lone gap is `finrank_g_three` (Problem 2.16.3(a),
the G₂ positive-nilpotent Lie algebra `𝔤₃` has dimension 6), in
`Chapter2/Problem2_16_3.lean:1051`. It is actively claimed under issue **#7084**
(proving it over `char ≠ 2` with an added `(2:k) ≠ 0` hypothesis; the theorem is
false over characteristic 2 — this is the reason #6340 was routed to replan as
#7084). Do not touch that file — this is a documentation/status turn only.

## Headline: 1 genuine sorry across 1 file

After stripping every block comment (`/- … -/`, nesting-aware) and truncating at
the first line comment (`--`), then matching whole-word `sorry` on the surviving
code, the `EtingofRepresentationTheory/` tree contains **1 genuine proof-gap
`sorry` tactic in 1 file**:

```
1 EtingofRepresentationTheory/Chapter2/Problem2_16_3.lean
--- TOTAL: 1 genuine sorry across 1 file ---
```

This is the `finrank_g_three` theorem body (`Problem2_16_3.lean:1051`).

**Do not use a bare `grep -c sorry`.** The codebase is saturated with the word
"sorry" in prose ("proved sorry-free", "rather than a `sorry`", "the sole
remaining sorry"), which inflates a naive count to ~165 false positives. The
authoritative counter is the nesting-aware comment-stripping `awk` depth counter
(documented at `progress/2026-07-11T00-49-00Z-sorry-landscape.md` lines 70-80),
reproduced here and re-run at authoring time against `origin/main` HEAD
`6c4f00db`:

```bash
find EtingofRepresentationTheory -name '*.lean' | while read f; do
  n=$(awk 'BEGIN{depth=0}{line=$0;out="";i=1;while(i<=length(line)){two=substr(line,i,2);
    if(depth>0){if(two=="-/"){depth--;i+=2;continue}i++;continue}
    else{if(two=="/-"){depth++;i+=2;continue}if(two=="--"){break}out=out substr(line,i,1);i++}}
    print out}' "$f" | grep -c '\bsorry\b')
  if [ "$n" -gt 0 ]; then echo "$n $f"; fi
done   # -> 1 EtingofRepresentationTheory/Chapter2/Problem2_16_3.lean
```

### The remaining unproved surface, in full

The single `sorry` slightly understates the unproved frontier, because two
book-*disavowed* statements are recorded via **`proof_wanted`** (not `sorry`),
which the comment-stripped counter does not see. Both are unchanged from the
prior snapshot and are **not project debt** — the book explicitly declines to
prove them:

- `Chapter2/Remark2_9_3.lean:47` — `ado` (Ado's theorem).
- `Chapter5/Remark5_23_3.lean:209` — `sl_finiteDimensional_completely_reducible`.

There are **no `axiom` declarations and no `admit`s** in the code. The only
`^axiom`/`admit` grep hits are the English words "axiom" and "admit" appearing
in prose inside docstrings (e.g. `Remark4_6_4.lean`, `Problem5_12_5.lean`). A
`theorem … : True` grep returns **0** — every prior vacuous-`True` stub is
retired (the completeness-audit sub-issues #5119–#5139 are all closed).

So the complete honest picture: **1 genuine `sorry`** (owned, #7084) + **2
book-disavowed `proof_wanted`** (not debt) + **0 axioms/admits/`True`-stubs**.

## `items.json` status snapshot

`progress/items.json` tracks **592 items**. Status distribution:

| status | count |
|---|---|
| `sorry_free` | 567 |
| `proved` | 8 |
| `accepted` | 6 |
| `proof_complete` | 3 |
| `partially_formalized` | 2 |
| `partially_proved` | 2 |
| `statement_formalized` | 1 |
| `formalized` | 1 |
| `proof_wanted` | 1 |
| `non_formalizable` | 1 |

The non-`sorry_free` labels are largely historical vocabulary variants
(`proved`, `proof_complete`, `formalized`, `accepted`) applied by different
threads over the project's life; they do **not** indicate open proof gaps. The
one label that genuinely tracks the live frontier is
`statement_formalized` on **`Chapter2/Problem2.16.3`** — the item holding the
`finrank_g_three` sorry — which correctly reflects that its statement is in
place but its proof is not yet complete. The two `partially_proved` Ch6 items
(Problem 6.1.6 McKay-graph, Problem 6.9.3 Ext/Jordan-Hölder) and the
`partially_formalized` Ch5 items (Problem 5.2.7, Discussion 5.10.2) record
deliberate partial book-coverage, not `sorry`-carrying source (all four files
pass the comment-stripped counter at 0).

**`items.json` was not edited this turn.** The 73-PR wave was overwhelmingly
docstring corrections plus proof completions that landed under their own
feature issues; the last item-level reconciliation, #7021
("reconcile with true 3-sorry proof state"), already aligned `items.json` with
the shrinking frontier on 2026-07-20. Per the summarize-session reconciliation
guidance, a zero-`sorry` file scan does **not** license flipping
`statement_formalized` / `partially_*` items to `sorry_free` — those are
deliberate holds that require a per-part blob-check, not a bulk relabel — so no
speculative reclassification was performed.

### Per-chapter picture

| Ch | items | `sorry_free` | other statuses | genuine sorries |
|---|---|---|---|---|
| 1 | 3 | 3 | — | 0 |
| 2 | 117 | 113 | proof_wanted 1, non_formalizable 1, proof_complete 1, **statement_formalized 1** | **1** (`finrank_g_three`) |
| 3 | 58 | 58 | — | 0 |
| 4 | 60 | 56 | proof_complete 2, proved 2 | 0 |
| 5 | 159 | 151 | partially_formalized 2, proved 4, formalized 1, accepted 1 | 0 |
| 6 | 64 | 62 | partially_proved 2 | 0 |
| 7 | 59 | 59 | — | 0 |
| 8 | 24 | 23 | proved 1 | 0 |
| 9 | 35 | 34 | proved 1 | 0 |
| (derived) | 13 | 8 | accepted 5 | 0 |
| **total** | **592** | **567** | **25** | **1** |

## What changed since 2026-07-18

The 73 merges break down as:

- **33 docstring-fidelity PRs** — the dominant thread. These changed *no* Lean
  signatures, proofs, or imports; they rewrote stale module/theorem docstrings
  that still claimed work was "deferred / statement-pass / left as sorry /
  BLOCKED / tracked as a sub-issue" on files whose proofs had since landed
  sorry-free. They concentrated in the chapters carrying the most spec-first
  scaffolding:
  - **Ch5 (14 PRs)** — the Schur-Weyl / polynomial-representation / Specht-module
    seam: `PolynomialRepEmbedding`, `PolynomialTensorBridge`, `DetIrreducible`,
    `SimpleSubrepExtraction`, `SchurModuleSpecialBlock`, `CauchyCharacterRight`,
    `Theorem5_22_1`, `Theorem5_23_2_PeterWeyl`, `Lemma5_13_4`, `Problem5_11_1`.
  - **Ch4 (several)** — `Exercise4_2_3` and its assembly/split-simples/
    semisimple-base-change satellites, `Problem4.12.2`, `Problem4.12.5`,
    `Problem4.12.8` (SO(3) classification docstrings).
  - **Ch2 (7)** — `Problem2_15_1_m_Module`, `Problem2_16_5`, `Exercise2_11_5`,
    `Problem2_5_2`, `Problem2_7_4/5`, `Problem2_8_6/11`, `Sl2Irrep` (#7091).
  - **Ch6 (7)** — `Problem6_1_5_OrbitComorphism`, `Problem6_1_6`,
    `Proposition6_6_7_sink`, `Corollary6_8_3/4`, `FrobeniusCharacterBridge`.
  - **Ch8 (a few)** — `RearrangeBifunctorNatIso`, `Problem8_2_8`,
    `Exercise8_1_4/8_2_2/8_2_9`.
  - **Ch9 (a few)** — the block-theory cluster `Theorem9_2_1`, `Problem9_5_3`,
    the Krull-Schmidt `Length`/`Fitting` files, `Problem9.4.6`.

- **24 genuine feat / infra PRs** — the proof completions that actually
  collapsed the sorry frontier. Two arcs dominate:
  - **Ch4 Problem 4.12.8 SO(3) finite-subgroup classification** (#6984, #6992,
    #6993, #6996, #6998, #6999, #6963, #6947, #6955, #6965, #6973, #6977, #7022,
    …): the abstract `so3_classification_aux` dispatch was assembled and every
    polyhedral disjunct (cyclic, dihedral, tetrahedral, octahedral, icosahedral)
    was reduced to and then discharged as pure group theory — the icosahedral
    crux reframed as `faithful_perm5_of_simple_index_five` for a simple group of
    order 60.
  - **Ch8 Problem 8.2.8-Ext** (#6981, #6994, #6964, #6968, #6958, #6954, #6948,
    #6952): the `Ext ≃ Extₖ` comparison bridge, closing with the `hXM`
    object-identification (#6994) that made `Problem_8_2_8_ext` sorry-free.
  - Plus **Ch6 Problem 6.1.3-g** affine-Dynkin tree-case residuals and
    **Ch9 Problem 9.4.6** Cartan-matrix = path-count.

- **7 report-only review PRs** — statement-fidelity and axiom-cleanliness audits
  of already-landed clusters (Ch3 3.9.x, Ch4 4.12.8, Ch5 Remark 5.2.8, Ch8
  homological, Ch9 9.4.6, and #7090 auditing the docstring wave itself). No
  source changes.

- **3 chore PRs** — #7021 (`items.json` reconciliation to the then-3-sorry
  state), #7080 (routing stale-claimed #6340 → replan as #7084, since
  `finrank_g_three` is false over char 2), and a skill note.

**Frontier trajectory.** The genuine-sorry count has fallen
6 (2026-07-17) → 4 (2026-07-18) → 3 (2026-07-20, #7021) → **1 (2026-07-21)**.
Unlike earlier windows — where the frontier *shifted* as much as it shrank,
abstract sorries splitting into concrete cruxes — this window is a clean
collapse: the Ch4 SO(3) classification and Ch8 Ext-bridge arcs closed outright,
leaving `finrank_g_three` as the sole survivor.

## Project status

The formalization of Etingof's *Introduction to Representation Theory* is now
**proof-complete modulo a single owned `sorry`**:

- **1 genuine `sorry`** — `finrank_g_three` (Problem 2.16.3(a)), claimed under
  #7084. The mathematical content is the dimension of the third G₂
  positive-nilpotent Lie algebra; the remaining work is a bounded proof over
  `char ≠ 2`.
- **2 book-disavowed `proof_wanted`** — Ado's theorem and complete reducibility
  for finite-dimensional `sl`-representations; recorded honestly, not project
  debt.
- **0 axioms, 0 admits, 0 `True`-stubs.**

The natural remaining work is therefore **not new formalization**. It is:

1. **Landing #7084** — discharge the lone `finrank_g_three` sorry (with the
   `(2:k) ≠ 0` hypothesis; note the char-2 falsity in the statement). Once it
   merges, the tree is genuinely sorry-free and a successor summarize turn should
   re-run the depth counter, confirm **0**, and record the sorry-free milestone.
2. **Documentation / consistency polish** — the docstring-fidelity sweep is
   winding down (#7090 audits its accuracy); a final pass can normalize the
   residual historical `items.json` status vocabulary (`proved` /
   `proof_complete` / `formalized` / `accepted` → a single canonical label) if a
   planner decides the inconsistency is worth a dedicated reconciliation issue.
   That is cleanup, not a correctness gap.

For the next planner: the project is at its terminus. Prioritize #7084; beyond
it, only status/documentation consistency remains.

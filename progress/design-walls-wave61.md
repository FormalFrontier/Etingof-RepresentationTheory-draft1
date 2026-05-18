# Wave 61 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress.
Wave 60 recorded **1 wall** (Wall 1, 6 waves stale) + **1 active
chain** (Wall 3, four pivots) + **1 ongoing chain** (Schur-Weyl,
C-tier mid-flight) + **1 active decomposition cascade** (D̃₅
Sub B) + **1 coordination note** (two broken-main events in
one day). Wave 61 records the **same** structural shape with
**no movement** on the four pre-existing items, **zero
broken-main events** (first broken-main-free wave since wave
60), and **1 new active infrastructure topic** (per-(F, Q) ↔
Theorem 2.1.2 bridge).

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework — STATUS UNCHANGED (7 WAVES STALE)

**Context.** Identical to waves 54-60. The current single-nilpotent-
twist construction is provably **false** for every m ≥ 1: the e_m
direction peels off as a 1-dim summand at the center. Reference
counter-examples in
`progress/indecomposability-framework-investigation.md`. No
mathematical movement since wave 54.

**File state (line positions unchanged from wave 60).** Same 5
sorries with the same line positions as at wave-60 close — the
wave-61 hoists (#2862, #2863) and proj-sibling lemmas (#2871)
landed in `FieldGenericInfiniteType.lean` / `FieldGenericStar.lean`
/ `FieldGenericD5Tilde.lean` (not the Ẽ files), so the Wall 1 line
positions in `FieldGenericETilde6.lean` and `FieldGenericETilde7.lean`
were not perturbed:

- `Chapter6/InfiniteTypeConstructions.lean:3344` —
  `etilde6v2Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/InfiniteTypeConstructions.lean:3599` —
  `etilde7Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/InfiniteTypeConstructions.lean:3826` —
  `t125Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/FieldGenericETilde6.lean:299` —
  `etilde6Rep_kQ_isIndecomposable` (F-generic, **on active
  chain**).
- `Chapter6/FieldGenericETilde7.lean:281` —
  `etilde7Rep_kQ_isIndecomposable` (F-generic, **on active
  chain**).

**Options** (unchanged from wave 54-60):

- **Option A — Book's Tits-form / orbit-counting argument.** Lean
  algebraic-geometry infrastructure (orbit maps, dimension of
  quasi-projective varieties, constructible sets). Estimate: 6+
  months.

- **Option B — Stronger explicit construction.** Couple multiple
  arms to block D/F with independent nilpotents, or add a γ-style
  center-to-center iso bridging independent arms. Estimate: weeks
  per case. **Wave-61 structural case sharpened further.** The
  wave-60 D̃₅ Sub B helpers (`embed_sum_zero_F`, `center_decomp_F`,
  `core_F`, `core3_F`, `gamma_containment_F`) plus γ⁻¹ closed
  forms (PR #2843) plus the wave-61 projection-sibling lemmas
  (`d5tildeRep_F_proj1/2/3/4`) now form a reusable scaffolding
  for any γ-style argument. The Ẽ₆ and Ẽ₇ files have analogous
  structure but no current Option-B body. The per-(F, Q)
  infrastructure work has reduced the Wall 1 ask to "produce
  an Option-B body for two stub theorems whose statement is
  already final."

- **Option C — Subgraph transfer for non-sporadic T(p,q,r).**
  Partial step; does not close the sporadic Ẽ₆ / Ẽ₇ / Ẽ₈ but
  would lighten the load on the F-generic chain. Wave 59-61 PRs
  (#2799, #2798, #2805, #2802, #2813, #2871, #2882) demonstrate
  this works end-to-end for non-sporadic cases.

**Blocks (unchanged wave 61).** 2 live F-generic Ch6 sorries +
1 Ch2 downstream (Theorem 2.1.2 forward bridge, transitively
gated on the F-generic Wall 1 stubs). The wave-61 bridge-
infrastructure work has further isolated this dependency: every
other piece of the bridge is independently solvable, so the
forward bridge closure forecast is now gated **solely** on Wall 1
plus #2877 outer assembly plus the per-(F, Q) K_{1,4}/T(1,2,5)
chain issues.

**Status.** Issue #2436 still `human-oversight`, `replan`.
**Seventh** consecutive wave with no Wall 1 movement. Still the
longest-running open item in the project by a large margin.

**Asks of Kim:** select Option A, B, A+C, or B+C. The wave-61
infrastructure work has reduced the ambiguity around Option B's
landing site: a stronger Option-B construction would slot into
two specific files (`FieldGenericETilde6.lean`,
`FieldGenericETilde7.lean`) whose statements are already final
and whose helper-lemma needs ~80% overlap with the D̃₅ chain's
already-landed helpers.

---

## Wall 2 — `dTildeDim` vertex-type strategy — REMOVED

**Status: still closed.** No regression in wave 61. Ch6 Wall 2
line remains sorry-free.

---

## Wall 3 — Garnir straightening induction measure — STATUS UNCHANGED

**Context.** `garnir_twisted_in_lower_span`
(`SpechtModuleBasis.lean:1958`) — combinatorial heart of the
straightening theorem. Promoted from "wall" to "chain" in wave 56
with the dominance-induction commitment (PR #2529). Wave 59
recorded four strategic pivots (per-fibre retired; TP ∈ V^λ first
retired; col-std-at-tabloid retired; single-coordinate Q_high
retired in favor of cross-region `(q, r)`-domain involution).

**Wave-61 movement:** None. No PRs touched Ch5 Wall-3 territory
this wave. R2.b.i (#2769) remains `replan` with the R3-bis
cross-region involution strategy. R2.b.ii (#2770), R2.c (#2703)
remain blocked. PR #2550 (C.1.a.ii pigeonhole, line-1487 helper)
remains `CONFLICTING`, now **~24 days** static, in the pr-repair
queue.

**Status.** Same as wave 60. Three issues in the active chain
(#2769 replan, #2770 blocked, #2703 blocked); one open PR carry-
over (#2550, ~24d). The strategy doc
`progress/r3-bis-residual-cancellation.md` is unchanged and ready
for the next worker.

**Risk (cumulative).** Pigeonhole PR #2550 has been static for
~24 days with the pr-repair flow dispatched every cycle. The
rebase surface keeps growing (now over wave-60 PRs #2802, #2813,
#2835, #2843, #2844 + wave-61 PRs #2862, #2863, #2871, #2878,
#2882). At some point a fresh re-implementation will be cheaper
than a rebase; the meditate skill could investigate this. Wave 61
adds further pressure but does not change the structural
recommendation.

---

## D̃₅ Sub B decomposition cascade — UNCHANGED ACTIVE TOPIC (file layout consolidated this wave)

**Context.** D̃₅ per-(F, Q) indecomposability (#2804) was
decomposed in wave 60 into a 4-level tree:

```
#2804 (parent, replan after deliverable 1 lands)
  ├── PR #2835 (helpers + API stubs)                            ─── DONE (wave 60)
  └── #2834 (proof body — replan after PR #2843)
       ├── PR #2843 (γ⁻¹ closed-form identities)                ─── DONE (wave 60)
       └── #2839 (main proof body — replan after wave-60 split)
            ├── #2850 sub-A (leaf equalities)                   ─── replan after PR #2854
            │    ├── PR #2854 (canonical orientation)           ─── DONE (wave 60)
            │    └── #2853 sub-A2 (31 non-canonical cases)      ─── blocked on #2850
            └── #2851 sub-B (assembly via N-invariance)         ─── blocked on #2850
```

**Wave-61 movement (file-layout consolidation, no body proof):**

- **PR #2862** — Hoist `core_F` / `core3_F` /
  `gamma_containment_F` from section-internal positions in
  `FieldGenericInfiniteType.lean` to top-level. Pre-step for
  #2853's 31-case fill so each non-canonical case can reuse the
  helpers by short name.
- **PR #2863** — Hoist `embed_sum_zero_F` / `center_decomp_F`
  from `FieldGenericD5Tilde` to `FieldGenericStar`. Pre-step
  for #2853 enabling re-use of the star-side helpers.
- **PR #2871** — Add projection-based reversed-leaf-edge sibling
  lemmas (`d5tildeRep_F_proj1/2`, `d5tildeRep_F_proj3/4`) to
  give #2853's 31 case-splits a clean projection-variant API
  surface. Pre-step for #2853.
- **PR #2861** — Audit of wave-60 D̃₅ Sub B cascade helpers
  (PRs #2835 / #2843 / #2854). PASS verdict.
- **PR #2866** — Audit of wave-61 hoist PRs (#2862, #2863).
  PASS verdict.
- **PR #2879** — Audit of wave-61 proj-sibling lemmas (#2871).
  PASS verdict.

**Wave-61 net effect on the cascade:** 0 body-proof closures,
0 sorries added/removed, file layout fully consolidated, all 6
sorry line positions shifted by the hoists/sibling lemmas (now
at lines 926/928/930/932/934 for the 5 reversed-edge cases and
line 981 for the indecomposability stub). The structural ordering
is unchanged; #2853 and #2851 remain blocked on #2850 (sub-A).

**Closure path (unchanged).** Once #2853 lands (31 cases via the
canonical-case template) and #2851 lands (assembly via N-
invariance + leaf equalities), #2804 closes. Estimate: still
1-2 waves of focused worker sessions. Wave-61 made the worker's
mechanical surface cleaner but did not advance the body proof.

**Closure-gating risk for wave 62.** With #2877 (the new
per-(F, Q) bridge outer assembly) now competing for worker
attention, the D̃₅ Sub B chain risks slipping further behind.
The next planner should consider whether to file #2853 as a
top-priority worker item or whether to encourage #2877
decomposition first.

---

## Per-(F, Q) ↔ Theorem 2.1.2 bridge — NEW ACTIVE TOPIC (NOT A WALL)

**Context.** The per-(F, Q) bridge is the structural workaround
for Wall 1 — instead of waiting for the framework decision on
the ℂ-specific Ẽ₆ / Ẽ₇ / Ẽ₈ stubs, the project has been
mechanically refactoring each forbidden-subgraph theorem into a
per-(F, Q) version that is `IsIndecomposable` for every field F
and every orientation Q. The bridge closes Theorem 2.1.2's
forward direction (line 173 in `Chapter2/Theorem2_1_2.lean`)
once all six per-(F, Q) leaves are proven.

**State at wave 60 close.** Five of six leaves either proven or
under active development. Two API stubs missing (K_{1,4} via
`star_not_finite_type_per_kQ`, T(1,2,5) via
`t125_not_finite_type_per_kQ`). The outer assembly
`not_posdef_infinite_type_per_kQ` unfiled.

**Wave-61 movement:**

- **PR #2878** — Per-(F, Q) API stubs for K_{1,4}
  (`Chapter6/FieldGenericStar.lean:542-556`) and T(1,2,5)
  (`Chapter6/FieldGenericT125.lean:39-53`). Both stubs have
  final statements; bodies are `sorry`, tracked by existing
  per-(F, Q) chain issues (#2789/#2801 for K_{1,4}; #2793 for
  T(1,2,5)).
- **PR #2882** — Per-(F, Q) subgraph dispatch wrappers in
  `Chapter6/FieldGenericCycle.lean` and
  `Chapter6/FieldGenericStar.lean`:
  - `chordless_cycle_infinite_type_per_kQ` (~22 lines).
  - `triangle_infinite_type_per_kQ` (~30 lines, k=3
    specialisation).
  - `star_subgraph_not_finite_type_per_kQ` (~55 lines, inherits
    the sorry chain of `star_not_finite_type_per_kQ`).
- **PR #2885** — Audit of #2878 + #2882. PASS verdict, with the
  audit explicitly confirming two of #2877's sub-deliverables
  (D2.cycle ~150 lines, D2.degree4 ~50 lines) are worker-ready
  as standalone sub-issues.

**State at wave 61 close.**

| Component | Status | PR / Issue |
|-----------|--------|------------|
| 6 forbidden-subgraph leaves | 4 proven, 2 API stubs | PR #2799/#2798/#2809/#2810 + PR #2878 (stubs) |
| 3 subgraph dispatch wrappers | All proven | PR #2882 |
| Outer assembly (`not_posdef_infinite_type_per_kQ`) | Unfiled / worker-ready | #2877 (D2) |
| Bridge close (line 173) | Open | #2877 (D3) |

**Closure path.** A worker claiming #2877 needs to:

1. **Decompose** #2877 into sub-issues per its own body's
   recommendation. The audit at #2885 confirmed D2.cycle
   (~150 lines) and D2.degree4 (~50 lines) are worker-ready
   standalone sub-issues. D2.adjacent (~150), D2.singleBranch
   (~305), D2.nonAdjacent (~927), and D2.acyclic (~51) round
   out the 6 sub-deliverables.
2. **Write each sub-issue body** to mirror the corresponding
   `_kQ`-free helper in
   `Chapter6/InfiniteTypeConstructions.lean`, but dispatching
   through `subgraph_infinite_type_transfer_per_kQ` +
   per-(F, Q) leaf theorems.
3. **Assemble D2** (the outer `not_posdef_infinite_type_per_kQ`)
   from the sub-deliverables (~50 lines once all sub-issues
   land).
4. **Close D3** (the line-173 forward bridge) by combining D2
   with `HasFiniteRepresentationType.finite_dimVectors`
   (`Chapter2/Theorem2_1_2.lean:111`). ~50 lines.

**Why this is not (yet) a wall.** The bridge has a clear closure
path. The only structural blocker is the Wall 1 framework
decision (#2436), which gates two of the six leaves
(`etilde6_not_finite_type_per_kQ`,
`etilde7_not_finite_type_per_kQ`). But the bridge work itself
can proceed against the stubbed leaves — the assembly dispatches
by name and inherits any unproven `sorry` chain transparently.

**Estimate.** Best plausible 1-wave delta on the bridge:
#2877 D2.degree4 + D2.cycle land + D2.adjacent + D2.acyclic
land + outer assembly + D3 → bridge closes modulo the Wall 1
stubs (which would themselves close out only on Kim's
framework decision). Pessimistic: #2877 sits unclaimed for
another wave waiting on planner decomposition.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:399`) — top-of-chain. Wave 55
scoped the chain; wave 58 closed C-3 and most of C-4; wave 59
closed C-4a-i sub-β tier and landed C-4c body; wave 60 saw no
movement; wave 61 saw **no movement on the chain.**

**Sub-issue status (unchanged vs wave 60):**

- All C-4 path items closed at the body level.
- γ-cluster (γ.A PR #2694 `CONFLICTING` ~16d, γ.B #2693
  unclaimed `replan`) still blocks aggregation.
- C-4a aggregation (`SchurModuleSimple.lean:148` / #2708)
  blocked on γ-cluster.
- Part C (#2493) → #5 (#2482) → #6 (#2483) → line 399 cascade
  unchanged.

**Why still not a wall.** Same as wave 60. The chain stays on
schedule pending γ-cluster + aggregation. No framework decision
needed; the residual work is mechanical given the wave-59 body
closures.

**Remaining sorries on the chain (unchanged):**
- `iso_of_formalCharacter_eq_schurPoly`
  (`FormalCharacterIso.lean:399`) — closes via #2483.
- `schurModuleSubmodule_isSimple_centralizer`
  (`SchurModuleSimple.lean:148`) — closes via #2708.

---

## Active design topic (not a wall) — Mathlib upstream forwarding pattern

**Context.** When the project produces a lemma that belongs
naturally in Mathlib (not specific to the book), we open a
Mathlib PR, then keep a local copy until the upstream lands.
This is the "Mathlib upstream tracker" pattern, first instanced
by #2564 (`MvPolynomial.eq_of_eval_eq_on_gl`,
Mathlib PR 38583, blocked on external review).

**Wave-61 movement.** PR #2867 (doc) forwarded
`LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero` to Mathlib
PR 39523, mirroring the same pattern. Tracker #2841 was filed
when the wave-59 lemma landed locally; PR #2867 documents the
forward and the deliverable is now complete on our side.

**Status of trackers at wave 61 close:**

- **#2564** (`MvPolynomial.eq_of_eval_eq_on_gl`): blocked on
  external Mathlib PR #38583 merge. Awaiting Mathlib review.
- **#2841** (`LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero`):
  on-our-side complete; blocked on external Mathlib PR #39523
  merge.

**Why not a wall.** Trackers are external-blocked but documented;
the local copies work and the project does not depend on the
Mathlib merge for any internal progress.

**Pattern note.** Wave-61 documented this pattern as a
repeatable workflow (open Mathlib PR → file in-project tracker
with forward link → remove local copy on Mathlib merge). Future
upstream-suitable lemmas should follow this template.

---

## Meta

- **Wall 1** still needs Kim's framework decision (#2436); **7**
  consecutive waves with no movement. 5 framework-wall sorries
  total (3 dead ℂ-specific + 2 live F-generic, line positions
  unchanged this wave). The wave-61 per-(F, Q) bridge-
  infrastructure work has further isolated this dependency:
  every other piece of the bridge is independently solvable, so
  Wall 1 now bottlenecks two leaves out of six.
- **Wall 2** closed.
- **Wall 3** chain unchanged from wave 60 (4 pivots historic,
  R2.b.i `replan` with concrete strategy doc; PR #2550 ~24d
  static).
- **Schur-Weyl chain** unchanged from wave 60. γ.A
  (PR #2694 CONFLICTING ~16d), γ.B (#2693 replan unclaimed for
  6+ waves), C-4a aggregation (#2708 blocked).
- **D̃₅ Sub B cascade.** File layout consolidated this wave
  (hoists in #2862/#2863, proj-sibling lemmas in #2871). 0 body-
  proof movement. Closure path unchanged: #2853 + #2851 →
  #2804. Estimate still 1-2 waves to close #2804.
- **Per-(F, Q) ↔ Theorem 2.1.2 bridge (new wave-61 active
  topic).** Infrastructure layer complete (6 leaves with
  callable names; 3 dispatch wrappers). Outer assembly
  #2877 is worker-ready per #2885 audit.
- **Mathlib upstream forwarding (new wave-61 active topic).**
  Wave 61 documented the pattern via PR #2867 (mirroring
  PR #2564 → #2841). Future upstream-suitable lemmas follow the
  same template.
- **Zero broken-main events.** First wave since wave 60 with no
  broken-main events. Audit cadence (4 of 10 substantive PRs)
  + smaller scoped refactors (vs. wave 60's #2844 file split)
  appear to have eliminated the wave-60 coordination signal.

**For comparison with wave 60:** wave 60 had **1 wall** (Wall 1,
6 waves stale) + **1 active chain** (Wall 3, four pivots) +
**1 ongoing chain** (Schur-Weyl, C-4 body closed) + **1 active
decomposition cascade** (D̃₅ Sub B) + **1 coordination note**
(two broken-main events).

Wave 61 has the **same** structural shape with **status-unchanged**
on Walls 1/2/3 + Schur-Weyl chain + D̃₅ cascade (but D̃₅ file
layout consolidated), plus **1 new active infrastructure topic**
(per-(F, Q) ↔ Theorem 2.1.2 bridge) and **1 active forwarding-
pattern note** (Mathlib upstream trackers). The wave-60
coordination note (two broken-main events) is **retired** — wave
61 had zero broken-main events.

The wave-61 distinguishing event is the **per-(F, Q) bridge
infrastructure landing**. With the wrappers and leaf API stubs
in place, the bridge's only remaining structural ambiguity is
the outer assembly (#2877). A worker claiming #2877 should
decompose it per the audit at #2885; the closure path from there
to the line-173 forward bridge is concrete.

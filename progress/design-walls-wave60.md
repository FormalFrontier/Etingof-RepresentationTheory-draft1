# Wave 60 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress.
Wave 59 recorded one wall (Wall 1, 5 waves stale) + one active
chain (Wall 3, four pivots) + one ongoing chain (Schur-Weyl, C-tier
mid-flight) + one new active topic (Ch2 forward bridge per-(F, Q)
refactor). Wave 60 records the **same** structural shape with **no
movement** on the four pre-existing items, **two broken-main
events** worth recording but not classifying as a wall, and a **new
active decomposition cascade** (D̃₅ Sub B) on the per-(F, Q) chain.

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework — STATUS UNCHANGED (6 WAVES STALE)

**Context.** Identical to waves 54-59. The current single-nilpotent-
twist construction is provably **false** for every m ≥ 1: the e_m
direction peels off as a 1-dim summand at the center. Reference
counter-examples in
`progress/indecomposability-framework-investigation.md`. No
mathematical movement since wave 54.

**File state (line positions shifted, content unchanged).** Wave
59 had 5 framework-wall sorries; wave 60 has the same 5 sorries
with two line shifts caused by PR #2844 (file split of
`FieldGenericInfiniteType.lean`):

- `Chapter6/InfiniteTypeConstructions.lean:3344` —
  `etilde6v2Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/InfiniteTypeConstructions.lean:3599` —
  `etilde7Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/InfiniteTypeConstructions.lean:3826` —
  `t125Rep_isIndecomposable` (ℂ-specific, dead w.r.t. forward
  bridge).
- `Chapter6/FieldGenericETilde6.lean:299` (was 283) —
  `etilde6Rep_kQ_isIndecomposable` (F-generic, **on active
  chain**).
- `Chapter6/FieldGenericETilde7.lean:281` (was 292) —
  `etilde7Rep_kQ_isIndecomposable` (F-generic, **on active
  chain**).

The line shifts come from PR #2844 (split of
`FieldGenericInfiniteType.lean` into shared / cycle / star modules)
and the broken-main repairs (#2848, #2852) that landed in the same
neighbourhood. Mathematical content of both F-generic stubs is
unchanged.

**Options** (unchanged from wave 54-59):

- **Option A — Book's Tits-form / orbit-counting argument.** Lean
  algebraic-geometry infrastructure (orbit maps, dimension of
  quasi-projective varieties, constructible sets). Estimate: 6+
  months.

- **Option B — Stronger explicit construction.** Couple multiple
  arms to block D/F with independent nilpotents, or add a γ-style
  center-to-center iso bridging independent arms. Estimate: weeks
  per case. **Wave-60 structural case strengthened:** the
  Section-5 helper-lemma scaffolding now landed for D̃₅
  (`embed_sum_zero_F`, `center_decomp_F`, `gamma_from_embed1_F`,
  `gamma_from_embed2_F`, `core_F`, `core3_F`,
  `gamma_containment_F`) is ~80% structurally compatible with
  the helper-lemma needs of Ẽ₆ and Ẽ₇. A stronger F-generic
  construction would slot cleanly into all three files.

- **Option C — Subgraph transfer for non-sporadic T(p,q,r).**
  Partial step; does not close the sporadic Ẽ₆ / Ẽ₇ / Ẽ₈ but
  would lighten the load on the F-generic chain. Wave 59 + 60
  PRs (#2799, #2798, #2805, #2802, #2813) demonstrate this works
  end-to-end for non-sporadic cases.

**Blocks (unchanged wave 60).** 2 live F-generic Ch6 sorries +
1 Ch2 downstream (Theorem 2.1.2 forward bridge, transitively
gated on the F-generic Wall 1 stubs).

**Status.** Issue #2436 still `human-oversight`, `replan`. **Sixth**
consecutive wave with no Wall 1 movement. Still the
longest-running open item in the project by a large margin.

**Asks of Kim:** select Option A, B, A+C, or B+C. The wave-60
D̃₅ Sub B cascade demonstrates that Option B's per-graph workload
is concrete and decomposable into weeks-of-effort focused
workitems. The dependency on Wall 1 has not narrowed since wave
59, but the **per-graph closure pattern** has been shown end-to-end
for the cycle and K_{1,4} D̃₄ F-generic cases (waves 58-59), and
is well-underway for K_{1,4} Q-ext and D̃₅ (wave 60).

---

## Wall 2 — `dTildeDim` vertex-type strategy — REMOVED

**Status: still closed.** No regression in wave 60. Ch6 Wall 2
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

**Wave-60 movement:** None. No PRs touched Ch5 Wall-3 territory
this wave. R2.b.i (#2769) remains `replan` with the R3-bis
cross-region involution strategy. R2.b.ii (#2770), R2.c (#2703)
remain blocked. PR #2550 (C.1.a.ii pigeonhole, line-1487 helper)
remains `CONFLICTING`, now **~24 days** static, in the pr-repair
queue.

**Status.** Same as wave 59. Three issues in the active chain
(#2769 replan, #2770 blocked, #2703 blocked); one open PR carry-
over (#2550, ~24d). The strategy doc
`progress/r3-bis-residual-cancellation.md` is unchanged and ready
for the next worker.

**Risk.** Pigeonhole PR #2550 has been static for ~24 days with
the pr-repair flow dispatched every cycle. The rebase surface
keeps growing (now over PR #2802, #2813, #2835, #2843, #2844 from
this wave). At some point a fresh re-implementation will be
cheaper than a rebase; the meditate skill could investigate this.

---

## D̃₅ Sub B decomposition cascade — NEW ACTIVE TOPIC (NOT A WALL)

**Context.** D̃₅ per-(F, Q) indecomposability (#2804) was
wave-59's only remaining unblocked per-(F, Q) sub-theorem in
flight (construction landed PR #2813, indecomposability deferred).
Wave 60 produced a 4-level decomposition tree from this single
parent in the span of a working day:

```
#2804 (parent, replan after deliverable 1 lands)
  ├── PR #2835 (helpers + API stubs)                            ─── DONE
  └── #2834 (proof body — replan after PR #2843)
       ├── PR #2843 (γ⁻¹ closed-form identities)                ─── DONE
       └── #2839 (main proof body — replan after wave-60 split)
            ├── #2850 sub-A (leaf equalities)                   ─── replan after PR #2854
            │    ├── PR #2854 (canonical orientation)           ─── DONE
            │    └── #2853 sub-A2 (31 non-canonical cases)      ─── blocked on #2850
            └── #2851 sub-B (assembly via N-invariance)         ─── blocked on #2850
```

**Wave-60 movement (all on this cascade):**

- **PR #2835** — D̃₅ per-(F, Q) helpers + API stubs (partial).
  Adds the `d5tildeRep_kQ_isIndecomposable` API stub at line 856
  of `FieldGenericD5Tilde.lean` (1 new sorry, tracked by #2851
  via #2839 sub-B).
- **PR #2843** — Closed-form γ⁻¹ identity helpers
  (`gammaInv_embed1_plus_embed2_F`,
  `gammaInv_embed1_plus_embedNshift_F`). These are the
  Section 5d identities needed for the reversed-central-edge
  case (3→2) of the leaf-equality theorem.
- **PR #2854** — Canonical-orientation case of
  `d5tildeRep_kQ_leaf_equalities` + API stub. Proves the
  all-canonical orientation branch (1 of 32) inline (~240 lines,
  mirroring the ℂ-source proof in
  `InfiniteTypeConstructions.lean:1569-1834`) and leaves the
  remaining 31 as 5 hierarchical case-split sorries (lines 802,
  804, 806, 808, 810) on the reversed-at-level-k branches
  (16+8+4+2+1 sub-cases respectively, tracked by #2853).

**Key patterns landed:**

1. **Hierarchical orientation case-split via 2-step destructure.**
   ```lean
   rcases hOrient_edge a b h_adj with hQab | hQba
   · obtain ⟨e⟩ := hQab    -- canonical direction
   · obtain ⟨e⟩ := hQba    -- reversed direction
   ```
   The 2-step `rcases ... | ...` then `obtain ⟨e⟩ :=` is
   necessary because `obtain ⟨e⟩ | ⟨e⟩ := ...` does not
   recursively destructure `Nonempty` in this context. Source
   `FieldGenericCycle.lean:210-235`. Pattern is reused 5 times
   in PR #2854.

2. **Per-edge invariance helpers with explicit `x` binding.**
   The `∀ x ∈ W ⟨source, _⟩, ...` binder syntax fails because
   Lean can't determine `x`'s type before the membership
   predicate. The fix:
   ```lean
   have hW_e (x : Fin (m + 1) → F) (hx : x ∈ W ⟨source, _⟩) :
       target_map x ∈ W ⟨target, _⟩ := by ...
   ```

3. **Reusable helper-lemma scaffolding** (`embed_sum_zero_F`,
   `center_decomp_F`, `gamma_from_embed1_F`, `gamma_from_embed2_F`,
   `core_F`, `core3_F`, `gamma_containment_F`). The
   canonical-case proof exercises all seven; #2853's 31
   non-canonical cases will compose them with projection-based
   variants (`starFirst_F`, `starSecond_F` from
   `FieldGenericStar.lean`) and the γ⁻¹ closed forms from
   PR #2843.

**Closure path.** Once #2853 lands (31 cases via the canonical-
case template) and #2851 lands (assembly via N-invariance + leaf
equalities), #2804 closes. Estimate: 1-2 waves of focused worker
sessions. This is the **most actively decomposed unblocked
sub-chain** in the project at the wave-60 boundary.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:399`) — top-of-chain. Wave 55
scoped the chain; wave 58 closed C-3 and most of C-4; wave 59
closed C-4a-i sub-β tier and landed C-4c body; wave 60 saw **no
movement on the chain** beyond cosmetic hygiene (PR #2842
heartbeat reductions in `youngSym_action_vanishes_off_block`).

**Sub-issue status (unchanged vs wave 59):**

- All C-4 path items closed at the body level.
- γ-cluster (γ.A PR #2694 `CONFLICTING` ~15d, γ.B #2693
  unclaimed `replan`) still blocks aggregation.
- C-4a aggregation (`SchurModuleSimple.lean:148` / #2708)
  blocked on γ-cluster.
- Part C (#2493) → #5 (#2482) → #6 (#2483) → line 399 cascade
  unchanged.

**Why still not a wall.** Same as wave 59. The chain stays on
schedule pending γ-cluster + aggregation. No framework decision
needed; the residual work is mechanical given the wave-59 body
closures.

**Remaining sorries on the chain (unchanged):**
- `iso_of_formalCharacter_eq_schurPoly`
  (`FormalCharacterIso.lean:399`) — closes via #2483.
- `schurModuleSubmodule_isSimple_centralizer`
  (`SchurModuleSimple.lean:148`) — closes via #2708.

---

## Active design topic (not a wall) — Ch2 forward bridge per-(F, Q) refactor

**Context.** `not_posdef_not_HasFiniteRepresentationType`
(`Chapter2/Theorem2_1_2.lean:173`). Wave 59 noted that deliverable
1 of #2774 landed (PR #2805) and that deliverables 2 + 3 awaited
re-scoping. Wave 60 saw **no movement on this topic** — neither
the deliverable-2/3 sub-issues, nor any of the per-(F, Q) residual
sub-theorems (#2789 K_{1,4} canonical, #2793 T(1,2,5), #2789),
moved status. However:

- **#2800 (K_{1,4} Q-ext construction) closed** via PR #2802 this
  wave (wave-59 carry-over). #2801 (indecomposability) could
  move from blocked to `replan` now that its construction
  dependency is resolved.
- **#2803 (D̃₅ construction) closed** via PR #2813 this wave
  (wave-59 carry-over). #2804 (indecomposability) is now the
  active D̃₅ Sub B cascade above.

**Net effect on line 173:** Same as wave 59. The assembly pattern
is concrete; the bridge transitively still depends on each per-(F, Q)
sub-theorem's `IsIndecomposable` step, two of which (Ẽ₆/Ẽ₇)
carry the F-generic Wall 1 stubs.

---

## Two broken-main events in one day — coordination note

Not a wall, but worth recording. Wave 60 saw **two broken-main
events** on 2026-05-17/18:

1. **First event (#2846, repaired by PR #2848 within ~1.5h):**
   The squash-merge of PR #2802 (K_{1,4} Q-ext direction-aware
   projections, ~3 hours static at wave-59 close) onto the
   wave-60-fresh PR #2844 file split exposed a name collision:
   `starRep_kQ` ended up referenced from a moved-out location,
   plus the new `etilde6LeafProj_F` and `starFirst_F` were
   duplicated across modules. Worker session 5b8dd06f filed
   the breakage as #2846, skipped its parent #2823, and repair
   landed via PR #2848 (move `starRep_kQ` to `FieldGenericStar`,
   dedupe D̃₅ projections).

2. **Second event (broken by stale rebase of #2839, repaired
   by PR #2852 within ~1h):** A rebase of the in-flight
   #2839 branch (the D̃₅ Sub B parent before its decomposition
   into #2850/#2851) against the same wave-60 file split
   referenced Section 5b/5d incorrectly. Repair landed via
   PR #2852.

**Pattern.** Both events were caused by the same root: a
long-lived branch interacting with a same-day file refactor
(PR #2844, +793/-644, 8 files). The pr-repair flow caught both
within hours and did not require human escalation. The
**underlying coordination cost** — concurrent in-flight PRs
against a file undergoing a rename — is recurring (this is the
second wave with a refactor that triggered broken-main; cf.
wave 57 / wave 58 had similar but smaller events).

**Mitigation candidate.** Coordination already runs
`coordination check-blocked` / `check-has-pr` cycles; a possible
addition is a `coordination warn-rebase-needed` step that posts
a comment on any open PR whose `files_changed` overlaps a freshly-
merged PR's. Out of scope for this summarize, but the meditate
skill could investigate the cost/benefit.

---

## Meta

- **Wall 1** still needs Kim's framework decision (#2436); **6**
  consecutive waves with no movement. 5 framework-wall sorries
  total (3 dead ℂ-specific + 2 live F-generic, line positions
  shifted by PR #2844 file split).
- **Wall 2** closed.
- **Wall 3** is a chain unchanged from wave 59 (4 pivots historic,
  R2.b.i `replan` with concrete strategy doc; PR #2550 ~24d
  static).
- **Schur-Weyl chain** unchanged from wave 59. γ.A
  (PR #2694 CONFLICTING ~15d), γ.B (#2693 replan unclaimed),
  C-4a aggregation (#2708 blocked). 4 PRs from closure of
  line 399.
- **Ch2 forward bridge** unchanged from wave 59. #2774
  deliverables 2 + 3 still unfiled. Two of the wave-59 in-flight
  constructions closed this wave (#2800 K_{1,4} Q-ext via
  PR #2802, #2803 D̃₅ via PR #2813); the corresponding
  indecomposability issues (#2801, #2804) are next.
- **D̃₅ Sub B cascade (new wave-60 active topic).** Most actively
  decomposed sub-chain in the project. 4-level decomposition
  tree, 6 new sorries all on the active path, all tracked by
  issues. Closure path visible; estimate 1-2 waves to close #2804.
- **Two broken-main events in one day.** Coordination signal,
  not a wall. Both repaired within hours via pr-repair flow.

**For comparison with wave 59:** wave 59 had **1 wall** (Wall 1,
restructured, 5 waves stale) + **1 active chain** (Wall 3, four
pivots) + **1 ongoing chain** (Schur-Weyl, C-4 body closed) +
**1 new active topic** (Ch2 forward bridge per-(F, Q) refactor).

Wave 60 has the **same** structural shape with **status-unchanged**
on the four pre-existing items, plus **1 new active decomposition
topic** (D̃₅ Sub B cascade) and **1 coordination note** (two
broken-main events).

The wave-60 distinguishing event is the **D̃₅ Sub B 4-level
decomposition cascade**. It is the most actively decomposed
unblocked sub-chain in the project at wave-60 close. Net sorry
count rose 10 → 16 (third consecutive non-monotone wave since
wave 55's plateau at 7) — entirely on the D̃₅ Sub B path, all
tracked by issues with concrete closure paths. The structural
shape of the project has not changed; the visible work has
shifted from broad per-(F, Q) chain construction (wave 59) to
narrow per-orientation case proof on a single graph (wave 60).

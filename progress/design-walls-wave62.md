# Wave 62 — Design Walls Inbox

Snapshot of framework-level decisions blocking worker progress.
Wave 61 recorded **1 wall** (Wall 1, 7 waves stale) + **1 active
chain** (Wall 3, four pivots) + **1 ongoing chain** (Schur-Weyl,
C-tier mid-flight) + **1 active decomposition cascade** (D̃₅
Sub B) + **1 new active infrastructure topic** (per-(F, Q) ↔
Theorem 2.1.2 bridge). Wave 62 records the **same** structural
shape with **status unchanged** on Walls 1/2/3 + Schur-Weyl
chain + D̃₅ cascade, **zero broken-main events** (second
consecutive broken-main-free wave), and **a major milestone on
the per-(F, Q) bridge**: the bridge proof itself
(`Theorem2_1_2.lean:173` ⇒
`not_posdef_not_HasFiniteRepresentationType`) is now
**sorry-free**. The residual bridge work is local to two new
per-(F, Q) leaf stubs.

---

## Wall 1 — Ẽ_n / T(p,q,r) indecomposability framework — STATUS UNCHANGED (8 WAVES STALE)

**Context.** Identical to waves 54-61. The current single-nilpotent-
twist construction is provably **false** for every m ≥ 1: the e_m
direction peels off as a 1-dim summand at the center. Reference
counter-examples in
`progress/indecomposability-framework-investigation.md`. No
mathematical movement since wave 54.

**File state (line positions unchanged from wave 61).** Same 5
sorries with the same line positions as at wave-61 close — the
wave-62 work landed in `FieldGenericAssembly.lean`,
`FieldGenericTpqr.lean`, and Chapter 2, not the Wall 1 files:

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

**Options** (unchanged from wave 54-61):

- **Option A — Book's Tits-form / orbit-counting argument.** Lean
  algebraic-geometry infrastructure (orbit maps, dimension of
  quasi-projective varieties, constructible sets). Estimate: 6+
  months.

- **Option B — Stronger explicit construction.** Couple multiple
  arms to block D/F with independent nilpotents, or add a γ-style
  center-to-center iso bridging independent arms. Estimate: weeks
  per case. **Wave-62 structural case sharpened further.** With
  the wave-62 closure of the per-(F, Q) outer assembly +
  Theorem 2.1.2 forward bridge, Wall 1 is now the **largest
  remaining architectural blocker on the forward direction's
  end-to-end closure**. The Wall 1 ask is structurally the
  smallest it has ever been: produce an Option-B body for
  exactly two stub theorems whose statements are final and
  whose helper scaffolding (γ⁻¹ closed forms from PR #2843;
  projection-sibling lemmas from PR #2871; top-level helper
  hoists from PRs #2862/#2863) is already in place.

- **Option C — Subgraph transfer for non-sporadic T(p,q,r).**
  Partial step; does not close the sporadic Ẽ₆ / Ẽ₇ / Ẽ₈ but
  would lighten the load on the F-generic chain. Wave 59-62 PRs
  (#2799, #2798, #2805, #2802, #2813, #2871, #2882, #2891, #2897,
  #2900, #2903, #2906, #2912, #2914, #2916, #2917, #2918, #2921)
  demonstrate this works end-to-end for non-sporadic cases.

**Blocks (unchanged wave 62).** 2 live F-generic Ch6 sorries +
the per-(F, Q) chain transitively. The wave-62 bridge closure
isolates Wall 1 as the largest structural blocker on the
forward direction. Every other piece of the bridge is
independently solvable; Wall 1 is the only piece that needs
human input.

**Status.** Issue #2436 still `human-oversight`, `replan`.
**Eighth** consecutive wave with no Wall 1 movement. Still the
longest-running open item in the project by a large margin.

**Asks of Kim:** select Option A, B, A+C, or B+C. The wave-62
bridge closure has reduced the ambiguity around Option B's
landing site to the absolute minimum: two specific files
(`FieldGenericETilde6.lean`, `FieldGenericETilde7.lean`) whose
statements are already final and whose helper-lemma needs are
already met by the D̃₅ chain's already-landed helpers. The
chosen approach can be implemented without touching any other
file in the project.

---

## Wall 2 — `dTildeDim` vertex-type strategy — REMOVED

**Status: still closed.** No regression in wave 62. Ch6 Wall 2
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

**Wave-62 movement:** None. No PRs touched Ch5 Wall-3 territory
this wave. R2.b.i (#2769) remains `replan` with the R3-bis
cross-region involution strategy. R2.b.ii (#2770), R2.c (#2703)
remain blocked. PR #2550 (C.1.a.ii pigeonhole, line-1487 helper)
remains `DIRTY`, now **~25 days** static, in the `/repair`
queue.

**Status.** Same as wave 61. Three issues in the active chain
(#2769 replan, #2770 blocked, #2703 blocked); one open PR carry-
over (#2550, ~25d). The strategy doc
`progress/r3-bis-residual-cancellation.md` is unchanged and ready
for the next worker.

**Risk (cumulative).** Pigeonhole PR #2550 has been static for
~25 days with the `/repair` flow dispatched every cycle. The
rebase surface keeps growing (now over wave-60/61 PRs plus
wave-62 PRs #2891, #2897, #2900, #2903, #2906, #2912, #2914,
#2916, #2917, #2918, #2921). At some point a fresh
re-implementation will be cheaper than a rebase; the meditate
skill could investigate this. Wave 62 adds further pressure but
does not change the structural recommendation.

---

## D̃₅ Sub B decomposition cascade — UNCHANGED ACTIVE TOPIC (NO WAVE-62 MOVEMENT)

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

**Wave-62 movement: none.** No PRs touched the D̃₅ Sub B chain
this wave. The 6 file-position-stable D̃₅ sorries
(`FieldGenericD5Tilde.lean:926/928/930/932/934/981`) carry
forward identically from wave 61.

**Closure path (unchanged).** Once #2853 lands (31 cases via the
canonical-case template) and #2851 lands (assembly via N-
invariance + leaf equalities), #2804 closes. Estimate: still
1-2 waves of focused worker sessions.

**Closure-gating risk for wave 63.** With wave-62 closing the
bridge architecture, the next critical-path item is **#2922**
(non-adjacent branches leaf-case helper, unclaimed) — which is
~700 lines of new code per the issue body. If the next planner
cycle does not prioritise scheduling a D̃₅ Sub B worker session
alongside #2922, the D̃₅ chain will slip a third consecutive
wave without movement.

---

## Per-(F, Q) ↔ Theorem 2.1.2 bridge — ARCHITECTURE CLOSED THIS WAVE (residual work local)

**Context.** The per-(F, Q) bridge is the structural workaround
for Wall 1 — instead of waiting for the framework decision on
the ℂ-specific Ẽ₆ / Ẽ₇ / Ẽ₈ stubs, the project has been
mechanically refactoring each forbidden-subgraph theorem into a
per-(F, Q) version that is `IsIndecomposable` for every field F
and every orientation Q. The bridge closes Theorem 2.1.2's
forward direction (`Chapter2/Theorem2_1_2.lean:153-179`) once
all six per-(F, Q) leaves are proven.

**State at wave 61 close.** Six leaves with callable names
(4 proven, 2 API stubs). Three dispatch wrappers proven. Outer
assembly `not_posdef_infinite_type_per_kQ` unfiled. Forward
bridge sorry at `Theorem2_1_2.lean:173` still open.

**Wave-62 movement (architecture closure):**

The wave's body-proof work decomposed into a pre-split planner
pattern: each of the six D2 sub-helpers of #2877 was filed as a
standalone sub-issue and landed as a 1-session worker target.

- **PR #2891** — `degree_ge_4_infinite_type_per_kQ` (D2.degree4).
- **PR #2897** — `graph_with_list_cycle_infinite_type_per_kQ`
  (D2.cycle).
- **PR #2900** — `adjacent_branches_infinite_type_per_kQ`
  (D2.adjacent).
- **PR #2903** — `single_branch_not_posdef_infinite_type_per_kQ`
  (D2.singleBranch outer) + leaf-case stub.
- **PR #2906** — `single_branch_leaf_case_per_kQ` leaf-leaf cases
  + `single_branch_leaf_case_both_extend_per_kQ` four-way
  dispatcher stub (Tpqr.lean:1286). Decomposed into sub-A
  (#2907), sub-B (#2908), sub-C (#2909), sub-D (#2910).
- **PR #2912** — sub-D `single_branch_leaf_both_extend_t122_per_kQ`
  via T(1,2,2)=D₅ posdef contradiction.
- **PR #2914** — sub-B partial
  `single_branch_leaf_both_extend_b3leaf_per_kQ` (c₂-leaf E₇ +
  d₂-leaf E₈ posdef cases).
- **PR #2916** — sub-C partial
  `single_branch_leaf_both_extend_b2leaf_per_kQ` (c₃-leaf E₇ +
  d₃-leaf E₈ posdef cases).
- **PR #2917** — `embed_t125_in_tree_per_kQ` shared helper +
  d₂-extends case (closes sub-B's partial sorry).
- **PR #2918** — d₃-extends case via the shared helper (closes
  sub-C's partial sorry).
- **PR #2921** — D2 outer assembly
  `not_posdef_infinite_type_per_kQ` +
  `acyclic_branch_not_posdef_infinite_type_per_kQ` +
  Theorem 2.1.2 forward bridge body
  (`not_posdef_not_HasFiniteRepresentationType` at line 153-179).
  Transferred one sorry from `Theorem2_1_2.lean:173` to
  `FieldGenericAssembly.lean:96` (`non_adjacent_branches_…_per_kQ`
  stub).

Audits:
- **PR #2894** — Audit of #2891 (D2.degree4 placement +
  `[IsAlgClosed F]` carriage). PASS.
- **PR #2926** — Audit of #2921 (outer assembly + Theorem 2.1.2
  bridge). PASS on all 5 deliverables (statement fidelity,
  bridge correctness, sorry-propagation accounting, etc.).

**State at wave 62 close.**

| Component | Status | PR / Issue |
|-----------|--------|------------|
| 6 forbidden-subgraph leaves | 4 proven, 2 API stubs | PR #2799/#2798/#2809/#2810 + PR #2878 (stubs) |
| 3 subgraph dispatch wrappers | All proven | PR #2882 |
| D2.degree4 / D2.cycle / D2.adjacent / D2.singleBranch outer / D2.acyclic | **All proven** | PR #2891 / #2897 / #2900 / #2903 / #2921 |
| D2.singleBranch leaf-case (outer + leaf-leaf) | **Proven** | PR #2906 |
| D2.singleBranch sub-B/C/D | **Proven** | PR #2912 / #2914 + #2917 / #2916 + #2918 |
| D2.singleBranch sub-A (Ẽ₇ embed arms ≥ 3) | PR #2911 in `/repair` (DIRTY) | #2907 |
| D2.singleBranch both-extend dispatcher | **Stub** (Tpqr.lean:1286) | #2905 chain |
| D2.nonAdjacent `non_adjacent_branches_infinite_type_per_kQ` | **Stub** (FieldGenericAssembly.lean:96) | #2919 → #2922 + #2923 |
| Outer assembly `not_posdef_infinite_type_per_kQ` | **Proven** | PR #2921 |
| Bridge close `not_posdef_not_HasFiniteRepresentationType` | **Proven** | PR #2921 |

**Closure path (post-wave-62).** The forward direction's end-to-
end closure transitively requires:

1. **#2922** lands → unblocks **#2923** → closes
   `FieldGenericAssembly.lean:96`.
2. PR #2911 lands → closes `Tpqr.lean:1286` (small wiring).
3. **Wall 1 framework decision (#2436)** → unblocks
   `FieldGenericETilde6.lean:299` + `FieldGenericETilde7.lean:281`.
4. **#2789 / #2801** chains close → unblock
   `FieldGenericStar.lean:557` (K_{1,4}).
5. **#2793** chain closes → unblocks `FieldGenericT125.lean:53`
   (T(1,2,5)).
6. **#2853 + #2851** close → unblock
   `FieldGenericD5Tilde.lean:926-934/981` (D̃₅ Sub B).

After all six conditions, the forward direction has no `sorry`
on any reachable proof obligation.

**Why this is closed at the architecture level.** Pre-wave-62,
the bridge body itself had a `sorry`; reading the proof
top-down hit an architectural gap. Post-wave-62, the body is
sorry-free; reading top-down hits only leaf-level stubs whose
statements are final. The structural ambiguity around how the
bridge connects to its leaves is **fully resolved**.

**Estimate.** Best plausible 1-wave delta on the bridge: #2922
+ #2923 land, PR #2911 lands → bridge has only the four
pre-existing leaf chains left to close. Pessimistic: #2922 sits
unclaimed (substantial new design work, ~700 lines per its
issue body) and the bridge holds at the current state.

---

## Active design topic (not a wall) — Schur-Weyl chain

**Context.** `iso_of_formalCharacter_eq_schurPoly`
(`Chapter5/FormalCharacterIso.lean:399`) — top-of-chain. Wave 55
scoped the chain; wave 58 closed C-3 and most of C-4; wave 59
closed C-4a-i sub-β tier and landed C-4c body; waves 60-62 saw
no movement.

**Sub-issue status (unchanged vs wave 61):**

- All C-4 path items closed at the body level.
- γ-cluster (γ.A PR #2694 `DIRTY` ~17d, γ.B #2693
  unclaimed `replan`) still blocks aggregation.
- C-4a aggregation (`SchurModuleSimple.lean:148` / #2708)
  blocked on γ-cluster.
- Part C (#2493) → #5 (#2482) → #6 (#2483) → line 399 cascade
  unchanged.

**Why still not a wall.** Same as wave 61. The chain stays on
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

**Status of trackers at wave 62 close (unchanged from wave 61):**

- **#2564** (`MvPolynomial.eq_of_eval_eq_on_gl`): blocked on
  external Mathlib PR #38583 merge. Awaiting Mathlib review.
- **#2841** (`LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero`):
  on-our-side complete; blocked on external Mathlib PR #39523
  merge.

**Why not a wall.** Trackers are external-blocked but documented;
the local copies work and the project does not depend on the
Mathlib merge for any internal progress.

---

## Meta

- **Wall 1** still needs Kim's framework decision (#2436); **8**
  consecutive waves with no movement. 5 framework-wall sorries
  total (3 dead ℂ-specific + 2 live F-generic). The wave-62
  bridge closure has made Wall 1 the single largest
  architectural blocker on Theorem 2.1.2 forward direction —
  every other piece of the bridge is independently solvable.
- **Wall 2** closed.
- **Wall 3** chain unchanged from wave 61 (4 pivots historic,
  R2.b.i `replan` with concrete strategy doc; PR #2550 ~25d
  static).
- **Schur-Weyl chain** unchanged from wave 61. γ.A
  (PR #2694 DIRTY ~17d), γ.B (#2693 replan unclaimed for
  7+ waves), C-4a aggregation (#2708 blocked).
- **D̃₅ Sub B cascade.** Unchanged from wave 61. No body-proof
  movement; layout consolidated since wave 61.
- **Per-(F, Q) ↔ Theorem 2.1.2 bridge** **architecture closed
  this wave.** Outer assembly + bridge proof both sorry-free
  (PR #2921). Residual work transferred into local
  per-(F, Q) leaf chains (#2919 non-adjacent branches via #2922
  + #2923; #2905 chain via #2907 → PR #2911 in `/repair`).
- **Zero broken-main events.** Second consecutive
  broken-main-free wave. The pre-split planner pattern (each
  D2 sub-helper as a standalone sub-issue) appears to have
  reproduced the small-blast-radius pattern that wave 61
  established.
- **Audit ratio dropped to 2:11 (review:feature) this wave**
  vs wave 61's 4:6 and wave 60's 4:8. The drop reflects the
  pre-split pattern producing more feature work, but it is a
  signal: only PRs #2891 and #2921 received explicit audits.
  The other five wave-62 features (#2897, #2900, #2903, #2906,
  #2912) shipped without dedicated review issues. If body-
  proof work continues at this rate, planners should consider
  scheduling catch-up audits.

**For comparison with wave 61:** wave 61 had **1 wall** (Wall 1,
7 waves stale) + **1 active chain** (Wall 3) + **1 ongoing
chain** (Schur-Weyl) + **1 active decomposition cascade**
(D̃₅ Sub B) + **1 active infrastructure topic**
(per-(F, Q) ↔ Theorem 2.1.2 bridge).

Wave 62 has the **same** structural shape with status-unchanged
on Walls 1/2/3 + Schur-Weyl chain + D̃₅ cascade, plus a **major
milestone**: the **per-(F, Q) ↔ Theorem 2.1.2 bridge architecture
is closed** (bridge proof sorry-free; residual work transferred
into local per-(F, Q) leaf stubs).

The wave-62 distinguishing event is the **architecture closure of
the per-(F, Q) bridge** (PR #2921 + the D2 sub-helper cascade).
With the bridge body sorry-free, the forward direction's
remaining work is **entirely local to per-(F, Q) leaf bodies**,
and Wall 1 — pending for 8 consecutive waves — is now the single
largest architectural blocker.

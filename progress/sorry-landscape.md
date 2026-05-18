# Sorry Landscape Analysis — Wave 62

Generated 2026-05-19 by summarize session (issue #2927, cycle `9ea12755`).

## Summary

**19 sorries** across 11 files (vs 18/10 at wave 61). Net delta vs
wave 61: **+1 sorry, +1 file.** The headline event of the wave is
that **`Chapter2/Theorem2_1_2.lean:173` closed** — the forward
bridge `not_posdef_not_HasFiniteRepresentationType` is now sorry-
free for the first time since it was filed. Theorem 2.1.2's
remaining work is now the per-(F, Q) leaf bodies in Chapter 6, not
the Chapter 2 bridge itself.

The +1 net is the bookkeeping cost of decomposing the bridge:

- **−1**: `Chapter2/Theorem2_1_2.lean:173`
  (`not_posdef_not_HasFiniteRepresentationType`) closed by PR #2921.
- **+1**: `Chapter6/FieldGenericAssembly.lean:96`
  (`non_adjacent_branches_infinite_type_per_kQ` stub introduced by
  PR #2921 as the only `sorry` it added back; tracked by #2919 →
  #2922 + #2923).
- **+1**: `Chapter6/FieldGenericTpqr.lean:1286`
  (`single_branch_leaf_case_both_extend_per_kQ` four-way dispatcher
  stub introduced by PR #2906; tracked by the #2905 chain — sub-A
  #2907 → PR #2911 in `/repair`, sub-B/C/D landed).
- Sub-B/C partial sorries from PR #2914 / #2916 (+2) were each
  closed within the wave by the follow-ups PR #2917 / #2918 (−2,
  net 0).

**Wave 62 was a body-proof-dominant wave with zero broken-main
events.** Counted from wave 61's close (2026-05-18T11:17Z) to this
snapshot (2026-05-18T22:46Z), the wave was ~11.5 hours of agent
activity producing **13 substantive PRs** — substantially above
the 10-PR triggering threshold. Of the 13 substantive PRs, **11
are feature PRs** (#2891, #2897, #2900, #2903, #2906, #2912, #2914,
#2916, #2917, #2918, #2921) and **2 are review audits** (#2894,
#2926), both returning PASS verdicts. The audit cadence shifted
from wave 61's 4-out-of-10 review skew toward feature-heavier work
as planners pre-split #2877 into per-helper sub-issues each of
which became a one-session worker target.

The wave-62 story has two parts:

- **Theorem 2.1.2 forward bridge closed at the assembly level.**
  The per-(F, Q) outer assembly `not_posdef_infinite_type_per_kQ`
  landed (PR #2921) along with `acyclic_branch_not_posdef_…_per_kQ`,
  and the bridge `not_posdef_not_HasFiniteRepresentationType`
  in `Chapter2/Theorem2_1_2.lean:153-179` is now wired to the
  assembly with a sorry-free body. The remaining work on the
  forward direction lives **exclusively in the per-(F, Q) leaf
  bodies**, not in the bridge architecture.

- **`single_branch_leaf_case_per_kQ` cascade landed in five
  pieces.** Outer stub (PR #2903), leaf-leaf cases + both-extend
  stub (PR #2906), then sub-D direct T(1,2,2)=D₅ posdef closure
  (PR #2912), sub-B partial + d₂-extends follow-up (PR #2914 +
  #2917), sub-C partial + d₃-extends follow-up (PR #2916 + #2918).
  Sub-A (arms ≥ 3 Ẽ₇ embed, PR #2911) is in `/repair` with merge
  conflicts and is the only remaining gap in the cascade.

288 Lean source files in `EtingofRepresentationTheory/`, of which
**288 are sorry-free out of 299 total (96.3%)**. **582/583 items
(99.8%) sorry-free** per `progress/items.json` — unchanged from
wave 60. (Wave 61's hand-count of 581/583 reflected a transient
addition of two per-(F, Q) API stub theorems into the item ledger
that was not preserved into the canonical `items.json`; the
ground-truth item count is unchanged across waves 60-62.)

**Definition-level sorries: 0.** All mathematical objects are
still constructed.

### Key story for wave 62

- **Wall 1 (Ẽ/T framework, #2436):** **status unchanged.** Still
  5 sorries (3 ℂ-specific dead code in
  `InfiniteTypeConstructions`, 2 F-generic live on the per-(F, Q)
  chain). Line positions identical to wave 61. **Eighth**
  consecutive wave with no Wall 1 movement. The wave-62 body
  proofs sharpen the Wall 1 cost further: with the outer
  assembly + bridge proof now sorry-free, the active forward
  path through Theorem 2.1.2 is gated on **(a)** the four
  per-(F, Q) leaf chains (K_{1,4}, T(1,2,5), D̃₅, Ẽ₆/Ẽ₇) and
  **(b)** finishing the non-adjacent branches helper. Wall 1
  bottlenecks two of those four leaves (Ẽ₆/Ẽ₇) directly.

- **Wall 2 (D̃_n indecomposability):** **STILL CLOSED.** No
  regression.

- **Wall 3 (Ch5 `SpechtModuleBasis.lean`, 2 sorries):** unchanged
  this wave. R2.b.i (#2769) still in `replan` with the R3-bis
  cross-region involution strategy from PR #2779. R2.b.ii (#2770)
  / R2.c (#2703) still blocked. PR #2550 (line 1487 helper,
  C.1.a.ii) still `DIRTY` — **~25 days static**, in the
  `/repair` queue with no successful repair yet.

- **Schur-Weyl chain (Ch5):** **status unchanged.** Same 2 sorries
  (`SchurModuleSimple.lean:148` C-4a aggregation;
  `FormalCharacterIso.lean:399` top-of-chain). γ.A (PR #2694)
  still `DIRTY`, **~17 days static**. γ.B (#2693) still
  unclaimed `replan` for 7+ waves.

- **D̃₅ Sub B chain (wave-60 cascade):** **status unchanged.** No
  body-proof movement in wave 62. The 5 D̃₅ leaf-equality sorries
  remain at lines 926/928/930/932/934 in
  `d5tildeRep_kQ_leaf_equalities`; the API stub remains at line
  981 in `d5tildeRep_kQ_isIndecomposable`. #2853 / #2851 still
  `blocked` on #2850.

- **Per-(F, Q) ↔ Theorem 2.1.2 bridge (Ch2 #2877):** **outer
  assembly + bridge proof closed.** PR #2921 landed
  `not_posdef_infinite_type_per_kQ` (outer assembly) plus
  `acyclic_branch_not_posdef_…_per_kQ` plus the bridge body in
  `Chapter2/Theorem2_1_2.lean:153-179`. The bridge proof itself
  is **sorry-free**; the residual transitively-pending work is
  in the per-(F, Q) leaf chain (#2919 non-adjacent branches,
  #2905 single-branch both-extend, plus Wall 1 / D̃₅ Sub B /
  K_{1,4} / T(1,2,5) chains).

- **D2.single_branch sub-case cascade (#2905 chain):** four of
  five sub-cases landed within the wave (outer + sub-B/C/D +
  helper `embed_t125_in_tree_per_kQ`). Sub-A (#2907 → PR #2911)
  remains in `/repair` with merge conflicts.

### Merges since wave 61 (19 PRs, 2026-05-18T11:17Z → 2026-05-18T22:46Z)

Of the 19 PRs merged in this window, **6 are planner / progress
no-ops** (#2890, #2893, #2896, #2899, #2902, #2925) and **0 are
pure repairs** — wave 62 had no broken-main events. The remaining
13 substantive PRs are tabulated chronologically:

| PR    | Time (UTC)       | Title (truncated)                                                                | Sorry Impact |
|-------|------------------|----------------------------------------------------------------------------------|--------------|
| #2891 | 05-18 12:00      | feat(Ch6 #2889): `degree_ge_4_infinite_type_per_kQ`                              | Feature (no net sorry change; closes D2.degree4 leg of #2877) |
| #2894 | 05-18 13:30      | review(Ch6 #2892): audit PR #2891 — D2.degree4 placement + `[IsAlgClosed F]`     | Audit (PASS) |
| #2897 | 05-18 14:00      | feat(Ch6 #2895): `graph_with_list_cycle_infinite_type_per_kQ`                    | Feature (no net sorry change; closes D2.cycle leg) |
| #2900 | 05-18 16:05      | feat(Ch6 #2898): `adjacent_branches_infinite_type_per_kQ`                        | Feature (no net sorry change; closes D2.adjacent leg) |
| #2903 | 05-18 17:00      | feat(Ch6 #2901): `single_branch_not_posdef_infinite_type_per_kQ` + leaf-case stub | **+1** (`single_branch_leaf_case_per_kQ` outer stub at Tpqr.lean) |
| #2906 | 05-18 18:30      | feat(Ch6 #2904 partial): `single_branch_leaf_case_per_kQ` leaf-leaf cases + both-extend stub | **+1** (`single_branch_leaf_case_both_extend_per_kQ` stub at Tpqr.lean:1286); −1 (outer stub from #2903 closed) |
| #2912 | 05-18 19:30      | feat(Ch6 #2910): `single_branch_leaf_both_extend_t122_per_kQ` — T(1,2,2)=D₅ posdef | Feature (sub-D direct, no net sorry change) |
| #2914 | 05-18 20:00      | feat(Ch6 #2908 partial): `single_branch_leaf_both_extend_b3leaf_per_kQ`          | **+1** (partial sub-B sorry, closed in same wave by #2917) |
| #2916 | 05-18 20:30      | feat(Ch6 #2909 partial): `single_branch_leaf_both_extend_b2leaf_per_kQ`          | **+1** (partial sub-C sorry, closed in same wave by #2918) |
| #2917 | 05-18 21:00      | feat(Ch6 #2913): `embed_t125_in_tree_per_kQ` shared helper + d₂-extends case     | **−1** (closes sub-B partial from #2914) |
| #2918 | 05-18 21:30      | feat(Ch6 #2915): d₃-extends case via shared helper (sub-C)                       | **−1** (closes sub-C partial from #2916) |
| #2921 | 05-18 22:00      | feat(Ch2 #2877 partial): `not_posdef_infinite_type_per_kQ` outer assembly + Theorem 2.1.2 forward bridge | **−1** (closes Theorem2_1_2.lean:173); **+1** (`non_adjacent_branches_infinite_type_per_kQ` stub at FieldGenericAssembly.lean:96) |
| #2926 | 05-18 22:30      | review(Ch2 #2924): audit PR #2921 — outer assembly + Theorem 2.1.2 bridge        | Audit (PASS, 5 deliverables) |

Planner / progress no-op PRs (6): #2890, #2893, #2896, #2899,
#2902, #2925.

**Net counts (wave 62):**
- Substantive feature PRs: 11 (#2891, #2897, #2900, #2903, #2906,
  #2912, #2914, #2916, #2917, #2918, #2921).
- Audit / review: 2 (#2894, #2926) — both PASS.
- Broken-main repair: 0.
- Planner-cycle no-op progress notes: 6 (#2890, #2893, #2896,
  #2899, #2902, #2925).
- Raw sorry count: 18 → 19. Files with sorries: 10 → 11.
- Net change: **+1 sorry, +1 file.** In-wave additions then
  closures cancelled to 0; the persistent net is decomposition
  bookkeeping (outer bridge → assembly stub transfer + new
  single-branch both-extend dispatcher).
- Body proofs closed: 6 substantive leaves
  (`degree_ge_4`, `graph_with_list_cycle`, `adjacent_branches`,
  `single_branch_not_posdef` outer, `single_branch_leaf_case`
  outer, `single_branch_leaf_both_extend_t122`).
- Headline closure: `Chapter2/Theorem2_1_2.lean:173`
  (`not_posdef_not_HasFiniteRepresentationType`) is now
  **sorry-free** for the first time since it was filed.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 61 |
|---------|---------|-------|--------------------|
| Ch2     | 0       | 0     | **−1 sorry, −1 file** (forward bridge closed) |
| Ch5     | 4       | 3     | 0                  |
| Ch6     | 15      | 8     | +2 sorries, +2 files |
| Ch9     | 0       | 0     | 0                  |

Wave-62 sorry motion: the Ch2 forward-bridge sorry closed; in
exchange the Ch6 assembly file picked up the
`non_adjacent_branches_…_per_kQ` stub and the new `Tpqr.lean` file
picked up the `single_branch_leaf_case_both_extend_per_kQ`
dispatcher stub. Two new Ch6 files (`FieldGenericTpqr.lean`,
`FieldGenericAssembly.lean`) appear in the sorry ledger; the
Ch2 forward-bridge file `Theorem2_1_2.lean` exits it.

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 3 sorries: WALL 1 ℂ-SPECIFIC (dead w.r.t. forward bridge)

Unchanged from wave 61. All three are refuted-as-stated pointers
to Wall 1; the wave-59 per-(F, Q) refactor moved the active
dependency path off these ℂ-specific stubs but they remain in
source.

| Line | Theorem | Status |
|-----:|---------|--------|
| 3344 | `etilde6v2Rep_isIndecomposable (m hm)` | Refuted; bypassed by F-generic chain |
| 3599 | `etilde7Rep_isIndecomposable (m hm)`  | Refuted; bypassed by F-generic chain |
| 3826 | `t125Rep_isIndecomposable (m hm)`     | Refuted; bypassed by F-generic chain |

Reference: `progress/indecomposability-framework-investigation.md`.
Framework issue: #2436 (`human-oversight`, `replan`, **8 waves stale**).

### FieldGenericD5Tilde (Ch6) — 6 sorries: D̃₅ SUB B CASCADE (UNCHANGED)

Unchanged in count, tracking, and line positions from wave 61.
All six introduced wave 60 by PRs #2835 + #2854; line positions
shifted by wave-61 PRs #2862 / #2863 / #2871; no movement in
wave 62.

| Line (wave 62) | Line (wave 61) | Theorem / branch | Tracking issue | Notes |
|---------------:|---------------:|------------------|----------------|-------|
| 926 | 926 | `d5tildeRep_kQ_leaf_equalities`, e53-reversed branch (3→5, 1 sub-case)  | #2853 | Reversed leaf edge — needs `starSecond_F` projection variant |
| 928 | 928 | `d5tildeRep_kQ_leaf_equalities`, e43-reversed branch (3→4, 2 sub-cases) | #2853 | Reversed leaf edge — needs `starFirst_F` projection variant |
| 930 | 930 | `d5tildeRep_kQ_leaf_equalities`, e23-reversed branch (3→2, 4 sub-cases) | #2853 | Reversed central edge — needs γ⁻¹ identities (`gammaInv_embed*_F`) |
| 932 | 932 | `d5tildeRep_kQ_leaf_equalities`, e12-reversed branch (2→1, 8 sub-cases) | #2853 | Reversed leaf edge — needs `starSecond_F` projection variant |
| 934 | 934 | `d5tildeRep_kQ_leaf_equalities`, e02-reversed branch (2→0, 16 sub-cases) | #2853 | Reversed leaf edge — needs `starFirst_F` projection variant |
| 981 | 981 | `d5tildeRep_kQ_isIndecomposable`     | #2851 (via #2839 sub-B) | API stub. Body deferred to #2851 (assembly via N-invariance + propagation) |

### FieldGenericETilde6 (Ch6) — 1 sorry: WALL 1 F-GENERIC (line position unchanged)

- **Line 299** — `etilde6Rep_kQ_isIndecomposable (F Q hOrient m hm)`.
  Line position **unchanged** from wave 61. **On the active
  dependency path** for `etilde6_not_finite_type_per_kQ` →
  Theorem 2.1.2 forward bridge.

### FieldGenericETilde7 (Ch6) — 1 sorry: WALL 1 F-GENERIC (line position unchanged)

- **Line 281** — `etilde7Rep_kQ_isIndecomposable (F Q hOrient m hm)`.
  Line position **unchanged** from wave 61. Same framework-wall
  inheritance as Ẽ₆. **Also on the active dependency path** for
  the per-(F, Q) assembly.

### FieldGenericStar (Ch6) — 1 sorry: K_{1,4} per-(F, Q) API STUB (UNCHANGED)

- **Line 557 — `star_not_finite_type_per_kQ` body.** Introduced
  wave 61 by PR #2878. The theorem statement is final; only the
  body is `sorry`. Tracked by the existing per-(F, Q) K_{1,4}
  chain issues #2789 (canonical orientation) + #2801
  (Q-extension indecomposability), both still `replan`. **On the
  active dependency path** — consumed by
  `star_subgraph_not_finite_type_per_kQ` and from there by
  `not_posdef_infinite_type_per_kQ`. Line position shifted by
  one (556 → 557) due to a `let _ := hOrient` placeholder added
  with PR #2882; mathematical content unchanged.

### FieldGenericT125 (Ch6) — 1 sorry: T(1,2,5) per-(F, Q) API STUB (UNCHANGED)

- **Line 53 — `t125_not_finite_type_per_kQ` body.** Introduced
  wave 61 by PR #2878. The theorem statement is final; only the
  body is `sorry`. Tracked by #2793 (T(1,2,5) per-(F, Q),
  `replan`). **On the active dependency path** — consumed
  directly by `not_posdef_infinite_type_per_kQ`.

### FieldGenericTpqr (Ch6) — 1 sorry: SINGLE-BRANCH BOTH-EXTEND DISPATCHER (NEW THIS WAVE)

- **Line 1286 — `single_branch_leaf_case_both_extend_per_kQ`
  body.** Introduced wave 62 by PR #2906. The theorem is the
  four-way dispatcher for the case "both arms `a₂`, `a₃` at
  `v₀`'s leaf neighbour extend (q, r ≥ 2)" — it should split
  into:
  * both arms ≥ 3 → embed Ẽ₇ via `etilde7_not_finite_type_per_kQ`
    (sub-A, tracked by **#2907 → PR #2911 in `/repair`**).
  * one arm length 2, other ≥ 5 → embed T(1,2,5) via
    `t125_not_finite_type_per_kQ` (closed by sub-B PR #2914 +
    follow-up PR #2917).
  * one arm length 2, other ≥ 3 → embed T(1,2,5) via shared
    helper (closed by sub-C PR #2916 + follow-up PR #2918).
  * ADE shapes T(1,2,2/3/4) → contradict `h_not_posdef` (closed
    by sub-D PR #2912).
  The remaining `sorry` is the assembled dispatch wiring once
  sub-A lands.

### FieldGenericAssembly (Ch6) — 1 sorry: NON-ADJACENT BRANCHES STUB (NEW THIS WAVE)

- **Line 96 — `non_adjacent_branches_infinite_type_per_kQ`
  body.** Introduced wave 62 by PR #2921 as the only `sorry`
  the outer-assembly PR added back into the codebase. The
  theorem statement is final; the body is `sorry` pending
  the per-(F, Q) version of `non_adjacent_branches_infinite_type`
  (`Chapter6/InfiniteTypeConstructions.lean:9682-10608`).
  Tracked by **#2919** (parent) → **#2922** (sub-A1
  leaf-neighbour helper, unclaimed) **+ #2923** (sub-A2 outer
  assembly + neighbour extraction + Ẽ₆ all-deg-2 case, blocked
  on #2922).

### SpechtModuleBasis (Ch5) — 2 sorries: WALL 3 CHAIN ACTIVE (unchanged)

- **Line 1487 — `twistedPolytabloid_pigeonhole_pair`** (C.1.a.ii).
  Unchanged in status. Issue #2543 still `has-pr` (PR #2550 open,
  `DIRTY`, static since 2026-04-24 — **~25 days**). In the
  `/repair` queue but no repair has succeeded; rebase surface has
  grown further over wave-62 Ch6 PRs (#2891, #2897, #2900, #2903,
  #2906, #2921).

- **Line 1958 — `garnir_twisted_in_lower_span`** (final Wall 3
  sorry). Unchanged. Semantically blocked on R2.b → R2.c. R2.b.i
  (#2769) `replan` with the R3-bis cross-region involution strategy
  (`progress/r3-bis-residual-cancellation.md`).

### SchurModuleSimple (Ch5) — 1 sorry: SCHUR-WEYL C-4a AGGREGATION (unchanged)

- **Line 148 — `schurModuleSubmodule_isSimple_centralizer`**.
  Unchanged from wave 61. Tracking issue #2708 blocked on
  γ.A (PR #2694, `DIRTY`) + γ.B (#2693, unclaimed `replan`).

### FormalCharacterIso (Ch5) — 1 sorry: SCHUR-WEYL TOP-OF-CHAIN (unchanged)

- **Line 399 — `iso_of_formalCharacter_eq_schurPoly`**. Unchanged
  in position. Same dependency cascade as wave 61: closes via
  `#6 (#2483) → #5 (#2482) → Part C (#2493) → C-4 aggregation
  (#2708) → γ-cluster (γ.A PR #2694 + γ.B #2693)`.

### Theorem2_1_2 (Ch2) — 0 sorries: FORWARD BRIDGE CLOSED (NEW THIS WAVE)

- **Line 173 (wave 61) — `not_posdef_not_HasFiniteRepresentationType`**
  (forward) **— CLOSED by PR #2921.** The bridge body now
  combines the outer assembly `not_posdef_infinite_type_per_kQ`
  (Chapter 6) with `HasFiniteRepresentationType.finite_dimVectors`
  (line 112) via the contrapositive direction and
  `Module.Finite.equiv`. **First wave with a sorry-free Ch2
  forward bridge.**

## Per-(F, Q) ↔ Theorem 2.1.2 bridge scoreboard

State of the bridge layer at wave 62 close:

| Component | Status | PR / Issue |
|-----------|--------|------------|
| **Leaf 1.** `cycle_not_finite_type_per_kQ`   | Proven (wave 59) | PR #2799 |
| **Leaf 2.** `degree_ge_4_not_finite_type_per_kQ`  | Proven (wave 59, via K_{1,4} D̃₄ F-generic) | PR #2798 |
| **Leaf 3.** `star_not_finite_type_per_kQ`     | API stub (wave 61, body sorry) | PR #2878; blocked on #2789/#2801 |
| **Leaf 4.** `d5tilde_not_finite_type_per_kQ`  | Conditional (D̃₅ stub `IsIndecomposable` body sorry) | PR #2813 / #2835; blocked on #2853, #2851 |
| **Leaf 5.** `etilde6_not_finite_type_per_kQ`  | Conditional (Wall 1 F-generic Ẽ₆ stub) | PR #2809; blocked on #2436 |
| **Leaf 6.** `etilde7_not_finite_type_per_kQ`  | Conditional (Wall 1 F-generic Ẽ₇ stub) | PR #2810; blocked on #2436 |
| **Leaf 7.** `t125_not_finite_type_per_kQ`     | API stub (wave 61, body sorry) | PR #2878; blocked on #2793 |
| **Wrapper A.** `chordless_cycle_infinite_type_per_kQ` | Proven (wave 61) | PR #2882 |
| **Wrapper B.** `triangle_infinite_type_per_kQ` | Proven (wave 61, k=3 specialisation of wrapper A) | PR #2882 |
| **Wrapper C.** `star_subgraph_not_finite_type_per_kQ` | Proven (wave 61, inherits Leaf 3's `sorry`) | PR #2882 |
| **D2.degree4** `degree_ge_4_infinite_type_per_kQ` | **Proven (wave 62)** | PR #2891 |
| **D2.cycle** `graph_with_list_cycle_infinite_type_per_kQ` | **Proven (wave 62)** | PR #2897 |
| **D2.adjacent** `adjacent_branches_infinite_type_per_kQ` | **Proven (wave 62)** | PR #2900 |
| **D2.singleBranch outer** `single_branch_not_posdef_infinite_type_per_kQ` | **Proven (wave 62)** | PR #2903 |
| **D2.singleBranch leaf-case** `single_branch_leaf_case_per_kQ` | **Proven outer + leaf-leaf (wave 62)** | PR #2906 (modulo `both-extend` dispatcher) |
| **D2.singleBranch leaf both-extend** `single_branch_leaf_case_both_extend_per_kQ` | **Stub (wave 62)** — sub-A pending | PR #2906; blocked on #2907 (PR #2911 in `/repair`) |
| **D2.singleBranch sub-B** `single_branch_leaf_both_extend_b3leaf_per_kQ` | **Proven (wave 62)** | PR #2914 + #2917 |
| **D2.singleBranch sub-C** `single_branch_leaf_both_extend_b2leaf_per_kQ` | **Proven (wave 62)** | PR #2916 + #2918 |
| **D2.singleBranch sub-D** `single_branch_leaf_both_extend_t122_per_kQ` | **Proven (wave 62)** | PR #2912 |
| **D2.nonAdjacent** `non_adjacent_branches_infinite_type_per_kQ` | **Stub (wave 62)** | PR #2921; tracked by #2919 → #2922 + #2923 |
| **D2.acyclic** `acyclic_branch_not_posdef_infinite_type_per_kQ` | **Proven (wave 62)** | PR #2921 |
| **Outer assembly.** `not_posdef_infinite_type_per_kQ` | **Proven (wave 62)** | PR #2921 |
| **Bridge close.** `not_posdef_not_HasFiniteRepresentationType` (Theorem 2.1.2 fwd) | **Proven (wave 62)** | PR #2921 |

**Closure-gating set as of wave-62 close.** The bridge cannot
close end-to-end without all of:
1. **#2919** (`non_adjacent_branches_infinite_type_per_kQ` body
   via #2922 + #2923). #2922 is unclaimed and the next concrete
   feature target.
2. **#2907** (`single_branch_leaf_both_extend_arms_ge3_per_kQ`,
   Ẽ₇ embed for arms ≥ 3) — PR #2911 in `/repair` with merge
   conflicts.
3. **#2436** framework decision (Wall 1) — unblocks Ẽ₆/Ẽ₇ stubs.
4. **#2789 / #2801** (K_{1,4} canonical + Q-extension
   indecomposability) — unblocks Leaf 3
   (`star_not_finite_type_per_kQ`).
5. **#2793** (T(1,2,5)) — unblocks Leaf 7
   (`t125_not_finite_type_per_kQ`).
6. **#2853** (D̃₅ Sub-A2 31 non-canonical cases) + **#2851** (D̃₅
   Sub-B assembly) — unblock Leaf 4.

The structural ordering has flipped relative to wave 61: the
bridge proof itself is now sorry-free, and the residual work is
**entirely local** to the per-(F, Q) leaf bodies. A
post-PR #2921 reader can navigate the forward-direction proof
end-to-end without encountering an architectural sorry.

## Open PRs

| PR | Status | Branch / Note |
|----|--------|---------------|
| #2911 | mergeStateStatus=DIRTY, CI SUCCESS | Ch6 `#2907` Ẽ₇ embed (arms ≥ 3); merge conflicts post-wave-62 Ch6 churn. In `/repair`. |
| #2849 | mergeStateStatus=UNSTABLE | Ch6 chore — dedupe `etilde6LeafProj_F` and `starFirst_F` post-#2802. CI flaky; in `/repair` queue (wave-60-fresh). |
| #2694 | mergeStateStatus=DIRTY, CI SUCCESS | Schur-Weyl L_i γ.A scaled-projection; **~17 days static**. |
| #2550 | mergeStateStatus=DIRTY, CI SUCCESS | Wall 3 C.1.a.ii pigeonhole; **~25 days static**, in `/repair` queue. |

PR #2694 and PR #2550 remain long carry-overs (4 and 6 waves
respectively). PR #2849 still flaky after ~9 hours in the
`/repair` queue (wave 60 → wave 62). PR #2911 is wave-62-fresh
and the highest-leverage repair target — its merge unblocks the
D2.singleBranch both-extend dispatcher wiring.

## Active / Claimed Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2927 | summarize: wave-62 sorry landscape + design-walls refresh | claimed (this session) |

## Unclaimed Issues (`agent-plan`, FIFO order)

| Issue | Title | Notes |
|-------|-------|-------|
| #2564 | Mathlib upstream tracker — `MvPolynomial.eq_of_eval_eq_on_gl` | Awaiting external Mathlib PR #38583 merge |
| #2922 | feat(Ch6 #2919 sub-A1) `non_adjacent_branches_leaf_case_per_kQ` — leaf-neighbour helper | **Next critical-path feature.** Substantial new file (~700 lines per the issue body); design genuinely new. |

## Replan / Human-oversight / Blocked Issues

Same shape as wave 61. Updates:

| Issue | Title | Status |
|-------|-------|--------|
| #2436 | Framework decision: affine Dynkin infinite type (Ẽ_n / T(p,q,r)) | replan, `human-oversight`, awaits Kim (**8 waves**) |
| #2877 | Ch2 per-(k, Q) assembly + bridge (parent) | replan after PR #2921 closed D2 outer + D3 (residual: #2919, #2905 chain) |
| #2875 | Ch2 per-(k, Q) assembly + bridge (grandparent) | replan (deliverables split into #2877, #2919, #2905 chain) |
| #2841 | Mathlib upstream tracker — `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero` | replan; on-our-side complete (PR #2867 forwarded to Mathlib PR 39523) |
| #2774 | Ch2 per-(k, Q) subgraph transfer + assembly | replan (long-superseded) |
| #2769 | Wall 3 R2.b.i cancellation involution | replan after R3-bis meditate PR #2779 |
| #2702 | Wall 3 R2.b assembly | replan |
| #2789 | K_{1,4} canonical orientation per-(F, Q) | replan; consumed by PR #2878 stub |
| #2790 | D̃₅ per-(F, Q) | replan — sub-decomposed (#2803 ✅ + #2804) |
| #2793 | T(1,2,5) per-(F, Q) | replan; consumed by PR #2878 stub |
| #2797 | K_{1,4} Q-extension per-(F, Q) | replan — sub-decomposed (#2800 ✅ + #2801) |
| #2693 | Schur-Weyl γ.B rank-1 dim count | replan, unclaimed (**7 waves**) |
| #2612 | Schur-Weyl C-4c final assembly | replan — body landed wave 59 (PR #2706); residual in #2708 |
| #2804 | D̃₅ indecomposability + per-(F, Q) | replan after PR #2835 (deliverable 1 of 2) |
| #2834 | D̃₅ Sub B proof body | replan after PR #2843 (γ⁻¹ helpers landed) |
| #2839 | D̃₅ main proof body — direction-aware case-analysis | replan after wave-60 decomposition into #2850 + #2851 |
| #2850 | D̃₅ Sub-A leaf equalities | replan after PR #2854 (canonical case landed); residual #2853 |
| #2823 | bridge `starRep_kQ ↔ starRepGen` | replan after worker session 5b8dd06f filed #2846 instead |
| #2904 | D2.singleBranch `single_branch_leaf_case_per_kQ` real body | replan after PR #2906 (leaf-leaf landed; both-extend dispatcher tracked by #2905 chain) |
| #2901 | D2.singleBranch `single_branch_not_posdef_infinite_type_per_kQ` outer | replan after PR #2903 (closed via #2904 leaf-case stub) |
| #2905 | D2.singleBranch `single_branch_leaf_case_both_extend_per_kQ` real body | replan (sub-A blocked on PR #2911; sub-B/C/D landed) |
| #2908 | D2.singleBranch sub-B both-extend (b₃ leaf, q ≥ 3) | replan after PR #2914 (partial sub-B landed; closed by #2917) |
| #2909 | D2.singleBranch sub-C both-extend (b₂ leaf, r ≥ 3) | replan after PR #2916 (partial sub-C landed; closed by #2918) |
| #2919 | D2.nonAdjacent `non_adjacent_branches_infinite_type_per_kQ` | replan after PR #2921 (transferred sorry to FieldGenericAssembly.lean:96); decomposed into #2922 + #2923 |

| Issue | Title | Blocked on |
|-------|-------|-----------|
| #2543 | Wall 3 C.1.a.ii pigeonhole | has-pr (#2550 in `/repair`, ~25d) |
| #2821 | Ch6 dedupe `etilde6LeafProj_F` / `starFirst_F` post-#2802 | has-pr (#2849 in `/repair`) |
| #2907 | D2.singleBranch sub-A Ẽ₇ embed (arms ≥ 3) | has-pr (#2911 in `/repair`, wave-62-fresh) |
| #2770 | Wall 3 R2.b.ii assembly | #2769 |
| #2703 | Wall 3 R2.c final assembly | #2702 |
| #2708 | Schur-Weyl C-4a aggregation | γ.A (#2694) + γ.B (#2693) |
| #2493 | Schur-Weyl Part C final assembly | #2708 |
| #2482 | polynomial GL_N-rep ⊕ Schur modules (#5) | #2493 |
| #2483 | close `iso_of_formalCharacter_eq_schurPoly` (#6) | #2482 |
| #2801 | K_{1,4} Q-ext indecomposability | #2800 (✅ wave 60) — could now move to replan |
| #2851 | D̃₅ Sub-B assembly via N-invariance + propagation | #2850 (sub-A) |
| #2853 | D̃₅ Sub-A2 31 non-canonical orientation cases | #2850 (sub-A) |
| #2923 | D2.nonAdjacent outer assembly + neighbour extraction + Ẽ₆ all-deg-2 | #2922 |

## Dependency Clusters

### Cluster A: Wall 3 — Garnir straightening (Ch5, 2 sorries)

**Files:** `Chapter5/SpechtModuleBasis.lean` (2 sorries).

```
PR #2550 (C.1.a.ii pigeonhole, DIRTY ~25d) ─→ kills line 1487
PR #2541 ✅ wave57 (C.1.b algorithm A leading-tabloid)
PR #2653 ✅ wave58 (sub-X bridge)
PR #2669 ✅ wave58 (R1 bridge)
PR #2707 ✅ wave59 (R2.a: twistedPolytabloid_per_q_decomp)
PR #2779 ✅ wave59 (R3-bis meditate: cross-region involution analysis)

                        Wall 3 final assembly (line 1958)
                                    ↑
                  garnir_twisted_in_lower_span ← R2.c (#2703, blocked on #2702)
                                    ↑
                  R2.b assembly via Δ ∈ V ← R2.b.ii (#2770, blocked on #2769)
                                    ↑
                  R2.b.i: residual_no_colStd_zero ← #2769 (replan; PR #2779
                                                   recommends cross-region
                                                   φ : (q, r)-domain involution)
```

No movement this wave.

### Cluster B: Schur-Weyl chain closing `iso_of_formalCharacter_eq_schurPoly` (Ch5, 2 sorries)

**Files:** `Chapter5/FormalCharacterIso.lean` (line 399 top-of-chain)
+ `Chapter5/SchurModuleSimple.lean` (line 148 C-4a aggregation).

```
β.1 ✅ wave59 PR #2689 ── β.2 ✅ wave59 PR #2697 ── β.3 ✅ wave59 PR #2795
                                          ↓
                            sub-β complete; β.3 heartbeat-cleaned wave 60 PR #2842
                                          ↓
sub-α ✅ PR #2665 ─┐
                   │
                   ▼
C-4a-i needs sub-γ (γ.A PR #2694 DIRTY ~17d + γ.B #2693 replan)
                   ↓
                C-4a (#2610) partially closed; sub-γ remnant
                   ↓
C-4a-ii ✅ wave59 PR #2698 (Module ↥B instance diamond)
                   ↓
C-4a aggregation: schurModuleSubmodule_isSimple_centralizer (#2708, blocked on γ)
       ← from wave 59 PR #2706 closing C-4c body
                   ↓
C-4b ✅ wave58 PR #2646
                   ↓
C-4c body ✅ wave59 PR #2706 (aggregation isolated)
                   ↓
            #2493 (Part C, blocked on #2708)
                   ↓
            #2482 (#5, blocked)
                   ↓
            #2483 (#6, blocked) → kills line 399
```

No movement this wave.

### Cluster C: Per-(F, Q) ↔ Theorem 2.1.2 forward bridge (Ch6, 15 sorries; Ch2, 0)

**Files:** `Chapter6/InfiniteTypeConstructions.lean` (3 dead ℂ-specific
stubs), `Chapter6/FieldGenericETilde6.lean` (1 F-generic Wall 1 stub),
`Chapter6/FieldGenericETilde7.lean` (1 F-generic Wall 1 stub),
`Chapter6/FieldGenericD5Tilde.lean` (6 D̃₅ Sub B stubs, unchanged),
`Chapter6/FieldGenericStar.lean` (1 K_{1,4} API stub, line 557),
`Chapter6/FieldGenericT125.lean` (1 T(1,2,5) API stub, line 53),
`Chapter6/FieldGenericTpqr.lean` (1 single-branch both-extend
dispatcher stub, line 1286, NEW THIS WAVE),
`Chapter6/FieldGenericAssembly.lean` (1 non-adjacent branches stub,
line 96, NEW THIS WAVE).

```
#2773 (per-(F, Q) sub-theorems for 6 forbidden subgraphs)
  ├── cycle ✅ PR #2799 (wave 59)
  ├── K_{1,4} D̃₄ F-generic ✅ PR #2798 (wave 59)
  ├── K_{1,4} canonical (#2789, replan): API stub wave 61 (PR #2878)
  ├── K_{1,4} Q-extension (#2797, replan):
  │     ├── #2800 construction ✅ PR #2802 (wave 60)
  │     └── #2801 indecomposability replan — consumed by PR #2878 stub
  ├── D̃₅ (#2790, replan):
  │     ├── #2803 construction ✅ PR #2813 (wave 60)
  │     └── #2804 indecomposability — Sub B cascade (waves 60-61):
  │            ├── PR #2835 helpers + API stubs (wave 60) [adds 1 sorry → #2851]
  │            ├── PR #2843 γ⁻¹ closed-forms (wave 60)
  │            ├── PR #2862 top-level hoist of helpers (wave 61, line shifts)
  │            ├── PR #2863 hoist `embed_sum_zero_F` / `center_decomp_F` (wave 61)
  │            ├── PR #2871 projection-based reversed-leaf siblings (wave 61)
  │            └── #2839 main proof body — wave-60 decomposition:
  │                  ├── #2850 sub-A leaf equalities
  │                  │     ├── PR #2854 canonical case (wave 60) [adds 5 sorries → #2853]
  │                  │     └── #2853 31 non-canonical cases (blocked)
  │                  └── #2851 sub-B assembly (blocked)
  ├── Ẽ₆ ✅ PR #2809 (wave 59) — carries Wall 1 F-generic sorry at FieldGenericETilde6:299
  ├── Ẽ₇ ✅ PR #2810 (wave 59) — carries Wall 1 F-generic sorry at FieldGenericETilde7:281
  └── T(1,2,5) (#2793, replan): API stub wave 61 (PR #2878)

per-(F, Q) subgraph dispatch wrappers (wave 61):
  ├── chordless_cycle_infinite_type_per_kQ ✅ PR #2882
  ├── triangle_infinite_type_per_kQ ✅ PR #2882
  └── star_subgraph_not_finite_type_per_kQ ✅ PR #2882

#2877 (Ch2 #2875 sub):
  ├── D1 ✅ PR #2878 (wave 61) — K_{1,4} + T(1,2,5) API stubs
  ├── D2 outer ✅ PR #2921 (wave 62):
  │      ├── D2.degree4 ✅ PR #2891 (wave 62)
  │      ├── D2.cycle ✅ PR #2897 (wave 62)
  │      ├── D2.adjacent ✅ PR #2900 (wave 62)
  │      ├── D2.singleBranch outer ✅ PR #2903 (wave 62)
  │      │      ├── leaf-leaf ✅ PR #2906 (wave 62)
  │      │      └── both-extend (Tpqr.lean:1286 sorry, #2905 chain):
  │      │            ├── sub-A (#2907 → PR #2911) — IN `/repair`
  │      │            ├── sub-B ✅ PR #2914 + #2917
  │      │            ├── sub-C ✅ PR #2916 + #2918
  │      │            └── sub-D ✅ PR #2912
  │      ├── D2.nonAdjacent (FieldGenericAssembly.lean:96 sorry,
  │      │     tracked by #2919 → #2922 + #2923)
  │      └── D2.acyclic ✅ PR #2921 (wave 62)
  └── D3 ✅ PR #2921 (wave 62) — `Theorem2_1_2.lean:173` closed
```

### Cluster D: Morita Theory (Ch9) — CLOSED (wave 50)

## Trajectory

| Wave | Sorries | Files | Items sorry-free | Date       |
|------|---------|-------|------------------|------------|
| 43   | 13      | 10    | 579/583 (99.3%)  | 2026-04-04 |
| 44   | 10      | 8     | 580/583 (99.5%)  | 2026-04-05 |
| 45   | 15      | 8     | 580/583 (99.5%)  | 2026-04-06 |
| 46   | 15      | 8     | 580/583 (99.5%)  | 2026-04-08 |
| 47   | 9       | 6     | 581/583 (99.7%)  | 2026-04-11 |
| 48   | 8       | 6     | 581/583 (99.7%)  | 2026-04-11 |
| 49   | 10      | 6     | 581/583 (99.7%)  | 2026-04-12 |
| 50   | 13      | 5     | 581/583 (99.7%)  | 2026-04-13 |
| 51   | 21      | 5     | 582/583 (99.8%)  | 2026-04-17 |
| 52   | 17      | 4     | 582/583 (99.8%)  | 2026-04-17 |
| 53   | 13      | 4     | 582/583 (99.8%)  | 2026-04-17 |
| 54   | 14      | 4     | 582/583 (99.8%)  | 2026-04-23 |
| 55   | 7       | 4     | 582/583 (99.8%)  | 2026-04-24 |
| 56   | 8       | 4     | 582/583 (99.8%)  | 2026-04-24 |
| 57   | 7       | 4     | 582/583 (99.8%)  | 2026-04-27 |
| 58   | 7       | 4     | 582/583 (99.8%)  | 2026-05-04 |
| 59   | 10      | 7     | 582/583 (99.8%)  | 2026-05-17 |
| 60   | 16      | 8     | 582/583 (99.8%)  | 2026-05-18 |
| 61   | 18      | 10    | 581/583 (99.6%)  | 2026-05-18 |
| **62** | **19** | **11** | **582/583 (99.8%)** | **2026-05-19** |

**Wave-62 trend:** Fifth consecutive non-monotone wave on raw
count (58 → 59: +3; 59 → 60: +6; 60 → 61: +2; 61 → 62: +1). The
wave-62 +1 net is a decomposition cost: the Ch2 forward bridge
closed but the bridge handed off two new stubs to Ch6 (one
non-adjacent-branches stub + one single-branch both-extend
dispatcher). The items-sorry-free fraction returned to 582/583,
matching the canonical `progress/items.json` count (wave 61's
581/583 was a hand-count error — the K_{1,4} / T(1,2,5)
per-(F, Q) API stubs were never persisted into `items.json` as
new items, so the denominator never grew).

Of the 19 current sorries:

- 3 are framework-wall stubs in `InfiniteTypeConstructions`
  (ℂ-specific, dead code w.r.t. the forward bridge).
- 2 are framework-wall stubs in the F-generic files
  (`FieldGenericETilde6.lean:299`, `FieldGenericETilde7.lean:281`)
  on the active per-(F, Q) chain.
- 6 are D̃₅ Sub B decomposition stubs in `FieldGenericD5Tilde.lean`
  (lines 926/928/930/932/934 in `d5tildeRep_kQ_leaf_equalities`,
  line 981 in `d5tildeRep_kQ_isIndecomposable`) — unchanged from
  wave 61.
- 2 are per-(F, Q) API stubs from wave 61's PR #2878:
  - `Chapter6/FieldGenericStar.lean:557` — K_{1,4} (#2789/#2801).
  - `Chapter6/FieldGenericT125.lean:53` — T(1,2,5) (#2793).
- 2 are NEW WAVE 62 stubs from PRs #2906 / #2921:
  - `Chapter6/FieldGenericTpqr.lean:1286` —
    `single_branch_leaf_case_both_extend_per_kQ` dispatcher
    (#2907 → PR #2911 in `/repair`).
  - `Chapter6/FieldGenericAssembly.lean:96` —
    `non_adjacent_branches_infinite_type_per_kQ` (#2919 → #2922
    + #2923).
- 2 are on the active Wall 3 chain (helper #2550 in repair static
  ~25 days; final assembly blocked through R2.b/R2.c).
- 1 is the Schur-Weyl C-4a aggregation (`SchurModuleSimple:148`),
  blocked through γ-cluster + #2493 onward.
- 1 is the top-of-chain Schur-Weyl goal
  (`FormalCharacterIso:399`), blocked through
  `#2483 → #2482 → #2493 → #2708 → γ-cluster`.

The headline change from wave 61: the **Theorem 2.1.2 forward
bridge sorry is no longer in this list.** The forward direction
is closed at the architectural level; what remains is local
per-(F, Q) leaf work.

## Honest Assessment

Wave 62 was a **body-proof-dominant, architecture-closing wave**.
The headline events are the per-(F, Q) outer assembly +
Theorem 2.1.2 forward-bridge closure (PR #2921) and the
`single_branch_leaf_case_per_kQ` cascade (PRs #2903, #2906,
#2912, #2914, #2916, #2917, #2918). The wave produced **6
substantive Ch6 leaf body closures**, **1 Ch2 bridge closure**,
**+1 net sorry** (decomposition cost), **0 broken-main events**,
and **2 PASS audits**. Net: the bridge architecture is done and
the residual work is local to per-(F, Q) leaf bodies.

**Strengths:**

1. **Theorem 2.1.2 forward bridge closed at the assembly level.**
   `not_posdef_not_HasFiniteRepresentationType` is now sorry-free
   in `Chapter2/Theorem2_1_2.lean:153-179`. A reader of the
   forward direction can navigate end-to-end without an
   architectural sorry. The remaining work is **entirely local**
   to per-(F, Q) leaf bodies (Wall 1 Ẽ₆/Ẽ₇, K_{1,4}, T(1,2,5),
   D̃₅ Sub B, the two new wave-62 dispatcher stubs).

2. **Pre-split decomposition pattern paid off.** Wave 62's
   planner cycles pre-split #2877 into per-helper sub-issues
   (D2.degree4 #2889, D2.cycle #2895, D2.adjacent #2898,
   D2.single #2901, D2.nonAdjacent #2919). Each landed as a
   focused 1-session worker target. **5 of 6 sub-helpers
   landed; the sixth (D2.nonAdjacent) is decomposed and ready.**

3. **Zero broken-main events.** Second consecutive wave (wave 61
   + wave 62) with no broken-main events. The audit cadence
   (PRs #2894, #2926) caught no regressions, and the cascading
   sub-issue workflow kept each PR's blast radius small.

4. **`single_branch_leaf_both_extend` cascade fully wired modulo
   sub-A.** Four-way dispatch closed in five PRs across the
   wave: outer (#2906), sub-B (#2914 + #2917), sub-C (#2916 +
   #2918), sub-D (#2912). The shared helper
   `embed_t125_in_tree_per_kQ` (PR #2917) closed −1 each in
   sub-B and sub-C. The remaining gap is sub-A (PR #2911 in
   `/repair`).

5. **Mathematical structure made local.** Pre-PR #2921, the
   Theorem 2.1.2 forward direction had an open sorry at the
   bridge level that obscured which per-(F, Q) leaves actually
   mattered. Post-PR #2921, the dependency set is explicit:
   six per-(F, Q) leaves plus two new dispatcher stubs. The
   structural ambiguity that motivated several waves of
   re-scoping has been resolved.

**Concerns:**

1. **Wall 1 is 8 waves stale (#2436).** No movement on the
   human-oversight side. Wave-62 architecture closure has
   further sharpened the cost: with the bridge proof sorry-free,
   the only architectural blocker on the forward direction's
   end-to-end closure (after #2919 lands) is Wall 1 plus the
   per-(F, Q) K_{1,4}/T(1,2,5)/D̃₅ Sub B chains. The Wall 1
   ask is structurally the smallest it has ever been — produce
   an Option-B body for two stub theorems whose statements are
   final.

2. **PR #2911 (wave-62-fresh) in `/repair`.** The Ẽ₇ embed PR
   for arms ≥ 3 hit merge conflicts. It is the highest-leverage
   repair target because its merge directly unblocks the
   `single_branch_leaf_case_both_extend_per_kQ` dispatcher
   wiring (Tpqr.lean:1286).

3. **PR #2550 has been in repair for ~25 days, PR #2694 for
   ~17 days.** Both are CI-clean but conflict-blocked. The
   `/repair` flow has dispatched on every pod cycle since their
   conflict status appeared. Neither has produced a result. The
   rebase surface continues to grow over wave-62 Ch6 motion
   (#2891, #2897, #2900, #2903, #2906, #2912, #2914, #2916,
   #2917, #2918, #2921).

4. **D̃₅ Sub B body-proof work has stalled.** The
   #2839 / #2850 / #2853 / #2851 chain saw no body-proof
   movement in wave 62. All four issues remain `replan` /
   `blocked`. The wave-61 hoists prepared the file layout for
   #2853, but no worker has claimed it across two waves now.

5. **#2693 (γ.B) is unclaimed and still `replan` after 7 waves.**
   Same concern as wave 61. The Schur-Weyl chain remains four
   PRs from closure modulo γ.A + γ.B; γ.B alone is the
   unblocked side of the cluster but no one has scoped a
   concrete workitem.

6. **Wave-62 audit ratio dropped to 2:11 (review:feature).**
   Wave 61 ran 4:6; wave 60 ran 4:8. The drop reflects the
   pre-split pattern naturally producing more feature work, but
   the audit cadence is now lagging — only PR #2891 and PR
   #2921 received explicit audits this wave. The other five
   wave-62 features (#2897, #2900, #2903, #2906, #2912) shipped
   without dedicated review issues. If body-proof work continues
   at this rate, planners should consider scheduling catch-up
   audits.

**Current priority ordering:**

1. **#2922 — `non_adjacent_branches_leaf_case_per_kQ` (D2.nonAdj
   sub-A1).** Next critical-path feature for the forward bridge.
   The issue body estimates ~700 lines and notes the proof
   design is genuinely new (cannot mechanically mirror the
   universal proof because no general `D̃_n` per-(F, Q) exists).
   Worker should design on paper first per the issue's guidance.
   Once #2922 lands, #2923 (sub-A2 outer assembly) auto-unblocks.

2. **Kim's framework decision on Wall 1 (#2436).** Now the
   single largest structural blocker on Theorem 2.1.2 closure.
   8 waves stale. With #2877 D2/D3 sorry-free, the bridge's
   only remaining architectural sorry is at the leaf level.
   Option B's landing site is two specific files
   (`FieldGenericETilde6.lean`, `FieldGenericETilde7.lean`).

3. **PR #2911 repair (D2.singleBranch sub-A).** Wave-62-fresh
   conflict. Its merge closes the `Tpqr.lean:1286` dispatcher
   stub.

4. **D̃₅ Sub B follow-through (#2853, then #2851).** Layout
   consolidated since wave 61. #2853 is 31 cases via the
   canonical template; #2851 follows. Both should be claimable
   worker items.

5. **PR repair for #2550, #2694, #2849.** Three long-conflict-
   blocked PRs.

6. **Wall 3 R2.b.i (#2769) with the R3-bis strategy.** Unchanged
   status from wave 61.

7. **Schur-Weyl γ.B (#2693).** Unclaimed, `replan` for 7+ waves.

**Closure forecast:** Wave 62's structural state is
"architecture-closed, leaf-pending." The closest closures are:

- **Theorem 2.1.2 forward direction (post-#2919 / #2922 / #2923):**
  Once the non-adjacent branches leaf-case helper lands plus
  the outer assembly, the forward direction transitively
  reduces to per-(F, Q) leaf bodies. Best-case 1-2 waves to
  fully close the architectural path.

- **D2.singleBranch both-extend dispatcher (Tpqr.lean:1286):**
  Once PR #2911 lands (sub-A Ẽ₇ embed), the dispatcher is
  small-glue wiring. ~1 session.

- **D̃₅ per-(F, Q) indecomposability (#2804):** Wave-61
  preparatory work means #2853's 31-case fill is mechanical;
  still 1-2 focused sessions to close, but no worker has
  claimed across two waves.

- **Schur-Weyl line 399 / Wall 3 line 1958:** same blockers as
  wave 61. No movement projected without a worker claiming γ.B
  / R2.b.i.

Best-case 1-wave projection (next summarize after wave 62):
19 → ≤13 (D2.nonAdj closes 1, D2.singleBranch both-extend
closes 1, the four D̃₅ Sub B sorries close on the
mechanical fill, optionally one Wall 3 / Schur-Weyl movement).
Worst-case (no framework decision, no #2922 claim, no D̃₅
body-proof work): 19 → ≥19, stable. Wave 62 has set up the
next wave to be highly productive if workers continue to
claim the now-explicit critical-path items.

## Design walls snapshot

- **Wall 1 status unchanged**, 8 waves stale. Per-(F, Q) refactor
  remains the structural workaround. 5 framework-wall sorries
  total (3 dead ℂ-specific + 2 live F-generic). The structural
  cost is now isolated to two stub theorems whose statements are
  final.
- **Wall 2** still closed.
- **Wall 3** chain unchanged from wave 61. R2.b.i (#2769) `replan`
  with concrete strategy doc; PR #2550 ~25 days static.
- **Schur-Weyl chain** unchanged from wave 61. γ.A (PR #2694
  DIRTY ~17d), γ.B (#2693 replan unclaimed), C-4a
  aggregation (#2708 blocked).
- **D̃₅ Sub B cascade** unchanged from wave 61. File layout
  consolidated; no body-proof movement.
- **Per-(F, Q) ↔ Theorem 2.1.2 bridge** **architecture closed
  this wave.** Outer assembly + bridge proof both sorry-free.
  Residual work transferred into local per-(F, Q) leaf chains
  (#2919, #2905, plus the four pre-existing leaf chains).

Refer to `progress/design-walls-wave62.md` for the updated decision
sheet.

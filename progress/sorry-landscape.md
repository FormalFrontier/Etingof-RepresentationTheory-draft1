# Sorry Landscape Analysis — Wave 61

Generated 2026-05-18 by summarize session (issue #2886).

## Summary

**18 sorries** across 10 files (vs 16/8 at wave 60). Net delta vs
wave 60: **+2 sorries, +2 files.** Both new sorries are per-(F, Q)
API stubs introduced by PR #2878 (Ch6 #2875 D1):
`star_not_finite_type_per_kQ`
(`Chapter6/FieldGenericStar.lean:556`, tracked by #2789/#2801) and
`t125_not_finite_type_per_kQ`
(`Chapter6/FieldGenericT125.lean:53`, tracked by #2793). Both are
intentional API stubs added to complete the six-leaf set required
by the per-(F, Q) ↔ Theorem 2.1.2 bridge — the assembly
`not_posdef_infinite_type_per_kQ` can now dispatch by name to all
six forbidden subgraphs, even though two of those names have
sorry bodies pending #2789/#2801/#2793.

**Wave 61 was a bridge-infrastructure wave with zero broken-main
events.** Counted from wave 60's close (2026-05-18T02:25Z) to this
snapshot (2026-05-18T11:08Z), the wave was ~9 hours of agent
activity. Of the 18 PRs merged in that window, **10 are
substantive** (feature / refactor / doc / review) and **8 are
planner-cycle / progress no-ops**. No `fix:` PRs and no
broken-main events — the first wave since wave 60 to clear this
bar. **Four of the ten substantive PRs are review audits**
(#2861, #2866, #2879, #2885), all returning PASS verdicts. The
audit cadence is paying off.

The wave-61 story has three parts:

- **Per-(F, Q) ↔ Theorem 2.1.2 bridge infrastructure layer
  landing.** The two missing per-(F, Q) API stubs for the
  forbidden-subgraph family (K_{1,4} and T(1,2,5)) shipped
  (PR #2878), giving Chapter 6 the complete six-leaf set required
  by the bridge. The three per-(F, Q) subgraph dispatch wrappers
  (chordless cycle / triangle / star_subgraph) shipped (PR #2882),
  giving the outer case-analysis assembly clean leaf functions to
  call. The bridge is now within **one outer-assembly issue
  (#2877)** of closing.

- **D̃₅ Sub B cascade preparatory hoists (no `sorry` motion).**
  PR #2862 hoisted `core_F` / `core3_F` / `gamma_containment_F`
  to top-level in `FieldGenericInfiniteType`. PR #2863 hoisted
  `embed_sum_zero_F` / `center_decomp_F` to `FieldGenericStar`.
  PR #2871 added projection-based reversed-leaf-edge sibling
  lemmas (`d5tildeRep_F_proj1/2`, `d5tildeRep_F_proj3/4`) for the
  #2853 31-case fill. These reorganize the file layout for the
  pending 31-case fill in #2853 (the 5 D̃₅ leaf-equality sorry
  positions shifted to lines 926/928/930/932/934/981, but the
  count is unchanged). All three hoists cleared light-audit
  review (#2866 / #2879). The D̃₅ Sub B chain itself
  (#2839 / #2850 / #2853 / #2851) saw no body-proof movement.

- **Mathlib upstream forwarding.** PR #2867 documented
  `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero` as
  forwarded to Mathlib PR 39523 — the on-our-side deliverable
  for tracker #2841 is now complete (the file simply waits for
  upstream merge before the local copy is removed). Tracker
  #2564 (`MvPolynomial.eq_of_eval_eq_on_gl`) remains external-
  blocked on Mathlib PR 38583.

288 Lean source files in `EtingofRepresentationTheory/`, of which
**278 are sorry-free (96.5%)**. **581/583 items (99.6%) sorry-free**
— a one-item drop from wave 60's 582/583. The two new API stubs
(`star_not_finite_type_per_kQ`, `t125_not_finite_type_per_kQ`)
were new theorems added by PR #2878, so the new items reduce the
sorry-free items denominator and numerator. The remaining
non-sorry-free items: Gabriel's theorem placeholder
(`Chapter2/Theorem2.1.2`, status `statement_formalized`,
unchanged) + the new stubs.

**Definition-level sorries: 0.** All mathematical objects are
still constructed.

### Key story for wave 61

- **Wall 1 (Ẽ/T framework, #2436):** **status unchanged.** Still 5
  sorries (3 ℂ-specific dead code in `InfiniteTypeConstructions`,
  2 F-generic live on the per-(F, Q) chain). Line positions
  identical to wave 60. **Seventh** consecutive wave with no
  Wall 1 movement. The wave-61 bridge-infrastructure work
  sharpens the Wall 1 cost: with the bridge assembly issue
  (#2877) now worker-ready, every per-(F, Q) leaf except the two
  Wall-1-blocked ones (Ẽ₆ / Ẽ₇) has either a real proof or a
  tracked-stub. The dependence has become explicit — the bridge
  closure forecast is gated solely on a Wall 1 decision and the
  six leaf stubs landing.

- **Wall 2 (D̃_n indecomposability):** **STILL CLOSED.** No
  regression.

- **Wall 3 (Ch5 `SpechtModuleBasis.lean`, 2 sorries):** unchanged
  this wave. R2.b.i (#2769) still in `replan` with the R3-bis
  cross-region involution strategy from PR #2779. R2.b.ii (#2770)
  / R2.c (#2703) still blocked. PR #2550 (line 1487 helper,
  C.1.a.ii) still `CONFLICTING` — **~24 days static**, in the
  pr-repair queue with no successful repair yet.

- **Schur-Weyl chain (Ch5):** **status unchanged.** Same 2 sorries
  (`SchurModuleSimple.lean:148` C-4a aggregation;
  `FormalCharacterIso.lean:399` top-of-chain). γ.A (PR #2694)
  still `CONFLICTING`, **~16 days static**. γ.B (#2693) still
  unclaimed `replan` for 6+ waves.

- **D̃₅ Sub B chain (wave-60 cascade):** **net 0 sorries, line
  positions shifted.** PR #2862 / PR #2863 / PR #2871 reorganized
  the file layout (hoists + projection sibling lemmas) ahead of
  the 31-case fill in #2853 but introduced no new sorries and
  closed none. The 5 D̃₅ leaf-equality sorries previously at
  lines 802/804/806/808/810 are now at lines 926/928/930/932/934
  (line shifts caused by the projection-sibling lemma block
  added by PR #2871). The `d5tildeRep_kQ_isIndecomposable` API
  stub previously at line 856 is now at line 981. Mathematical
  content unchanged.

- **Per-(F, Q) ↔ Theorem 2.1.2 bridge (Ch2 #2774 / #2875 / #2877):**
  **infrastructure layer landed.** All six per-(F, Q) leaf
  theorems exist (4 fully proven with sorry-propagating bodies,
  2 as fresh API stubs tracked by #2789/#2801/#2793). All three
  per-(F, Q) subgraph dispatch wrappers exist (PR #2882). The
  outer case-analysis assembly `not_posdef_infinite_type_per_kQ`
  is the only remaining gap on the bridge — tracked by #2877,
  worker-self-decomposes into 6 sub-deliverables per its body
  (the audit at #2885 confirmed D2.cycle ~150 lines and
  D2.degree4 ~50 lines are worker-ready as standalone sub-issues).

### Merges since wave 60 (18 PRs, 2026-05-18T02:25Z → 2026-05-18T11:08Z)

Of the 18 PRs merged in this window, **8 are planner / progress
no-ops** (#2865, #2870, #2872, #2874, #2876, #2881, #2884, #2887)
and **0 are pure repairs** — wave 61 had no broken-main events.
The remaining 10 substantive PRs are tabulated chronologically:

| PR    | Time (UTC)       | Title (truncated)                                                                | Sorry Impact |
|-------|------------------|----------------------------------------------------------------------------------|--------------|
| #2861 | 05-18 02:47      | review(Ch6 #2858): audit D̃₅ Sub B cascade helpers (PRs #2835 / #2843 / #2854)   | Audit (PASS) |
| #2862 | 05-18 03:02      | refactor(Ch6): hoist `core_F` / `core3_F` / `gamma_containment_F` to top-level   | Refactor / line shifts |
| #2863 | 05-18 03:20      | refactor(Ch6): hoist `embed_sum_zero_F` / `center_decomp_F` to `FieldGenericStar` | Refactor / line shifts |
| #2866 | 05-18 03:51      | review(Ch6): audit #2862 / #2863 hoist correctness                                | Audit (PASS) |
| #2867 | 05-18 06:24      | doc(Ch5 #2841): forward to Mathlib PR 39523 (`IsIdempotentElem.eq_zero_of_trace`) | Doc |
| #2871 | 05-18 07:03      | feat(Ch6 #2853 pre-step): projection-based reversed-leaf-edge sibling lemmas      | Infra (chain) / line shifts |
| #2878 | 05-18 09:53      | feat(Ch6 #2875 D1): per-(F, Q) API stubs for K_{1,4} and T(1,2,5)                | **+2** (`star_not_finite_type_per_kQ`, `t125_not_finite_type_per_kQ`) |
| #2879 | 05-18 10:10      | review(Ch6 #2868): audit proj-sibling lemmas in PR #2871                          | Audit (PASS) |
| #2882 | 05-18 10:38      | feat(Ch6 #2877 pre-step): per-(F, Q) subgraph dispatch wrappers                   | Infra (bridge) |
| #2885 | 05-18 11:01      | review(Ch6 #2877 pre-step): audit per-(F, Q) dispatch wrappers + K_{1,4}/T(1,2,5) | Audit (PASS) |

Planner / progress no-op PRs (8): #2865, #2870, #2872, #2874,
#2876, #2881, #2884, #2887.

**Net counts (wave 61):**
- Substantive feature / infra PRs: 3 (#2871, #2878, #2882).
- Documentation / hygiene: 1 (#2867).
- Refactor: 2 (#2862, #2863).
- Audit / review: 4 (#2861, #2866, #2879, #2885) — all PASS.
- Broken-main repair: 0.
- Planner-cycle no-op progress notes: 8 (#2865, #2870, #2872,
  #2874, #2876, #2881, #2884, #2887).
- Raw sorry count: 16 → 18. Files with sorries: 8 → 10.
- Net change: **+2 sorries, +2 files.** Closures: 0. Additions: 2 —
  both API stubs in PR #2878 (one in `FieldGenericStar.lean`, one
  in `FieldGenericT125.lean`), both tracked by pre-existing
  per-(F, Q) chain issues (#2789/#2801 and #2793).

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 60 |
|---------|---------|-------|--------------------|
| Ch2     | 1       | 1     | 0                  |
| Ch5     | 4       | 3     | 0                  |
| Ch6     | 13      | 6     | +2 sorries, +2 files |
| Ch9     | 0       | 0     | 0                  |

Wave-61 sorry growth is entirely in Ch6, distributed across two
new files (`FieldGenericStar.lean` +1, `FieldGenericT125.lean` +1).

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 3 sorries: WALL 1 ℂ-SPECIFIC (dead w.r.t. forward bridge)

Unchanged from wave 60. All three are refuted-as-stated pointers
to Wall 1; the wave-59 per-(F, Q) refactor moved the active
dependency path off these ℂ-specific stubs but they remain in
source.

| Line | Theorem | Status |
|-----:|---------|--------|
| 3344 | `etilde6v2Rep_isIndecomposable (m hm)` | Refuted; bypassed by F-generic chain |
| 3599 | `etilde7Rep_isIndecomposable (m hm)`  | Refuted; bypassed by F-generic chain |
| 3826 | `t125Rep_isIndecomposable (m hm)`     | Refuted; bypassed by F-generic chain |

Reference: `progress/indecomposability-framework-investigation.md`.
Framework issue: #2436 (`human-oversight`, `replan`, **7 waves stale**).

### FieldGenericD5Tilde (Ch6) — 6 sorries: D̃₅ SUB B CASCADE (UNCHANGED, LINE POSITIONS SHIFTED)

Unchanged in count and tracking. All six introduced wave 60 by
PRs #2835 + #2854. Line positions shifted by PRs #2862 / #2863
(helper hoists) + #2871 (projection sibling lemmas).

| Line (wave 61) | Line (wave 60) | Theorem / branch | Tracking issue | Notes |
|---------------:|---------------:|------------------|----------------|-------|
| 926 | 802 | `d5tildeRep_kQ_leaf_equalities`, e53-reversed branch (3→5, 1 sub-case)  | #2853 | Reversed leaf edge — needs `starSecond_F` projection variant |
| 928 | 804 | `d5tildeRep_kQ_leaf_equalities`, e43-reversed branch (3→4, 2 sub-cases) | #2853 | Reversed leaf edge — needs `starFirst_F` projection variant |
| 930 | 806 | `d5tildeRep_kQ_leaf_equalities`, e23-reversed branch (3→2, 4 sub-cases) | #2853 | Reversed central edge — needs γ⁻¹ identities (`gammaInv_embed*_F`) |
| 932 | 808 | `d5tildeRep_kQ_leaf_equalities`, e12-reversed branch (2→1, 8 sub-cases) | #2853 | Reversed leaf edge — needs `starSecond_F` projection variant |
| 934 | 810 | `d5tildeRep_kQ_leaf_equalities`, e02-reversed branch (2→0, 16 sub-cases) | #2853 | Reversed leaf edge — needs `starFirst_F` projection variant |
| 981 | 856 | `d5tildeRep_kQ_isIndecomposable`     | #2851 (via #2839 sub-B) | API stub. Body deferred to #2851 (assembly via N-invariance + propagation) |

The five reversed-leaf-edge case-splits cover 31 of 32 orientation
branches; the canonical branch (proven inline) closes the
remaining one. The supporting infrastructure for #2853 is now
fully in place: top-level helpers (post #2862/#2863 hoists) +
projection-based sibling lemmas (post #2871) + γ⁻¹ closed forms
(PR #2843, wave 60).

### FieldGenericETilde6 (Ch6) — 1 sorry: WALL 1 F-GENERIC (line position unchanged)

- **Line 299** — `etilde6Rep_kQ_isIndecomposable (F Q hOrient m hm)`.
  Line position **unchanged** from wave 60. Mathematical content
  unchanged: the single-nilpotent-twist construction peels off a
  1-dim summand at the center, inheriting the wave-54 framework
  wall. **On the active dependency path** for
  `etilde6_not_finite_type_per_kQ` → Theorem 2.1.2 forward bridge.

### FieldGenericETilde7 (Ch6) — 1 sorry: WALL 1 F-GENERIC (line position unchanged)

- **Line 281** — `etilde7Rep_kQ_isIndecomposable (F Q hOrient m hm)`.
  Line position **unchanged** from wave 60. Mathematical content
  unchanged. Same framework-wall inheritance as Ẽ₆. **Also on the
  active dependency path** for the per-(F, Q) assembly.

### FieldGenericStar (Ch6) — 1 sorry: K_{1,4} per-(F, Q) API STUB (NEW THIS WAVE)

- **Line 556 — `star_not_finite_type_per_kQ` body.**
  Introduced wave 61 by PR #2878. API stub for the K_{1,4}
  (D̃₄) forbidden-subgraph case of the per-(F, Q) bridge. The
  theorem statement is final; only the body is `sorry`. Tracked
  by the existing per-(F, Q) K_{1,4} chain issues #2789
  (canonical orientation) + #2801 (Q-extension indecomposability).
  Both still `replan`. **On the active dependency path** —
  consumed by `star_subgraph_not_finite_type_per_kQ` (PR #2882)
  and from there by `not_posdef_infinite_type_per_kQ` (#2877).

### FieldGenericT125 (Ch6) — 1 sorry: T(1,2,5) per-(F, Q) API STUB (NEW THIS WAVE)

- **Line 53 — `t125_not_finite_type_per_kQ` body.**
  Introduced wave 61 by PR #2878. API stub for the T(1,2,5)
  forbidden-subgraph case of the per-(F, Q) bridge. The theorem
  statement is final; only the body is `sorry`. Tracked by
  #2793 (T(1,2,5) per-(F, Q), `replan`). **On the active
  dependency path** — consumed directly by
  `not_posdef_infinite_type_per_kQ` (#2877).

### SpechtModuleBasis (Ch5) — 2 sorries: WALL 3 CHAIN ACTIVE (unchanged)

- **Line 1487 — `twistedPolytabloid_pigeonhole_pair`** (C.1.a.ii).
  Unchanged in status. Issue #2543 still `has-pr` (PR #2550 open,
  `CONFLICTING`, static since 2026-04-24T09:36Z — **~24 days**).
  In the `coordination list-pr-repair` queue but no repair has
  succeeded; rebase surface has grown further over wave-60/61
  Ch6 refactors.

- **Line 1958 — `garnir_twisted_in_lower_span`** (final Wall 3
  sorry). Unchanged. Semantically blocked on R2.b → R2.c. R2.b.i
  (#2769) `replan` with the R3-bis cross-region involution strategy
  (`progress/r3-bis-residual-cancellation.md`).

### SchurModuleSimple (Ch5) — 1 sorry: SCHUR-WEYL C-4a AGGREGATION (unchanged)

- **Line 148 — `schurModuleSubmodule_isSimple_centralizer`**.
  Unchanged from wave 60. Tracking issue #2708 blocked on
  γ.A (PR #2694, `CONFLICTING`) + γ.B (#2693, unclaimed `replan`).

### FormalCharacterIso (Ch5) — 1 sorry: SCHUR-WEYL TOP-OF-CHAIN (unchanged)

- **Line 399 — `iso_of_formalCharacter_eq_schurPoly`**. Unchanged
  in position. Same dependency cascade as wave 60: closes via
  `#6 (#2483) → #5 (#2482) → Part C (#2493) → C-4 aggregation
  (#2708) → γ-cluster (γ.A PR #2694 + γ.B #2693)`.

### Theorem2_1_2 (Ch2) — 1 sorry: FORWARD BRIDGE (unchanged)

- **Line 173 — `not_posdef_not_HasFiniteRepresentationType`**
  (forward). Unchanged from wave 60. Wave-61 bridge-infrastructure
  PRs (#2878, #2882) shrank the gap to closure: the bridge can
  now be filled by writing the `not_posdef_infinite_type_per_kQ`
  assembly (#2877) and then closing the line-173 sorry by
  combining it with `HasFiniteRepresentationType.finite_dimVectors`
  (`Theorem2_1_2.lean:111`). End-to-end closure still
  transitively depends on the F-generic Ẽ₆/Ẽ₇ Wall 1 stubs +
  per-(F, Q) K_{1,4}/T(1,2,5) chain issues (#2789, #2801, #2793).

## Per-(F, Q) ↔ Theorem 2.1.2 bridge scoreboard

State of the bridge layer at wave 61 close:

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
| **Outer assembly.** `not_posdef_infinite_type_per_kQ` | Unfiled | #2877 (worker-ready per #2885) |
| **Bridge close.** `not_posdef_not_HasFiniteRepresentationType` line 173 | Open | #2877 D3 |

**Closure-gating set as of wave-61 close.** The bridge cannot
close end-to-end without all of:
1. #2877 D2 (outer assembly `not_posdef_infinite_type_per_kQ` —
   worker-ready; ~1600 lines of new code if all sub-cases
   handled inline, or ~50-150 lines each if decomposed into
   sub-issues per #2877's body).
2. #2877 D3 (line 173 forward bridge — ~50 lines once D2 lands).
3. #2436 framework decision (Wall 1) — unblocks Ẽ₆/Ẽ₇ stubs.
4. #2789 / #2801 (K_{1,4} canonical + Q-extension
   indecomposability) — unblocks Leaf 3.
5. #2793 (T(1,2,5)) — unblocks Leaf 7.
6. #2853 (D̃₅ Sub-A2 31 non-canonical cases) + #2851 (D̃₅ Sub-B
   assembly) — unblocks Leaf 4.

The structural ordering is unchanged from wave 60 — what wave 61
adds is that all of (2), the wrappers, and the API stubs are now
in place, so a worker claiming #2877 has every required leaf
and dispatch wrapper available by name.

## Open PRs

| PR | Status | Branch / Note |
|----|--------|---------------|
| #2849 | mergeable=UNKNOWN, CI FAILURE | Ch6 chore — dedupe `etilde6LeafProj_F` and `starFirst_F` post-#2802. CI failing; in pr-repair queue. |
| #2694 | CI SUCCESS, mergeable=UNKNOWN | Schur-Weyl L_i γ.A scaled-projection; ~16 days static |
| #2550 | CI SUCCESS, mergeable=UNKNOWN | Wall 3 C.1.a.ii pigeonhole; ~24 days static, in repair queue |

PR #2694 and PR #2550 remain long carry-overs (4 and 6 waves
respectively). The pr-repair flow continues to dispatch on every
pod cycle but has not produced a result on either. PR #2849 is
the wave-60 chore PR that introduced CI failures; **still failing
CI as of wave-61 close** despite being in the repair queue for
~9 hours.

## Active / Claimed Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2886 | summarize: wave-61 sorry landscape + design-walls refresh | claimed (this session) |

## Unclaimed Issues (`agent-plan`, FIFO order)

| Issue | Title | Notes |
|-------|-------|-------|
| #2564 | Mathlib upstream tracker — `MvPolynomial.eq_of_eval_eq_on_gl` | Awaiting external Mathlib PR #38583 merge |
| #2877 | feat(Ch2 #2875 sub): `not_posdef_infinite_type_per_kQ` assembly + Theorem 2.1.2 bridge | **WORKER-READY** per #2885 audit; D2+D3 deliverables explicit |

## Replan / Human-oversight / Blocked Issues

Same shape as wave 60. Updates:

| Issue | Title | Status |
|-------|-------|--------|
| #2436 | Framework decision: affine Dynkin infinite type (Ẽ_n / T(p,q,r)) | replan, `human-oversight`, awaits Kim (**7 waves**) |
| #2875 | Ch2 per-(k, Q) assembly + bridge (parent) | replan since wave 61 D1 close (PR #2878); D2/D3 spun out as #2877 |
| #2841 | Mathlib upstream tracker — `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero` | replan; on-our-side deliverable complete (PR #2867 forwarded to Mathlib PR 39523) |
| #2774 | Ch2 per-(k, Q) subgraph transfer + assembly | replan since wave 59 (deliverables 2 + 3 now tracked by #2877) |
| #2769 | Wall 3 R2.b.i cancellation involution | replan after R3-bis meditate PR #2779 |
| #2702 | Wall 3 R2.b assembly | replan |
| #2789 | K_{1,4} canonical orientation per-(F, Q) | replan; consumed by PR #2878 stub |
| #2790 | D̃₅ per-(F, Q) | replan — sub-decomposed (#2803 ✅ + #2804) |
| #2793 | T(1,2,5) per-(F, Q) | replan; consumed by PR #2878 stub |
| #2797 | K_{1,4} Q-extension per-(F, Q) | replan — sub-decomposed (#2800 ✅ + #2801) |
| #2693 | Schur-Weyl γ.B rank-1 dim count | replan, unclaimed (**6 waves**) |
| #2612 | Schur-Weyl C-4c final assembly | replan — body landed wave 59 (PR #2706); residual in #2708 |
| #2804 | D̃₅ indecomposability + per-(F, Q) | replan after PR #2835 (deliverable 1 of 2) |
| #2834 | D̃₅ Sub B proof body | replan after PR #2843 (γ⁻¹ helpers landed) |
| #2839 | D̃₅ main proof body — direction-aware case-analysis | replan after wave-60 decomposition into #2850 + #2851 |
| #2850 | D̃₅ Sub-A leaf equalities | replan after PR #2854 (canonical case landed); residual #2853 |
| #2823 | bridge `starRep_kQ ↔ starRepGen` | replan after worker session 5b8dd06f filed #2846 instead |

| Issue | Title | Blocked on |
|-------|-------|-----------|
| #2543 | Wall 3 C.1.a.ii pigeonhole | has-pr (#2550 in repair, ~24d) |
| #2821 | Ch6 dedupe `etilde6LeafProj_F` / `starFirst_F` post-#2802 | has-pr (#2849, CI FAILURE wave-60-fresh; still failing wave-61) |
| #2770 | Wall 3 R2.b.ii assembly | #2769 |
| #2703 | Wall 3 R2.c final assembly | #2702 |
| #2708 | Schur-Weyl C-4a aggregation | γ.A (#2694) + γ.B (#2693) |
| #2493 | Schur-Weyl Part C final assembly | #2708 |
| #2482 | polynomial GL_N-rep ⊕ Schur modules (#5) | #2493 |
| #2483 | close `iso_of_formalCharacter_eq_schurPoly` (#6) | #2482 |
| #2801 | K_{1,4} Q-ext indecomposability | #2800 (✅ wave 60) — could now move to replan |
| #2851 | D̃₅ Sub-B assembly via N-invariance + propagation | #2850 (sub-A) |
| #2853 | D̃₅ Sub-A2 31 non-canonical orientation cases | #2850 (sub-A) |

## Dependency Clusters

### Cluster A: Wall 3 — Garnir straightening (Ch5, 2 sorries)

**Files:** `Chapter5/SpechtModuleBasis.lean` (2 sorries).

```
PR #2550 (C.1.a.ii pigeonhole, CONFLICTING ~24d) ─→ kills line 1487
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
C-4a-i needs sub-γ (γ.A PR #2694 CONFLICTING ~16d + γ.B #2693 replan)
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

### Cluster C: Per-(F, Q) ↔ Theorem 2.1.2 forward bridge (Ch6, 13 sorries + Ch2, 1 sorry)

**Files:** `Chapter6/InfiniteTypeConstructions.lean` (3 dead ℂ-specific
stubs), `Chapter6/FieldGenericETilde6.lean` (1 F-generic Wall 1 stub),
`Chapter6/FieldGenericETilde7.lean` (1 F-generic Wall 1 stub),
`Chapter6/FieldGenericD5Tilde.lean` (6 D̃₅ Sub B stubs, line positions
shifted this wave), `Chapter6/FieldGenericStar.lean` (1 K_{1,4} API
stub NEW THIS WAVE), `Chapter6/FieldGenericT125.lean` (1 T(1,2,5)
API stub NEW THIS WAVE), `Chapter2/Theorem2_1_2.lean` (1 forward-
bridge sorry).

```
#2773 (per-(F, Q) sub-theorems for 6 forbidden subgraphs)
  ├── cycle ✅ PR #2799 (wave 59)
  ├── K_{1,4} D̃₄ F-generic ✅ PR #2798 (wave 59)
  ├── K_{1,4} canonical (#2789, replan): API stub NEW WAVE 61 (PR #2878)
  ├── K_{1,4} Q-extension (#2797, replan):
  │     ├── #2800 construction ✅ PR #2802 (wave 60)
  │     └── #2801 indecomposability replan — consumed by PR #2878 stub
  ├── D̃₅ (#2790, replan):
  │     ├── #2803 construction ✅ PR #2813 (wave 60)
  │     └── #2804 indecomposability — Sub B cascade (wave 60 + 61):
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
  └── T(1,2,5) (#2793, replan): API stub NEW WAVE 61 (PR #2878)

per-(F, Q) subgraph dispatch wrappers (wave 61):
  ├── chordless_cycle_infinite_type_per_kQ ✅ PR #2882
  ├── triangle_infinite_type_per_kQ ✅ PR #2882 (k=3 specialisation)
  └── star_subgraph_not_finite_type_per_kQ ✅ PR #2882 (inherits #2789/#2801 sorry)

#2877 (Ch2 #2875 sub):
  ├── D1 ✅ PR #2878 (wave 61) — K_{1,4} + T(1,2,5) API stubs
  ├── D2: `not_posdef_infinite_type_per_kQ` outer assembly (worker-ready, see #2885 audit)
  └── D3: close `Theorem2_1_2.lean:173` (~50 lines once D2 lands)
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
| **61** | **18** | **10** | **581/583 (99.6%)** | **2026-05-18** |

**Wave-61 trend:** Fourth consecutive non-monotone wave on raw
count (58 → 59: +3; 59 → 60: +6; 60 → 61: +2). The wave-61
additions are not body-proof regressions but explicit API stubs
landed by PR #2878 to complete the bridge's leaf set. The items-
sorry-free fraction dropped from 582/583 to 581/583 because two
new theorems (`star_not_finite_type_per_kQ`,
`t125_not_finite_type_per_kQ`) were added to the item count by
PR #2878, each landing as a non-sorry-free item.

Of the 18 current sorries:

- 3 are framework-wall stubs in `InfiniteTypeConstructions`
  (ℂ-specific, dead code w.r.t. the forward bridge).
- 2 are framework-wall stubs in the F-generic files
  (`FieldGenericETilde6.lean:299`, `FieldGenericETilde7.lean:281`)
  on the active per-(F, Q) chain.
- 6 are D̃₅ Sub B decomposition stubs in `FieldGenericD5Tilde.lean`
  (lines 926/928/930/932/934 in `d5tildeRep_kQ_leaf_equalities`,
  line 981 in `d5tildeRep_kQ_isIndecomposable`), all on the active
  per-(F, Q) chain. **Line positions shifted from wave 60** but
  count unchanged.
- 2 are NEW WAVE 61 per-(F, Q) API stubs from PR #2878:
  - `Chapter6/FieldGenericStar.lean:556` — K_{1,4} (#2789/#2801).
  - `Chapter6/FieldGenericT125.lean:53` — T(1,2,5) (#2793).
- 1 is the Theorem 2.1.2 forward bridge (line 173), structurally
  still gated on the F-generic Wall 1 stubs.
- 2 are on the active Wall 3 chain (helper #2550 in repair static
  ~24 days; final assembly blocked through R2.b/R2.c).
- 1 is the Schur-Weyl C-4a aggregation (`SchurModuleSimple:148`),
  blocked through γ-cluster + #2493 onward.
- 1 is the top-of-chain Schur-Weyl goal
  (`FormalCharacterIso:399`), blocked through
  `#2483 → #2482 → #2493 → #2708 → γ-cluster`.

## Honest Assessment

Wave 61 was a **bridge-infrastructure-heavy, body-proof-light
wave**. The headline events are the per-(F, Q) ↔ Theorem 2.1.2
bridge infrastructure landing (PR #2878 API stubs, PR #2882
dispatch wrappers) and the supporting D̃₅ Sub B file-layout
hoists (PR #2862 / #2863 / #2871). The wave produced **0
body-proof closures**, **+2 stub sorries**, **0 broken-main
events**, and **4 PASS audits**. Net: the bridge is shovel-ready
for #2877 (the outer assembly), but no `sorry` was actually
removed.

**Strengths:**

1. **Bridge infrastructure complete.** All six per-(F, Q) leaf
   theorems exist and have callable names. All three dispatch
   wrappers exist (`chordless_cycle_infinite_type_per_kQ`,
   `triangle_infinite_type_per_kQ`,
   `star_subgraph_not_finite_type_per_kQ`). A worker claiming
   #2877 can dispatch by name to any of the seven forbidden
   subgraphs and any of the three subgraph types. The
   wave-60 #2885 audit explicitly confirmed two of #2877's
   sub-deliverables — D2.cycle (~150 lines) and D2.degree4 (~50
   lines) — are worker-ready as standalone sub-issues.

2. **Zero broken-main events.** First wave since wave 60 with no
   broken-main events. The wave-61 refactors (#2862, #2863) were
   smaller, more focused hoists than the wave-60 file split
   (#2844) and did not collide with any in-flight branch.

3. **Audit cadence paying off.** Four of the ten substantive PRs
   are review audits (#2861, #2866, #2879, #2885) — a 4:6
   review:feature ratio. All four returned PASS verdicts with no
   follow-up issues. The audit cadence appears to be catching
   potential issues at the pre-step layer (the D̃₅ hoists in
   #2862 / #2863 ahead of #2853, the proj-sibling lemmas in
   #2871 ahead of #2853, the dispatch wrappers + API stubs in
   #2878 / #2882 ahead of #2877).

4. **Mathlib upstream forwarding pattern documented.** PR #2867
   forwarded `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero`
   to Mathlib PR 39523, mirroring the #2564 →
   Mathlib PR 38583 pattern. This is now a repeatable workflow:
   write the lemma in-project, open the Mathlib PR, document the
   forward, and the local copy gets removed on Mathlib merge.

5. **D̃₅ Sub B file layout consolidated.** The wave-60 cascade
   left helper lemmas at section-internal positions; PR #2862 +
   #2863 + #2871 hoisted them to top-level / projection-sibling
   form, making #2853's 31-case fill mechanical (it can use the
   helpers by short name from any file in the chain).

**Concerns:**

1. **Wall 1 is 7 waves stale (#2436).** No movement on the
   human-oversight side. Wave-60 noted this as "6 waves" and the
   longest-running open item. Wave 61 adds another wave. The
   two F-generic sorries (`FieldGenericETilde6:299`,
   `FieldGenericETilde7:281`) sit on the active forward-bridge
   path and cannot close without a framework decision. The
   wave-61 bridge-infrastructure work has sharpened the cost —
   with the wrappers and stubs in place, every other piece of
   the bridge is independently solvable, but Wall 1 still
   bottlenecks two leaves.

2. **PR #2550 has been in repair for ~24 days, PR #2694 for
   ~16 days.** Both are CI-clean but conflict-blocked. The
   pr-repair flow has dispatched on every pod cycle since their
   conflict status appeared. Neither has produced a result. The
   rebase surface continues to grow over wave-60 + wave-61 Ch6
   refactors for #2550 (already wave-60: #2802, #2813, #2835,
   #2843, #2844; wave-61: #2862, #2863, #2871, #2878, #2882).
   For PR #2694 the wave-61 motion is similar but smaller.

3. **PR #2849 (Ch6 chore, wave-60-fresh) is still failing CI.**
   The chore PR deduping `etilde6LeafProj_F` and `starFirst_F`
   post-#2802 has been failing CI in the pr-repair queue for
   ~9 hours (~wave 60 to wave 61 boundary). The repair flow
   has not produced a fix. The wave-61 file hoists may have
   shifted further rebase surface here too.

4. **0 body-proof closures this wave.** Despite 10 substantive
   PRs and 4 PASS audits, no `sorry` was removed from `main`.
   The wave was entirely infrastructure: file hoists, dispatch
   wrappers, API stubs, audit verdicts. This is OK in a
   bridge-infrastructure wave — what matters is whether the
   following wave starts closing bodies — but it is a signal
   to call out.

5. **#2693 (γ.B) is unclaimed and still `replan` after 6 waves.**
   Same concern as wave 60. The Schur-Weyl chain remains four
   PRs from closure modulo γ.A + γ.B; γ.B alone is the
   unblocked side of the cluster but no one has scoped a
   concrete workitem.

6. **D̃₅ Sub B body-proof work has stalled.** The #2839 / #2850 /
   #2853 / #2851 chain saw no body-proof movement in wave 61.
   All four issues remain `replan` / `blocked`. The wave-61
   hoists prepared the file layout for #2853, but no worker
   claimed it. With #2877 now competing for worker attention,
   the D̃₅ Sub B chain risks slipping further behind.

**Current priority ordering:**

1. **#2877 — the outer assembly for the per-(F, Q) bridge.**
   Worker-ready per #2885 audit. D2 has 6 explicit sub-
   deliverables (D2.cycle ~150 lines, D2.degree4 ~50 lines, plus
   D2.adjacent ~150, D2.singleBranch ~305, D2.nonAdjacent ~927,
   D2.acyclic ~51, then outer D2 assembly ~50 + D3 bridge ~50).
   The #2877 body **strongly recommends** decomposition before
   claiming — first planner cycle to look at the queue should
   split it into the per-helper sub-issues. With the wrappers
   and leaf API stubs in place, each sub-issue can be sized
   reasonably.

2. **Kim's framework decision on Wall 1 (#2436).** Now
   bottlenecks 2 Ch6 F-generic sorries (live) + 3 ℂ-specific
   (dead) + 1 Ch2 downstream. Seventh consecutive wave with no
   movement. The wave-61 bridge-infrastructure work has reduced
   the structural ambiguity around the Wall 1 ask: an Option B
   strengthening, validated for D̃₅ in wave 60, can slot
   directly into the now-stub Ẽ₆ and Ẽ₇ files (which are next
   to each other in the file layout and share the helper
   scaffolding).

3. **D̃₅ Sub B follow-through (#2853, then #2851).** The file
   layout is now fully consolidated (post wave-61 hoists +
   proj-sibling lemmas). #2853 is 31 cases via the canonical-case
   template; #2851 is the assembly via N-invariance. Both
   should be unblocked workitems for a worker session that
   picks up #2850's "blocked-on" status and claims #2853 directly.

4. **PR repair for #2550, #2694, #2849.** Three conflict-
   blocked PRs (one ~24 days, one ~16 days, one wave-60-fresh
   CI FAIL). PR #2550 closes #2543 → line 1487 sorry. PR #2694
   unblocks γ.A → C-4a aggregation → C-4c → Part C → ... →
   line 399. PR #2849 unblocks #2821 (Ch6 chore).

5. **Wall 3 R2.b.i (#2769) with the R3-bis strategy.**
   Unchanged status from wave 60. PR #2779 produced the
   refined cross-region involution sketch validated on the
   running (2,2) example. Still a worker-ready item.

6. **Per-(F, Q) Ẽ live work residuals.**
   #2801 K_{1,4} Q-ext indecomposability (could move to replan
   now that #2800 / PR #2802 landed); T(1,2,5) #2793 needs
   triage / decomposition; K_{1,4} canonical #2789 same.

7. **Schur-Weyl γ.B (#2693).** Unclaimed, `replan` for 6+ waves.
   Single highest-impact Ch5 unblock if a worker re-scopes and
   claims it.

**Closure forecast:** Wave 61's structural state is "bridge-
ready, framework-blocked, body-stalled." The closest closures
are:

- **#2877 D2.degree4 + D2.cycle:** With clear sizing (~50 + ~150
  lines) and worker-ready dispatch wrappers, both sub-issues
  are 1-session closures each. After both land, the outer
  assembly D2 reduces to ~50 lines + connecting glue.

- **D̃₅ per-(F, Q) indecomposability (#2804):** Wave-61
  preparatory work means #2853's 31-case fill is mechanical;
  one or two focused sessions should close it. #2851 follows
  on #2850. Optimistically 1-2 waves to close #2804.

- **Theorem 2.1.2 forward bridge (line 173):** Still gated on
  Wall 1 + the per-(F, Q) K_{1,4}/T(1,2,5) chain. Best
  plausible 1-wave delta if Kim decides #2436 + #2877 D2 +
  #2877 D3 land + #2789/#2793 chains decompose+land.

- **Schur-Weyl line 399 / Wall 3 line 1958:** same blockers as
  wave 60. No movement projected without a worker claiming γ.B
  / R2.b.i.

Best-case 1-wave projection (next summarize after wave 61):
18 → ≤11 (D̃₅ Sub B closes 6 sorries, #2877 D2 closes the line-
173 sorry, the two new K_{1,4}/T(1,2,5) stubs may close inline
if PR #2878's TODO comments are picked up). Worst-case (no
framework decision, no #2877 claim, no D̃₅ body-proof work):
18 → ≥20 if further pre-step API stubs land for #2877's outer
assembly without body fills.

## Design walls snapshot

- **Wall 1 status unchanged**, 7 waves stale. Per-(F, Q) refactor
  remains the structural workaround. 5 framework-wall sorries
  total (3 dead ℂ-specific + 2 live F-generic).
- **Wall 2** still closed.
- **Wall 3** chain unchanged from wave 60. R2.b.i (#2769) `replan`
  with concrete strategy doc; PR #2550 ~24 days static.
- **Schur-Weyl chain** unchanged from wave 60. γ.A (PR #2694
  CONFLICTING ~16d), γ.B (#2693 replan unclaimed), C-4a
  aggregation (#2708 blocked).
- **D̃₅ Sub B cascade (wave 60 design topic).** Wave-61 brought
  file-layout consolidation (top-level helper hoists +
  projection-sibling lemmas) but no body-proof movement.
- **Per-(F, Q) ↔ Theorem 2.1.2 bridge (new wave-61 active
  topic).** Infrastructure layer complete; outer assembly
  #2877 is worker-ready.

Refer to `progress/design-walls-wave61.md` for the updated decision
sheet.

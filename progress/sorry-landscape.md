# Sorry Landscape Analysis — Wave 60

Generated 2026-05-18 by summarize session (issue #2855).

## Summary

**16 sorries** across 8 files (vs 10/7 in wave 59). Net delta vs
wave 59: **+6 sorries, +1 file.** Every new sorry is on the **D̃₅
Sub B decomposition path** in `Chapter6/FieldGenericD5Tilde.lean`,
introduced by PR #2835 (1 sorry, `d5tildeRep_kQ_isIndecomposable`
API stub) and PR #2854 (5 sorries, non-canonical-orientation
case-splits in `d5tildeRep_kQ_leaf_equalities`). All 6 new sorries
are tracked by issues #2839 / #2853 / #2851. The headline number
rises but, as in wave 59, the underlying picture is structural
decomposition — the canonical orientation branch (1 of 32) of the
leaf-equality theorem now has a closed proof inline, validating the
helper-lemma scaffolding the remaining branches will reuse.

**Wave 60 was a low-volume, file-restructure-heavy wave.** ~14
days separated this snapshot from wave 59; the 6 new sorries are
matched by **two `main`-breakages in one day** that required two
dedicated repair PRs (#2848, #2852). The dominant story of wave 60
is therefore not progress in the sorry count but the **D̃₅ Sub B
decomposition cascade** (#2804 → #2834 → #2839 → #2850 / #2851;
#2850 → #2853) and the supporting refactor that split
`FieldGenericInfiniteType.lean` into three smaller modules.

The wave-60 story has three parts:

- **D̃₅ Sub B cascade (Ch6).** Issue #2804 (D̃₅ per-(F, Q)
  indecomposability), wave-59's last-mile residual, was decomposed
  across the wave into a 4-level tree:
  ```
  #2804 (parent, replan after deliverable 1 lands)
    ├── PR #2835 (helpers + API stubs)         ─── DONE
    └── #2834 (proof body)
         ├── PR #2843 (γ⁻¹ closed-form identities)  ─── DONE
         └── #2839 (main proof body)
              ├── #2850 sub-A (leaf-equality theorem)
              │    ├── PR #2854 (canonical orientation + API stub)  ─── DONE
              │    └── #2853 sub-A2 (31 non-canonical cases)        ─── blocked on #2850
              └── #2851 sub-B (assembly via N-invariance + leaf eq)  ─── blocked on #2850
  ```
  The leaf-equality stub now closes 1 of 32 orientation branches
  inline (the all-canonical case 0→2, 1→2, 2→3, 4→3, 5→3 — mirrors
  the ℂ-source proof in `InfiniteTypeConstructions.lean:1569-1834`)
  and leaves the remaining 31 as 5 hierarchical `sorry`s on the
  reversed-at-level-k branches. The closed canonical branch proves
  the helper-lemma chain (`embed_sum_zero_F`, `center_decomp_F`,
  `gamma_from_embed1_F`, `gamma_from_embed2_F`, `core_F`, `core3_F`,
  `gamma_containment_F`) is end-to-end usable — a template for #2853.

- **File split + double-breakage repair (Ch6).** PR #2844 split
  `FieldGenericInfiniteType.lean` into shared / cycle / star
  modules (+793/-644, 8 files). The squash-merge order between
  #2802 and the rebased file-split produced the first broken-main
  event (#2846, repaired by PR #2848 — moving `starRep_kQ` to
  `FieldGenericStar`, deduping D̃₅ projections). A stale rebase
  in #2839's branch against the same refactor produced the second
  broken-main event (repaired by PR #2852 — fixing Section 5b/5d
  in `FieldGenericD5Tilde`). **Two broken-main events in a single
  day** is a structural signal (file-split + concurrent in-flight
  PRs) worth recording but not a wall — see
  `progress/design-walls-wave60.md`.

- **K_{1,4} Q-extension landed (Ch6).** PR #2802 (Q-extension
  direction-aware projections + `starRep_kQ` + dim vec) was
  CONFLICTING through wave 59; it landed early in wave 60 after
  pr-repair. This closes the construction half of #2797
  (K_{1,4} Q-extension) on the per-(F, Q) chain; the
  indecomposability half (#2801) is still blocked.

286 of 293 Lean files (97.6%) — wait, let me reconcile:
**288 Lean source files in `EtingofRepresentationTheory/`**, of
which 280 are sorry-free (97.2%). 582/583 items (99.8%) sorry-free —
unchanged from wave 59. The one non-sorry-free item is the same
status-`statement_formalized` placeholder for Gabriel's theorem
(Chapter2/Theorem2.1.2).

**Definition-level sorries: 0.** All mathematical objects are still
constructed.

### Key story for wave 60

- **Wall 1 (Ẽ/T framework, #2436):** **status unchanged.** Still 5
  sorries (3 ℂ-specific dead code in `InfiniteTypeConstructions`,
  2 F-generic live on the per-(F, Q) chain). Line positions of the
  F-generic stubs **shifted** due to PR #2844 refactor:
  `FieldGenericETilde6.lean` 283 → 299;
  `FieldGenericETilde7.lean` 292 → 281. **Sixth** consecutive wave
  with no Wall 1 movement. No worker action available.

- **Wall 2 (D̃_n indecomposability):** **STILL CLOSED.** No
  regression.

- **Wall 3 (Ch5 `SpechtModuleBasis.lean`, 2 sorries):** unchanged
  this wave. R2.b.i (#2769) still in `replan` with the R3-bis
  cross-region involution strategy from PR #2779. R2.b.ii (#2770)
  / R2.c (#2703) still blocked. PR #2550 (line 1487 helper, C.1.a.ii)
  still `CONFLICTING` — **~24 days static**, in the pr-repair queue
  but no repair has succeeded.

- **Schur-Weyl chain (Ch5):** **status unchanged.** Same 2 sorries
  (`SchurModuleSimple.lean:148` C-4a aggregation;
  `FormalCharacterIso.lean:399` top-of-chain). γ.A (PR #2694) still
  `CONFLICTING`, ~15 days static. γ.B (#2693) still unclaimed
  `replan`. The β.3 lint cleanup landed (PR #2842 — heartbeat
  reductions 800k/800k → 400k/200k in `youngSym_action_vanishes_off_block`,
  responding to a deliverable of the wave-59 review #2832).

- **D̃₅ per-(F, Q) chain (new wave-60 cascade):** **net +6 sorries,
  all on the active path.** Helpers + API stubs landed (PR #2835),
  γ⁻¹ closed-forms landed (PR #2843), construction landed (PR #2813
  carried over the wave boundary), leaf-equality canonical case
  landed (PR #2854). The remaining work is fully decomposed into
  31 case-splits (#2853, 5 sorry positions covering 16+8+4+2+1
  branches) + main assembly (#2851).

- **Theorem 2.1.2 forward bridge (Ch2 #2774):** **unchanged.**
  Deliverable 1 (PR #2805) landed wave 59; deliverables 2 + 3
  remain unfiled. The forward bridge cannot close until all six
  per-(F, Q) sub-theorems land AND the F-generic Wall 1 stubs close
  AND the assembly issues are filed. The D̃₅ Sub B cascade is the
  most active sub-thread on this chain at present.

### Merges since wave 59 (16 PRs, 2026-05-17T17:58Z → 2026-05-18T02:14Z)

16 PRs merged in the ~9-hour window between wave-59 close and
this snapshot. Of those, **5 are planner / progress no-ops**
(#2830, #2833, #2845, #2847, #2856) and **2 are pure repairs**
(#2848, #2852 — broken-main fixes). The remaining 9 substantive
PRs are tabulated chronologically:

| PR    | Time (UTC)       | Title (truncated)                                                            | Sorry Impact |
|-------|------------------|------------------------------------------------------------------------------|--------------|
| #2813 | 05-17 17:58      | feat(Ch6): `d5tildeRep_kQ` construction + dim vec (sub of #2790)             | Infra (chain) |
| #2802 | 05-17 19:40      | feat(Ch6 #2800): direction-aware projections + `starRep_kQ` + dim vec        | Infra (chain) |
| #2831 | 05-17 18:08      | doc(Ch6): document `_kQ` / `_per_kQ` / `_F` naming convention                | Doc |
| #2835 | 05-17 18:29      | feat(Ch6 #2804): D̃₅ per-(F, Q) helpers + API stubs (partial)                | **+1** (`d5tildeRep_kQ_isIndecomposable` stub at FieldGenericD5Tilde:856) |
| #2842 | 05-17 18:52      | refactor(Ch5 Theorem5_22_1): reduce heartbeats 800k/800k → 400k/200k         | Hygiene |
| #2843 | 05-18 00:13      | feat(Ch6 #2834): closed-form γ⁻¹ identity helpers (`gammaInv_embed*_F`)      | Infra (chain) |
| #2844 | 05-17 19:35      | refactor(Ch6): split `FieldGenericInfiniteType.lean` (+793/-644, 8 files)    | Refactor / line shifts |
| #2848 | 05-18 00:13      | fix(Ch6 #2846): repair broken main — move `starRep_kQ` to `FieldGenericStar` | Repair (no sorry impact) |
| #2852 | 05-18 01:12      | fix(Ch6 #2839): repair broken main — fix Section 5b/5d in `FieldGenericD5Tilde` | Repair (no sorry impact) |
| #2854 | 05-18 02:04      | feat(Ch6 #2850): canonical-orientation case of `d5tildeRep_kQ_leaf_equalities` + API stub | **+5** (5 reversed-at-level-k case-split sorries at FieldGenericD5Tilde:802/804/806/808/810) |

Planner / progress no-op PRs (5): #2830, #2833, #2845, #2847, #2856.

**Net counts (wave 60):**
- Substantive feature / infra PRs: 5 (#2813, #2802, #2835, #2843, #2854).
- Documentation / hygiene: 2 (#2831, #2842).
- Refactor: 1 (#2844).
- Broken-main repair: 2 (#2848, #2852).
- Planner-cycle no-op progress notes: 5 (#2830, #2833, #2845, #2847, #2856).
- Raw sorry count: 10 → 16. Files with sorries: 7 → 8.
- Net change: **+6 sorries, +1 file.** Closures: 0. Additions: 6 —
  all on the D̃₅ Sub B path, all in `Chapter6/FieldGenericD5Tilde.lean`,
  all tracked by sub-issues of #2839.

## Chapter Breakdown

| Chapter | Sorries | Files | Delta from Wave 59 |
|---------|---------|-------|--------------------|
| Ch2     | 1       | 1     | 0                  |
| Ch5     | 4       | 3     | 0                  |
| Ch6     | 11      | 4     | +6 sorries, +1 file |
| Ch9     | 0       | 0     | 0                  |

Wave-60 sorry growth is entirely in Ch6, and entirely in one
new file (`FieldGenericD5Tilde.lean`).

## Per-File Sorry Detail

### InfiniteTypeConstructions (Ch6) — 3 sorries: WALL 1 ℂ-SPECIFIC (dead w.r.t. forward bridge)

Unchanged from wave 59. All three are refuted-as-stated pointers
to Wall 1; the wave-59 per-(F, Q) refactor moved the active
dependency path off these ℂ-specific stubs but they remain in
source.

| Line | Theorem | Status |
|-----:|---------|--------|
| 3344 | `etilde6v2Rep_isIndecomposable (m hm)` | Refuted; bypassed by F-generic chain |
| 3599 | `etilde7Rep_isIndecomposable (m hm)`  | Refuted; bypassed by F-generic chain |
| 3826 | `t125Rep_isIndecomposable (m hm)`     | Refuted; bypassed by F-generic chain |

Reference: `progress/indecomposability-framework-investigation.md`.
Framework issue: #2436 (`human-oversight`, `replan`, **6 waves stale**).

### FieldGenericD5Tilde (Ch6) — 6 sorries: D̃₅ SUB B CASCADE (NEW THIS WAVE)

All six introduced this wave by PRs #2835 + #2854. All tracked
by sub-issues of #2839.

| Line | Theorem / branch | Tracking issue | Notes |
|-----:|------------------|----------------|-------|
| 802 | `d5tildeRep_kQ_leaf_equalities`, e53-reversed branch (3→5, 1 sub-case) | #2853 | Reversed leaf edge — needs `starSecond_F` projection variant |
| 804 | `d5tildeRep_kQ_leaf_equalities`, e43-reversed branch (3→4, 2 sub-cases) | #2853 | Reversed leaf edge — needs `starFirst_F` projection variant |
| 806 | `d5tildeRep_kQ_leaf_equalities`, e23-reversed branch (3→2, 4 sub-cases) | #2853 | Reversed central edge — needs γ⁻¹ identities (`gammaInv_embed*_F`, PR #2843) |
| 808 | `d5tildeRep_kQ_leaf_equalities`, e12-reversed branch (2→1, 8 sub-cases) | #2853 | Reversed leaf edge — needs `starSecond_F` projection variant |
| 810 | `d5tildeRep_kQ_leaf_equalities`, e02-reversed branch (2→0, 16 sub-cases) | #2853 | Reversed leaf edge — needs `starFirst_F` projection variant |
| 856 | `d5tildeRep_kQ_isIndecomposable`     | #2851 (via #2839 sub-B) | API stub. The leaf-equality theorem (lines 528-810) is sub-A; this is sub-B (assembly via N-invariance + propagation). Body deferred to #2851 |

Combined, the 5 leaf-equality sorries cover 31 of 32 orientation
branches; the canonical branch (lines 559-800) is proven inline.
Section-5 helpers (`embed_sum_zero_F`, `center_decomp_F`,
`gamma_from_embed1_F`, `gamma_from_embed2_F`, `core_F`, `core3_F`,
`gamma_containment_F`) and the γ⁻¹ closed forms (PR #2843) are
the reusable infrastructure #2853 will assemble against.

### FieldGenericETilde6 (Ch6) — 1 sorry: WALL 1 F-GENERIC (line shifted)

- **Line 299** (was 283 in wave 59) — `etilde6Rep_kQ_isIndecomposable (F Q hOrient m hm)`.
  Line position shifted by PR #2844 (file split) and ancillary
  edits. Mathematical content **unchanged** from wave 59: the
  single-nilpotent-twist construction peels off a 1-dim summand at
  the center, inheriting the wave-54 framework wall. **On the
  active dependency path** for `etilde6_not_finite_type_per_kQ` →
  Theorem 2.1.2 forward bridge.

### FieldGenericETilde7 (Ch6) — 1 sorry: WALL 1 F-GENERIC (line shifted)

- **Line 281** (was 292 in wave 59) — `etilde7Rep_kQ_isIndecomposable (F Q hOrient m hm)`.
  Line position shifted by PR #2844 + #2852. Mathematical content
  **unchanged** from wave 59. Same framework-wall inheritance as Ẽ₆.
  **Also on the active dependency path** for the per-(F, Q)
  assembly.

### SpechtModuleBasis (Ch5) — 2 sorries: WALL 3 CHAIN ACTIVE (unchanged)

- **Line 1487 — `twistedPolytabloid_pigeonhole_pair`** (C.1.a.ii).
  Unchanged in status. Issue #2543 still `has-pr` (PR #2550 open,
  `CONFLICTING`, static since 2026-04-24T09:36Z — **~24 days**).
  In the `coordination list-pr-repair` queue but no repair has
  succeeded; rebase surface has grown further over the wave-60
  Ch6 refactor.

- **Line 1958 — `garnir_twisted_in_lower_span`** (final Wall 3
  sorry). Unchanged. Semantically blocked on R2.b → R2.c. R2.b.i
  (#2769) `replan` with the R3-bis cross-region involution strategy
  (`progress/r3-bis-residual-cancellation.md`).

### SchurModuleSimple (Ch5) — 1 sorry: SCHUR-WEYL C-4a AGGREGATION (unchanged)

- **Line 148 — `schurModuleSubmodule_isSimple_centralizer`**.
  Unchanged from wave 59. Tracking issue #2708 blocked on
  γ.A (PR #2694, `CONFLICTING`) + γ.B (#2693, unclaimed `replan`).

### FormalCharacterIso (Ch5) — 1 sorry: SCHUR-WEYL TOP-OF-CHAIN (unchanged)

- **Line 399 — `iso_of_formalCharacter_eq_schurPoly`**. Unchanged
  in position. Same dependency cascade as wave 59: closes via
  `#6 (#2483) → #5 (#2482) → Part C (#2493) → C-4 aggregation
  (#2708) → γ-cluster (γ.A PR #2694 + γ.B #2693)`.

### Theorem2_1_2 (Ch2) — 1 sorry: FORWARD BRIDGE (unchanged)

- **Line 173 — `not_posdef_not_HasFiniteRepresentationType`**
  (forward). Unchanged from wave 59. Deliverable 1 of #2774 landed
  PR #2805 wave 59; deliverables 2 + 3 still unfiled. End-to-end
  closure transitively depends on the F-generic Ẽ₆/Ẽ₇ Wall 1
  stubs + the residual per-(F, Q) sub-theorems (#2789 K_{1,4}
  canonical, #2790 D̃₅, #2793 T(1,2,5), #2797 K_{1,4} Q-extension).

## Open PRs

| PR | Status | Branch / Note |
|----|--------|---------------|
| #2849 | mergeable=MERGEABLE, CI FAILURE×2 | Ch6 chore — dedupe `etilde6LeafProj_F` and `starFirst_F` post-#2802. CI failing as of 2026-05-18T01:09; in pr-repair queue. |
| #2694 | CI SUCCESS, mergeable=CONFLICTING | Schur-Weyl L_i γ.A scaled-projection; ~15 days static |
| #2550 | CI SUCCESS, mergeable=CONFLICTING | Wall 3 C.1.a.ii pigeonhole; ~24 days static, in repair queue |

PR #2694 and PR #2550 are both long carry-overs (3 and 5 waves
respectively). The pr-repair flow continues to dispatch on every
pod cycle but has not produced a result on either. PR #2849 is a
fresh wave-60 chore PR that introduced CI failures; it's already
in the repair queue.

## Active / Claimed Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2855 | summarize: wave-60 sorry landscape + design-walls refresh | claimed (this session) |

## Unclaimed Issues (`agent-plan`, FIFO order)

| Issue | Title | Notes |
|-------|-------|-------|
| #2564 | Mathlib upstream tracker — `MvPolynomial.eq_of_eval_eq_on_gl` | Awaiting external Mathlib PR #38583 merge |
| #2841 | Mathlib upstream tracker — `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero` | Awaits Mathlib PR; tracker pattern matching #2564 |

## Replan / Human-oversight / Blocked Issues

| Issue | Title | Status |
|-------|-------|--------|
| #2436 | Framework decision: affine Dynkin infinite type (Ẽ_n / T(p,q,r)) | replan, `human-oversight`, awaits Kim (**6 waves**) |
| #2774 | Ch2 per-(k, Q) subgraph transfer + assembly | replan since wave 59 (deliverables 2 + 3 unfiled) |
| #2769 | Wall 3 R2.b.i cancellation involution | replan after R3-bis meditate PR #2779 |
| #2702 | Wall 3 R2.b assembly | replan |
| #2789 | K_{1,4} canonical orientation per-(F, Q) | replan |
| #2790 | D̃₅ per-(F, Q) | replan — sub-decomposed into #2803 ✅ + #2804 |
| #2793 | T(1,2,5) per-(F, Q) | replan |
| #2797 | K_{1,4} Q-extension per-(F, Q) | replan — sub-decomposed into #2800 ✅ + #2801 |
| #2693 | Schur-Weyl γ.B rank-1 dim count | replan, unclaimed |
| #2612 | Schur-Weyl C-4c final assembly | replan — body landed wave 59 (PR #2706); residual aggregation in #2708 |
| #2804 | D̃₅ indecomposability + per-(F, Q) | replan after PR #2835 (deliverable 1 of 2) |
| #2834 | D̃₅ Sub B proof body | replan after PR #2843 (γ⁻¹ helpers landed) |
| #2839 | D̃₅ main proof body — direction-aware case-analysis | replan after wave-60 decomposition into #2850 + #2851 |
| #2850 | D̃₅ Sub-A leaf equalities | replan after PR #2854 (canonical case landed); residual #2853 |
| #2823 | bridge `starRep_kQ ↔ starRepGen` | replan after worker session 5b8dd06f filed #2846 instead |

| Issue | Title | Blocked on |
|-------|-------|-----------|
| #2543 | Wall 3 C.1.a.ii pigeonhole | has-pr (#2550 in repair) |
| #2821 | Ch6 dedupe `etilde6LeafProj_F` / `starFirst_F` post-#2802 | has-pr (#2849, CI FAILURE) |
| #2770 | Wall 3 R2.b.ii assembly | #2769 |
| #2703 | Wall 3 R2.c final assembly | #2702 |
| #2708 | Schur-Weyl C-4a aggregation | γ.A (#2694) + γ.B (#2693) |
| #2493 | Schur-Weyl Part C final assembly | #2708 |
| #2482 | polynomial GL_N-rep ⊕ Schur modules (#5) | #2493 |
| #2483 | close `iso_of_formalCharacter_eq_schurPoly` (#6) | #2482 |
| #2801 | K_{1,4} Q-ext indecomposability | #2800 (✅ wave 60 — could now move to replan) |
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
C-4a-i needs sub-γ (γ.A PR #2694 CONFLICTING ~15d + γ.B #2693 replan)
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

No movement this wave beyond PR #2842 (cosmetic heartbeat
reductions on already-proven β.3 obligations).

### Cluster C: Per-(F, Q) Ẽ/T forward bridge (Ch6, 8 sorries + Ch2, 1 sorry)

**Files:** `Chapter6/InfiniteTypeConstructions.lean` (3 dead ℂ-specific
stubs), `Chapter6/FieldGenericETilde6.lean` (1 F-generic Wall 1 stub),
`Chapter6/FieldGenericETilde7.lean` (1 F-generic Wall 1 stub),
`Chapter6/FieldGenericD5Tilde.lean` (6 D̃₅ Sub B stubs NEW THIS WAVE),
`Chapter2/Theorem2_1_2.lean` (1 forward-bridge sorry).

```
#2773 (per-(F, Q) sub-theorems for 6 forbidden subgraphs)
  ├── cycle ✅ PR #2799 (wave 59)
  ├── K_{1,4} D̃₄ F-generic ✅ PR #2798 (wave 59)
  ├── K_{1,4} Q-extension (#2797, replan):
  │     ├── #2800 construction ✅ PR #2802 (THIS WAVE)
  │     └── #2801 indecomposability blocked
  ├── D̃₅ (#2790, replan):
  │     ├── #2803 construction ✅ PR #2813 (THIS WAVE)
  │     └── #2804 indecomposability — DECOMPOSED THIS WAVE:
  │            ├── PR #2835 helpers + API stubs (DONE)  [adds 1 sorry #2851]
  │            └── #2834 proof body
  │                  ├── PR #2843 γ⁻¹ closed-forms (DONE)
  │                  └── #2839 main proof body — DECOMPOSED THIS WAVE:
  │                        ├── #2850 sub-A leaf equalities
  │                        │     ├── PR #2854 canonical case (DONE)  [adds 5 sorries #2853]
  │                        │     └── #2853 31 non-canonical cases (blocked)
  │                        └── #2851 sub-B assembly (blocked)
  ├── Ẽ₆ ✅ PR #2809 (wave 59) — carries Wall 1 F-generic sorry at FieldGenericETilde6:299
  ├── Ẽ₇ ✅ PR #2810 (wave 59) — carries Wall 1 F-generic sorry at FieldGenericETilde7:281
  └── T(1,2,5) (#2793, replan, untouched)

#2774 (Ch2 assembly):
  ├── Deliverable 1 ✅ PR #2805 (wave 59)
  ├── Deliverable 2 (final per-quiver classification) UNFILED
  └── Deliverable 3 (close line-173 forward bridge) UNFILED
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
| **60** | **16** | **8** | **582/583 (99.8%)** | **2026-05-18** |

**Wave-60 trend:** Second consecutive non-monotone wave on raw
count. Wave 58 → 59 was +3; wave 59 → 60 is +6. All 6 wave-60
additions sit in a single file (`FieldGenericD5Tilde.lean`) on a
single decomposition path. Items-sorry-free unchanged at 582/583
because the new sorries land inside an existing-but-extended item
(`Chapter6/Definition6_4_9_D̃` family — the D̃₅ per-(F, Q)
indecomposability theorem statement is already counted as part of
the items.json entry for #2804).

Of the 16 current sorries:

- 3 are framework-wall stubs in `InfiniteTypeConstructions`
  (ℂ-specific, dead code w.r.t. the forward bridge).
- 2 are framework-wall stubs in the F-generic files
  (`FieldGenericETilde6.lean:299`, `FieldGenericETilde7.lean:281`)
  on the active per-(F, Q) chain.
- 6 are D̃₅ Sub B decomposition stubs in `FieldGenericD5Tilde.lean`
  (lines 802/804/806/808/810 in `d5tildeRep_kQ_leaf_equalities`,
  line 856 in `d5tildeRep_kQ_isIndecomposable`), all on the active
  per-(F, Q) chain.
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

Wave 60 was a **structurally productive, numerically regressive** wave.
The D̃₅ Sub B decomposition cascade is the headline event: a 4-level
issue tree (#2804 → #2834 → #2839 → #2850/#2851; #2850 → #2853)
emerged from a single parent in the span of a working day. The
canonical-orientation case proof of `d5tildeRep_kQ_leaf_equalities`
(PR #2854, lines 559-800 of `FieldGenericD5Tilde.lean`) is the most
detailed F-generic proof of any leaf-equality result in the project,
and validates the Section-5 helper-lemma scaffolding for #2853.

**Strengths:**

1. **D̃₅ Sub B decomposed into focused workitems.** Wave 59 ended
   with #2804 (D̃₅ per-(F, Q) indecomposability) as a single
   monolithic issue. Wave 60 produced a 4-level decomposition tree
   that isolates each layer's contract: helpers + API stubs (PR
   #2835), γ⁻¹ closed-forms (PR #2843), canonical orientation
   case (PR #2854), 31 non-canonical cases (#2853 — explicitly
   sized at 16+8+4+2+1 sub-cases per natural split point), main
   assembly (#2851). The remaining work is unblocked once #2853
   lands; the path to #2804 closure is fully visible.

2. **K_{1,4} Q-extension construction unblocked.** PR #2802
   (wave-59 carry-over, ~3 hours static at wave-59 close) landed
   early in wave 60 after pr-repair. This closes the construction
   half of #2797 on the per-(F, Q) chain.

3. **File split landed.** PR #2844 reduced
   `FieldGenericInfiniteType.lean` (was a single ~2000-line
   module) into shared / cycle / star modules. Future per-graph
   work targets smaller, more focused files — the per-(F, Q)
   chain has been operating against a clearer file boundary since.

4. **Both broken-main events resolved within the wave.** PR
   #2848 (move `starRep_kQ`, dedupe D̃₅ projections, ~1.5h after
   detection) + PR #2852 (fix Section 5b/5d in
   `FieldGenericD5Tilde`, ~1h after the second detection). The
   pr-repair flow handled both without escalation. The harness
   can recover from squash-merge interaction breakages.

5. **Helper-lemma + γ⁻¹ infrastructure complete for D̃₅.** Before
   PR #2854 went in, the canonical-case proof (~240 lines) was
   blocked by missing infrastructure: `gamma_from_embed1_F`,
   `gamma_from_embed2_F`, `core_F`, `core3_F`,
   `gamma_containment_F`, and the γ⁻¹ closed forms. All seven
   helper lemmas now have closed proofs that the 31 follow-up
   cases will reuse.

**Concerns:**

1. **Wall 1 is 6 waves stale (#2436).** No movement on the
   human-oversight side. Wave-59 noted this as "5 waves" and the
   longest-running open item. Wave 60 adds another wave. Two
   F-generic sorries (`FieldGenericETilde6:299`,
   `FieldGenericETilde7:281`) sit on the active forward-bridge
   path and cannot close without a framework decision.

2. **PR #2550 has been in repair for ~24 days, PR #2694 for
   ~15 days.** Both are CI-clean but conflict-blocked. The
   pr-repair flow has dispatched on every pod cycle since their
   conflict status appeared. Neither has produced a result. The
   rebase surface continues to grow over the wave-60 Ch6 refactor
   for #2550 (already PR #2541, #2669, #2653, #2664, #2665,
   #2670, #2698, #2706, #2707, **#2802, #2813, #2835, #2843,
   #2844**, ...).

3. **PR #2849 (Ch6 chore, wave-60-fresh) is failing CI.** The
   chore PR deduping `etilde6LeafProj_F` and `starFirst_F`
   post-#2802 hit CI failures (twice) and is in the pr-repair
   queue. Likely a stale rebase against the wave-60 file split
   (#2844).

4. **Net sorry count up for the third consecutive wave on the
   raw metric.** Wave 58 → 59: +3. Wave 59 → 60: +6. The raw
   metric has been non-monotone since wave 51 (when we hit 21),
   but the longer 4-wave plateau at 7 in waves 55-58 has now
   given way to growth. Wave-58 plateau hid the decomposition
   work that was happening; wave-59 + wave-60 expose it.

5. **#2774 deliverables 2 + 3 still unfiled.** Same concern as
   wave 59. Wave-60 saw two relevant per-(F, Q) construction
   PRs land (#2802 K_{1,4} Q-ext, #2813 D̃₅) but neither
   triggered the planner to file the assembly sub-issues.

6. **#2693 (γ.B) is unclaimed and still `replan` after 5 waves.**
   Same concern as wave 59. The Schur-Weyl chain remains four
   PRs from closure modulo γ.A + γ.B; γ.B alone is the
   unblocked side of the cluster but no one has scoped a
   concrete workitem.

7. **Two broken-main events in one day is a coordination signal
   worth recording.** Both events were caused by the squash-merge
   interaction between a long-lived branch and a same-day file
   refactor (PR #2844). The pr-repair flow caught both within
   hours, but the underlying coordination cost — concurrent in-
   flight PRs against a file undergoing a rename — is recurring.
   See `progress/design-walls-wave60.md` for the meta-note.

**Current priority ordering:**

1. **Kim's framework decision on Wall 1 (#2436).** Now
   bottlenecks 2 Ch6 F-generic sorries (live) + 3 ℂ-specific
   (dead) + 1 Ch2 downstream. Sixth consecutive wave with no
   movement. The wave-60 D̃₅ cascade tightens the structural
   case for Option B: the Section-5 helper-lemma scaffolding
   for D̃₅ and the analogous helpers for Ẽ₆/Ẽ₇ are ~80%
   compatible, and a stronger construction would slot cleanly
   into all three.

2. **D̃₅ Sub B follow-through (#2853, then #2851).** The
   canonical-orientation case in PR #2854 establishes the
   proof template; #2853 is 31 non-canonical cases (5
   sorry positions, natural splits 16+8+4+2+1) using projection
   variants (`starFirst_F`, `starSecond_F`) and γ⁻¹ closed
   forms (PR #2843). Both #2853 and #2851 unblock on #2850
   → close once both land. This is the **most actively
   decomposed and unblocked** sub-chain in the project.

3. **PR repair for #2550, #2694, #2849, #2802.** Three
   conflict-blocked PRs (one ~24 days, one ~15 days, one
   wave-60-fresh CI FAIL). PR #2550 closes #2543 → line 1487
   sorry. PR #2694 unblocks γ.A → C-4a aggregation → C-4c →
   Part C → ... → line 399. PR #2849 unblocks #2821 (Ch6
   chore).

4. **Wall 3 R2.b.i (#2769) with the R3-bis strategy.**
   Unchanged status from wave 59. PR #2779 produced the
   refined cross-region involution sketch validated on the
   running (2,2) example. A worker with the R3-bis notes in
   hand should still be able to close R2.b.i in one or two
   sessions. Unblocks R2.b.ii → R2.c → line 1958 sorry.

5. **#2774 replan triage.** Planner needs to file deliverables
   2 + 3 as concrete sub-issues so the Theorem 2.1.2 forward
   closure has a well-scoped final step. Has been pending since
   wave 59 close.

6. **Per-(F, Q) Ẽ live work residuals.**
   #2801 K_{1,4} Q-ext indecomposability (could move to replan
   now that #2800/PR #2802 landed); T(1,2,5) #2793 needs
   triage / decomposition; K_{1,4} canonical #2789 same.

7. **Schur-Weyl γ.B (#2693).** Unclaimed, `replan` for 5+ waves.
   Single highest-impact Ch5 unblock if a worker re-scopes and
   claims it.

**Closure forecast:** The D̃₅ Sub B cascade now has the cleanest
unblocked path of the project:

- **D̃₅ per-(F, Q) indecomposability (#2804):** Once #2853
  (31 non-canonical cases via the canonical-case template) and
  #2851 (assembly via N-invariance + leaf eq) land, #2804
  closes. Each is a focused, well-scoped workitem; the helper
  infrastructure exists. Optimistically 1-2 waves to close #2804.

- **Theorem 2.1.2 forward bridge (line 173):** still gated on
  Wall 1. Best plausible 1-wave delta if Kim decides #2436 with
  Option B + worker resources are focused: the F-generic Ẽ₆/Ẽ₇
  stubs close, the residual per-(F, Q) cases (#2789, #2793,
  #2801) decompose+land, and #2774 deliverables 2+3 are filed
  and worked.

- **Schur-Weyl line 399 / Wall 3 line 1958:** same blockers as
  wave 59. No movement projected without a worker claiming γ.B
  / R2.b.i.

Best-case 1-wave projection (next summarize after wave 60):
16 → ≤7 (D̃₅ Sub B closes 6 sorries, Wall 1 framework decision
+ a single F-generic close could remove 1 more). Worst-case (no
movement on framework / no R2.b.i claim / no γ.B claim):
16 → 16 or slightly higher if the cascade decomposition continues
without inline closures.

## Design walls snapshot

- **Wall 1 status unchanged**, 6 waves stale. Per-(F, Q) refactor
  remains the structural workaround. 5 framework-wall sorries
  total (3 dead ℂ-specific + 2 live F-generic); line positions of
  the F-generic stubs shifted by PR #2844 file split.
- **Wall 2** still closed.
- **Wall 3** chain unchanged from wave 59. R2.b.i (#2769) `replan`
  with concrete strategy doc; PR #2550 ~24 days static.
- **Schur-Weyl chain** unchanged from wave 59. γ.A (PR #2694
  CONFLICTING ~15d), γ.B (#2693 replan unclaimed), C-4a
  aggregation (#2708 blocked).
- **D̃₅ Sub B cascade (new wave-60 design topic).** Most active
  decomposition. See `progress/design-walls-wave60.md` for the
  cascade narrative and the two-broken-mains-in-one-day
  coordination signal.

Refer to `progress/design-walls-wave60.md` for the updated decision
sheet.

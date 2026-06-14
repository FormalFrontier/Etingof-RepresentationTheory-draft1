## Current state

The last sorry-landscape snapshot is `progress/sorry-landscape.md`
(wave 62, generated via #2927 on 2026-05-19T03:00Z; wave-62 issue
closed 2026-05-18T22:55Z but the file landed in the wave-62 PR
itself). Since the wave-62 issue closed, **21 substantive PRs**
have merged on `main` (excluding the 4 `progress:` planner/session
no-op commits), well past the 10+ threshold for a wave-63
summarise.

Sorry count: **20 sorries across 12 files** (vs 19/11 at wave 62).
Net delta: **+1 sorry, +1 file** — entirely accounted for by the
introduction of `Chapter6/FieldGenericD7Tilde.lean` (new D̃₇
per-(F, Q) helper), whose `d7tildeRep_kQ_isIndecomposable` sorry
(tracked by #2967) is the +1.

The wave-63 story is **the non-adjacent-branches leaf-case Phase 1
+ Phase 2 cascade landing**:

* PR #2952 — Phase 1 setup (lattice extraction + leaf-neighbour
  decomposition, ~330 lines).
* PR #2956 — Case A: T(1, 2, 5) at v₀ (`chain.length ≥ 6`,
  side_arm extends).
* PR #2958 — Case B: T(1, 2, 5) at v₀ via arm₁/arm₂
  (chain.length ≥ 6, an arm extends).
* PR #2961 — Cases C-main + D (4 ≤ chain.length < 6, side_arm or
  both arms extend).
* PR #2966 — Case C.short tractable sub-cases (Ẽ₇ at v₀ for
  vertexDegree x = 3, T(1, 2, 5) for chain.length = 5 and the two
  tractable chain.length = 4 sub-cases).
* PR #2970 — Case C.short all-leaves residual chain.length = 4 via
  D̃₇ dispatch (depends on the D̃₇ helper).
* PR #2979 — Partial Case E coverage (E.aa via Ẽ₆ at w + E.s1c4
  via D̃₇) plus residual decomposition into #2974/#2976/#2977/#2978.

Foundation work feeding this cascade:

* PR #2933 (sub-A1 of #2919) — leaf-case helper signature avoiding
  general D̃_n.
* PR #2941 — strengthened leaf_case signature + Ẽ₆/Ẽ₇ embedder
  stubs.
* PR #2943 (sub-A2 of #2919) — outer assembly
  `non_adjacent_branches_infinite_type_per_kQ` (with #2959 hot-fix
  for the signature delta).
* PR #2945 — `embed_etilde6_in_tree_per_kQ` body (T(2, 2, 2)
  embedding).
* PR #2947 — `embed_etilde7_in_tree_per_kQ` body (T(1, 3, 3)
  embedding).
* PR #2968 — `Chapter6/FieldGenericD7Tilde.lean` per-(F, Q) D̃₇
  helper (`d7tildeRep_kQ` real body, indecomposability deferred to
  #2967).

Six review audits this wave, all PASS verdicts:

* PR #2931 — audit `embed_t125_in_tree_per_kQ` (from #2928).
* PR #2940 — audit D2 wrapper trilogy per-(F, Q) (from #2934).
* PR #2942 — audit `single_branch_leaf_both_extend_t122_per_kQ`
  (from #2935).
* PR #2969 — audit `non_adjacent_branches_leaf_case_per_kQ` stub +
  #2941 signature delta (from #2948).
* PR #2971 — audit `embed_etilde{6,7}_in_tree_per_kQ` bodies (from
  the audit issue for #2945 + #2947).
* PR #2975 — audit Phase 1 setup + Phase 2 Cases A/B/C-main/D
  (from #2972).
* PR #2981 — audit Case C.short residual + D̃₇ helper (PRs #2966 +
  #2968 + #2970, from #2973).

The remaining sorries on the Theorem 2.1.2 forward bridge chain:

* `non_adjacent_branches_leaf_case_per_kQ`
  (`FieldGenericNonAdjacentBranches.lean:1093`) — residual `sorry`
  for the chain.length = 3 mixed arms + chain.length = 5 +
  chain.length ≥ 6 all-leaves sub-cases. Decomposed into
  #2974/#2976/#2977/#2978 (all blocked on #2955, which carries
  `replan`).
* `single_branch_leaf_case_both_extend_per_kQ`
  (`FieldGenericTpqr.lean:1286`) — four-way dispatcher. Sub-A
  #2907 / PR #2911 in `/repair` (CONFLICTS), sub-B #2908 + sub-C
  #2909 claimed, sub-D #2910 landed.
* Earlier per-(F, Q) leaves still tracked: #2789/#2801 (K_{1,4}),
  #2853/#2851 (D̃₅ via #2834 → #2839 → #2850 cascade), #2793
  (T(1, 2, 5)), #2967 (D̃₇ indecomposability), #2436 (Wall 1
  framework decision, human-escalated).

## Deliverables

Three artefacts, mirroring the wave-62 pattern:

1. **Regenerate `progress/sorry-landscape.md`** for wave 63. Walk
   each file from the `grep -rn 'sorry'` list, give a one-line
   "what is the sorry, who tracks it, what's blocking it". Headline
   the +1 file change (`FieldGenericD7Tilde.lean`) and the
   non-adjacent-branches leaf-case cascade closure (Phase 1 + Phase
   2 Cases A/B/C-main/C-short/D + partial E).

2. **Write the wave-63 summary file** at
   `progress/summaries/2026-05-20-wave-63.md`. Use the wave-62
   template (`progress/summaries/2026-05-19-wave-62.md`):
   `Headline / Key achievements / Sorry landscape delta / Active
   frontiers / What's next`. Keep it factual; cross-reference the
   audit reports under `progress/reviews/2026-05-19-*.md`.

3. **(Optional) Refresh `progress/design-walls-*.md`** *only if*
   there's a structural change in the active frontiers since
   wave-62. The Wall 1 (framework decision #2436) and Wall 3
   (Schur-Weyl) walls were already current at wave-62; check
   whether the d5tilde Sub-A2 cascade has produced new wall
   updates this wave. If not, skip — don't manufacture wall
   churn.

## Context

* Wave-62 issue (#2927) closed 2026-05-18T22:55Z. Wave-62
  summary file: `progress/summaries/2026-05-19-wave-62.md`.
* Recent audit reports (read these before writing the summary):
  - `progress/reviews/2026-05-19-non-adjacent-branches-leaf-case-api-stub.md`
  - `progress/reviews/2026-05-19-non-adjacent-branches-outer-assembly-per-kQ.md`
  - `progress/reviews/2026-05-19-non-adjacent-branches-leaf-case-phase-1-and-cases-a-b-c-d.md`
  - `progress/reviews/2026-05-19-case-c-short-and-d7tilde-helper.md`
  - `progress/reviews/2026-05-19-t122-leaf-both-extend-per-kQ.md`
  - `progress/reviews/2026-05-19-embed-t125-in-tree-per-kQ.md`
* The 21 substantive PRs (in merge order, oldest first):
  #2931, #2933, #2940, #2941, #2942, #2943, #2945, #2947, #2948
  (audit issue → PR #2969), #2952, #2956, #2958, #2959, #2961,
  #2966, #2968, #2969, #2970, #2971, #2975, #2979, #2981. (Total
  is actually 22 once you count #2948 as a review PR — verify
  against `git log --oneline origin/main --since='2026-05-18T22:55:19Z'`
  before quoting numbers.)
* Replan-labelled issues still in queue at wave-63 close
  (do **not** triage these — `/replan` owns them):
  #2436, #2693, #2702, #2769, #2774, #2789, #2790, #2793, #2797,
  #2801, #2804, #2823, #2834, #2839, #2841, #2850, #2875, #2877,
  #2904, #2905, #2908, #2909, #2919, #2932, #2939, #2951, #2955,
  #2960, #2967, #2612.

## Verification

* `progress/sorry-landscape.md` updated, dated 2026-05-20.
* `progress/summaries/2026-05-20-wave-63.md` exists and follows
  the wave-62 template.
* The headline sorry counts and PR enumeration agree with
  `grep -rn '^\s*sorry\s*$' EtingofRepresentationTheory/*.lean
   EtingofRepresentationTheory/**/*.lean | wc -l` (20 at the
  time of planning) and
  `git log --oneline origin/main --since='2026-05-18T22:55:19Z'
   | grep -v 'progress:' | wc -l` (21 at the time of planning).
* `lake build EtingofRepresentationTheory` passes (run after
  `lake exe cache get`).
* No CLAUDE.md or PLAN.md edits.

## Notes

* This is purely an observational / narrative wave — no code
  changes expected. The summary issue's PR touches only files
  under `progress/`.
* If the regenerated sorry-landscape reveals a sorry that's not
  tracked by any open issue, file a separate `feature` or `chore`
  issue noting the orphan and link from the summary. Do **not**
  attempt to close orphan sorries from inside this summarise
  cycle.

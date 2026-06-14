## Current state

Wave 63 closed **four** chore PRs that refreshed citations and
docstrings affected by the non-adjacent-branches Phase 2 cascade.
None have been audited:

* **PR #2983** (closed #2982) — file docstring refresh for
  `Chapter6/FieldGenericNonAdjacentBranches.lean`: replaced the
  "API stub" framing with a "Status" section summarising the
  landed Phase 1 + Phase 2 dispatch and citing the four sub-
  issues for the residual.
* **PR #2989** (closed #2986) — file docstring refresh for
  `Chapter6/FieldGenericTpqr.lean`: rewrote the leaf-arm dispatch
  bullet to describe the actual case-split (a₂/a₃ degree-2 split,
  D-type collapse via `tree_two_leaf_posdef`); replaced the
  `single_branch_leaf_case_per_kQ` "API stub" sentence with a
  pointer at the remaining stub
  `single_branch_leaf_case_both_extend_per_kQ` (line 1233, tracked
  by #2905 sub-chain #2907/#2908/#2909/#2910); added
  `non_adjacent_branches_infinite_type_per_kQ`
  (`FieldGenericAssembly.lean:75`, PR #2943) to the sibling-
  wrapper enumeration.
* **PR #2993** (closed #2990) — cite sub-issues
  #2974/#2976/#2977/#2978 in two residual-sorry comment blocks
  in `FieldGenericNonAdjacentBranches.lean` (Block 1 upstream
  enumeration at lines 994-1003 → 4 bullets; Block 2 residual
  site at lines 1098-1102 → 4 bullets).
* **PR #2994** (closed #2991) — cite sub-issues
  #2907/#2908/#2909/#2910 (and parent #2905) in the TODO block
  at lines 1267-1279 of `Chapter6/FieldGenericTpqr.lean`
  (`single_branch_leaf_case_both_extend_per_kQ`).

The two NonAdjacentBranches PRs (#2983 + #2993) address audit
concerns raised by PR #2984's audit of PR #2979 (Case E.aa +
E.s1c4 partial coverage of #2955):

* PR #2984's **D3 concern** — residual comment-block enumeration
  did not match the 4-way sub-issue decomposition. Resolved by
  PR #2993.
* PR #2984's **D5(a) concern** — same enumeration mismatch
  cross-referenced. Resolved by PR #2993.
* PR #2984's **D5(b)/(c) concerns** — file docstring stale
  ("API stub" framing missing D̃₇ helper inventory). Resolved
  by PR #2983.

PRs #2989 + #2994 cover the parallel cleanup on
`FieldGenericTpqr.lean`: #2989 refreshes the file-level docstring
to reflect `single_branch_leaf_case_per_kQ` having a real body
(post-#2903), and #2994 cites the #2905 sub-chain in the inner
TODO block. The wave-63 planner cycle (`ffed68b7`) intentionally
separated these: #2986 explicitly scoped out the TODO block, and
#2991 picked it up as a follow-up chore.

## Deliverables

Consolidated six-dimension audit of the four chore PRs, with
verdicts written to
`progress/reviews/2026-05-20-wave-63-chore-citation-refresh.md`:

* **D1 — Citation accuracy on `FieldGenericNonAdjacentBranches.lean`
  Block 1** (post-#2993, lines 994-1003 era): verify the 4 bullets
  cite #2974 (D̃₆ all-leaves), #2976 (Ẽ₇ mixed at chain.length=3),
  #2977 (D̃₈ at chain.length=5), #2978 (parametric D̃_n at
  chain.length≥6) with correct scope descriptions matching each
  sub-issue's body. Confirm Block 2 (residual-sorry site, post-#2993
  lines 1098-1102 era) mirrors Block 1's 4-bullet shape with the
  same issue citations.

* **D2 — Citation accuracy on `FieldGenericTpqr.lean` TODO block**
  (post-#2994, lines 1267-1279 era): verify the bullets cite #2907
  (Ẽ₇ embed q,r≥3), #2908 (T(1,q,2) b₃-leaf split), #2909
  (T(1,2,r) b₂-leaf split), #2910 (T(1,2,2)=D₅ posdef
  contradiction) plus parent #2905, with scope descriptions
  matching each sub-issue's body. Confirm consistency with the
  file-level docstring refreshed by PR #2989 (see D6).

* **D3 — `FieldGenericNonAdjacentBranches.lean` file docstring
  accuracy** (post-#2983, lines 27-90 era): verify the "Status"
  section accurately summarises Phase 1 setup + Phase 2 dispatch
  (Cases A/B/C-main/C.short/D + partial E.aa/E.s1c4) and lists the
  four residual sub-issues. Verify
  `d7tilde_not_finite_type_per_kQ` and `embed_d7tilde_in_tree_per_kQ`
  are mentioned in the per-(F, Q) library inventory. Verify the
  "Why a different strategy" paragraph mentions D̃₇ alongside
  Ẽ₆/Ẽ₇/T(1,2,5).

* **D4 — Audit-concern closure**: confirm the three concerns
  raised by PR #2984 (D3, D5(a), D5(b)/(c)) are fully resolved
  by the combined effect of PRs #2983 + #2993. No new concerns
  introduced.

* **D5 — Build sanity + cross-file consistency**: verify
  `lake build EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches`
  and
  `lake build EtingofRepresentationTheory.Chapter6.FieldGenericTpqr`
  both pass with exactly the expected `declaration uses sorry`
  warning(s) at the documented residual sites (1 sorry in
  `FieldGenericNonAdjacentBranches`, 1 sorry in `FieldGenericTpqr`
  at `single_branch_leaf_case_both_extend_per_kQ:1240`). Confirm
  no transitive build breakage in downstream files
  (`FieldGenericAssembly`).

* **D6 — `FieldGenericTpqr.lean` file docstring accuracy**
  (post-#2989, lines 11-48 era): verify the leaf-arm dispatch
  bullet describes the actual case-split (a₂/a₃ degree-2 split,
  D-type collapse) and points at
  `single_branch_leaf_case_both_extend_per_kQ` as the remaining
  API stub with #2905 sub-chain citation
  (#2907/#2908/#2909/#2910). Verify the sibling-wrapper
  enumeration includes
  `non_adjacent_branches_infinite_type_per_kQ`
  (`FieldGenericAssembly.lean:75`, PR #2943). Verify consistency
  with the inner TODO block from PR #2994 (see D2).

For each verdict, cite the exact post-PR line numbers and quote
the relevant comment text. Report PASS / CONCERN / FAIL per
dimension and a one-paragraph summary verdict.

## Context

* Parent (decomposing-via-chore-PRs): #2955 (residual decomposition
  into #2974/#2976/#2977/#2978) and #2905 (residual decomposition
  into #2907/#2908/#2909/#2910).
* Audit that originally raised the concerns: PR #2984 (audit of
  PR #2979).
* Audit precedent for file-level docstring refresh: PR #2984's D5
  pattern. The D5 dimension is the natural place to confirm cross-
  file consistency on this consolidated audit; D3 and D6 carry the
  two file-docstring substance checks.
* Previous reviews of the wave-63 cascade (already merged):
  PR #2969 (#2933 + #2941 signature delta), PR #2975 (Phase 1 +
  Cases A/B/C-main/D), PR #2981 (Case C.short + D̃₇ helper),
  PR #2984 (Case E.aa + E.s1c4).
* No code changes expected — this is a documentation/citation
  consistency audit. Worker should verify against the merged
  PRs by reading the affected files at HEAD and cross-referencing
  the sub-issue bodies.

## Verification

* Audit report written to
  `progress/reviews/2026-05-20-wave-63-chore-citation-refresh.md`
  with six dimension verdicts + summary.
* Build state recorded: `lake build` on the two affected modules
  passes with documented sorry counts.
* If any dimension verdicts CONCERN or FAIL, post follow-up
  chore issues (do not include code changes in the review PR).

## Sizing

Small. Four chore PRs, all pure citation/docstring changes; no
mathematical content. Estimate: 1 session, ~350-line audit
report. The four cross-referenced sub-issues (#2974/#2976/#2977/
#2978) and four sibling sub-issues (#2907/#2908/#2909/#2910)
should each be opened in the GitHub UI and their scope
descriptions compared against the in-file bullets.

## Amendment note (planner cycle 14799d02)

This issue body was amended by a follow-on planner cycle to:
1. Correct the citation error in the original "Current state"
   bullet 1, which attributed the `FieldGenericNonAdjacentBranches.lean`
   file-docstring refresh to PR #2989. The actual PR for that
   refresh is **#2983** (closing #2982). PR #2989 (closing #2986)
   is the parallel `FieldGenericTpqr.lean` file-docstring refresh.
2. Add **D6** to audit the previously-uncovered substance of
   PR #2989 (the Tpqr file-docstring refresh). The original five-
   dimension audit covered only #2993 (D1), #2994 (D2), and the
   NonAdjacentBranches docstring refresh (D3, mis-cited as #2989
   but described as the NonAdjacentBranches "Status" section
   refresh — i.e. PR #2983's actual content).
3. Update D3 / D4 / Verification / Sizing to reference the
   corrected PR list (#2983 + #2989 + #2993 + #2994).

## Current state

The file docstring of
`EtingofRepresentationTheory/Chapter6/FieldGenericTpqr.lean` is
stale relative to what's landed on `main`.

Specifically, lines 27-29 of the file-level docstring claim:

> `single_branch_leaf_case_per_kQ` is introduced here as an API
> stub with a `sorry` body, tracked by a follow-up issue. Mirrors
> the API-stub precedent set by `t125_not_finite_type_per_kQ`
> (`FieldGenericT125.lean`).

This was accurate when PR #2903 introduced
`single_branch_leaf_case_per_kQ` alongside the API stub for
`single_branch_not_posdef_infinite_type_per_kQ`, but the body of
`single_branch_leaf_case_per_kQ` has since landed (the theorem at
`FieldGenericTpqr.lean:1306` is now substantively proved — it
case-splits on whether `a₂` and `a₃` extend, then either delegates
to `single_branch_leaf_case_both_extend_per_kQ` or closes via
`tree_two_leaf_posdef`).

The remaining `sorry` in this file (`FieldGenericTpqr.lean:1286`)
sits in `single_branch_leaf_case_both_extend_per_kQ`, not in
`single_branch_leaf_case_per_kQ`. That sorry is correctly described
by the per-theorem docstring at lines 1223-1232.

This is the direct analogue of the docstring-refresh chore that
PR #2983 (issue #2982) handled for
`FieldGenericNonAdjacentBranches.lean` after the leaf-case body
landed in wave 63.

## Deliverables

Refresh the file-level docstring of
`Chapter6/FieldGenericTpqr.lean` (lines 11-44, the
`/-! … -/` block):

1. **Lines 23-25** (the leaf-arm dispatch bullet): keep the bullet,
   but rewrite from a "delegate to API stub" framing to a "delegate
   to `single_branch_leaf_case_per_kQ`, which case-splits on
   whether `a₂` / `a₃` extend and dispatches to
   `single_branch_leaf_case_both_extend_per_kQ` (still an API stub,
   tracked by #2905 sub-chain #2907/#2908/#2909/#2910) or closes
   inline via `tree_two_leaf_posdef`" framing. Keep it factual; do
   not editorialise.

2. **Lines 27-29** (the "introduced here as an API stub" sentence):
   replace with a single sentence pointing at the *current* API
   stub — `single_branch_leaf_case_both_extend_per_kQ` at line
   1233, tracked by the #2905 sub-chain.

3. **Lines 31-43** (the audit-pattern recipe + sibling wrapper
   enumeration): verify still accurate. The sibling-wrapper list
   should now include the
   `non_adjacent_branches_infinite_type_per_kQ` wrapper landed by
   PR #2943 (file: `Chapter6/FieldGenericAssembly.lean`); add a
   bullet if missing.

4. **Per-theorem docstring at lines 1300-1305** (the
   `single_branch_leaf_case_per_kQ` docstring): verify that the
   prose accurately describes the case-split implemented in the
   body. If it still calls itself an "API stub", rewrite to
   describe the actual dispatch logic. Keep it short.

Do **not** modify any theorem statement or proof. Pure docstring
edit.

## Context

* Precedent for this kind of refresh: PR #2983 (issue #2982) for
  `FieldGenericNonAdjacentBranches.lean`. Mirror its surgical
  scope.
* The theorem `single_branch_leaf_case_per_kQ` lives at lines
  1306-1407 of `FieldGenericTpqr.lean`. The internal dispatch is
  visible from line 1362 (`exact
  single_branch_leaf_case_both_extend_per_kQ adj …`).
* Sub-chain status (do not list this in the docstring — it goes
  stale fast — just point at the parent issue):
  - #2907 (Ẽ₇, both arms ≥ 3) — PR #2911 in /repair (CONFLICTS).
  - #2908 (T(1, q, 2), b₃ leaf) — claimed.
  - #2909 (T(1, 2, r), b₂ leaf) — claimed.
  - #2910 (T(1, 2, 2)) — landed via PR #2912.

## Verification

* `git diff main -- Chapter6/FieldGenericTpqr.lean` shows changes
  only inside the file-level `/-! … -/` docstring (lines 11-44)
  and possibly the theorem docstring at lines 1300-1305. No
  changes outside those line ranges.
* `lake build EtingofRepresentationTheory.Chapter6.FieldGenericTpqr`
  passes (docstring edits should be trivially compatible, but
  verify).
* No new `sorry`s introduced. Existing `sorry` at line 1286 left
  intact.

## Notes

* Strictly chore-level. Mark the PR with `chore(Ch6):` title
  prefix to match the convention used by PR #2983.
* If during the refresh you notice other stale lines in
  neighbouring docstrings (e.g., the per-theorem docstring of
  `single_branch_leaf_case_both_extend_per_kQ` at lines 1219-1232),
  fold them in *only* if they're also stale relative to `main`.
  Do not expand scope to fix non-stale prose.

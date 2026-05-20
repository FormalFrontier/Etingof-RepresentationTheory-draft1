# Review: wave-63 chore citation/docstring PRs #2983 / #2989 / #2993 / #2994

**Issue:** https://github.com/kim-em/Etingof-RepresentationTheory-draft1/issues/2995
**PRs audited (all merged):**
- #2983 (closes #2982) — `FieldGenericNonAdjacentBranches.lean` file docstring refresh, merged 2026-05-19T15:42:53Z
- #2989 (closes #2986) — `FieldGenericTpqr.lean` file docstring refresh, merged 2026-05-20T00:21:25Z
- #2993 (closes #2990) — `FieldGenericNonAdjacentBranches.lean` residual-sorry comment blocks (cite #2974/#2976/#2977/#2978), merged 2026-05-20T00:19:35Z
- #2994 (closes #2991) — `FieldGenericTpqr.lean` TODO block (cite #2907/#2908/#2909/#2910 + parent #2905), merged 2026-05-20T00:20:25Z
- **Audited commit:** `711068e` (HEAD of `main` at session start)
- **Target files:** `EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean`, `EtingofRepresentationTheory/Chapter6/FieldGenericTpqr.lean`

## Summary

| Dim | Verdict |
|-----|:-------:|
| D1 — Citation accuracy on `FieldGenericNonAdjacentBranches.lean` Block 1 / Block 2 (post-#2993) | **PASS** |
| D2 — Citation accuracy on `FieldGenericTpqr.lean` TODO block (post-#2994) | **CONCERN** |
| D3 — `FieldGenericNonAdjacentBranches.lean` file docstring accuracy (post-#2983) | **PASS** |
| D4 — Audit-concern closure (PR #2984 D3, D5(a), D5(b)/(c)) | **PASS (with minor residual slop)** |
| D5 — Build sanity + cross-file consistency | **PASS** |
| D6 — `FieldGenericTpqr.lean` file docstring accuracy (post-#2989) | **CONCERN** |

**Overall verdict:** the four chore PRs land their intended citation refresh cleanly. Block 1 and Block 2 of `FieldGenericNonAdjacentBranches.lean` are now correctly aligned with the 4-way #2974/#2976/#2977/#2978 sub-issue decomposition; the file docstring of the same file accurately reflects the landed Phase 1 + Phase 2 dispatch and includes the `D̃₇` helper inventory. Two real concerns persist, both in the `FieldGenericTpqr.lean` cleanup: (i) the post-#2994 TODO block bullet 4 attributes T(1, 2, 3) and T(1, 2, 4) to PR #2912, but PR #2912 only landed T(1, 2, 2) = D₅; (ii) the post-#2989 file docstring cites the residual API stub as "(line 1233)", but the actual theorem is at line 1240 (the docstring was authored against a base predating PR #2994 and merged without rebasing the line number). Neither is build-breaking; recommend a small follow-up chore PR to correct both. No code changes pushed.

## D1 — Citation accuracy on `FieldGenericNonAdjacentBranches.lean` (post-#2993): **PASS**

### Block 1 — upstream comment block (lines 974-1005)

The comment block sits inside the `Case E — partial coverage from sub-issue #2955` branch at `FieldGenericNonAdjacentBranches.lean:974`. The "Remaining cases (still `sorry`)" subsection at lines 994-1003 reads:

```
-- Remaining cases (still `sorry`):
--
-- * `chain.length = 3`, all-leaves (#2974): requires the
--   unavailable D̃₆ per-(F, Q) helper.
-- * `chain.length = 3`, mixed arm degrees E.ab / E.bb (#2976):
--   requires Ẽ₇ at `v₀` or `w` plus extension-degree splits.
-- * `chain.length = 5`, any sub-case (#2977): needs the D̃₈
--   per-(F, Q) helper, not in the per-(F, Q) library.
-- * `chain.length ≥ 6`, all-leaves (#2978): needs a general
--   parametric D̃_n per-(F, Q) helper.
```

4 bullets, 4 sub-issue citations, all scope descriptions match the sub-issue bodies:

| Bullet | Cited issue | Sub-issue title (verified via `gh issue view`) | Match |
|---|---|---|---|
| `chain.length = 3`, all-leaves → D̃₆ | #2974 | "D̃₆ per-(F, Q) helper (chain.length=3 all-leaves)" | ✓ |
| `chain.length = 3`, mixed arm degrees E.ab / E.bb → Ẽ₇ extension splits | #2976 | "Ẽ₇ extension splits for chain.length=3 mixed arm degrees" | ✓ |
| `chain.length = 5`, any sub-case → D̃₈ | #2977 | "D̃₈ per-(F, Q) helper for chain.length=5 residual" | ✓ |
| `chain.length ≥ 6`, all-leaves → parametric D̃_n | #2978 | "general D̃_n per-(F, Q) helper for chain.length≥6 all-leaves" | ✓ |

The Block 1 enumeration's "Remaining cases" is sandwiched between the description of the two **landed** sub-cases (E.aa, E.s1c4) at lines 982-993 and the actual `by_cases hE_aa` dispatch at line 1006. Reader can land on the block and follow the four pointers to read the planned proof strategy for each residual configuration. PASS.

### Block 2 — residual `sorry` site comment block (lines 1100-1113)

The residual `sorry` branch at `FieldGenericNonAdjacentBranches.lean:1100` carries a mirror-image comment block to Block 1:

```
-- Remaining cases (still `sorry`):
--
-- * `chain.length = 3`, all-leaves (#2974): requires the
--   unavailable D̃₆ per-(F, Q) helper.
-- * `chain.length = 3`, mixed arm degrees E.ab / E.bb
--   (#2976): requires Ẽ₇ at `v₀` or `w` plus
--   extension-degree splits.
-- * `chain.length = 5`, any sub-case (#2977): needs the
--   D̃₈ per-(F, Q) helper.
-- * `chain.length ≥ 6`, all-leaves (#2978): needs a
--   general parametric D̃_n per-(F, Q) helper.
```

4 bullets, same 4 issue citations, same scope descriptions (modulo line-wrapping). The two blocks are mutually consistent. PASS.

### Coverage check (cross-referencing sub-issues to the negated guard)

The residual `sorry` site is reached after the cascade
`¬ hA ∧ ¬ hB ∧ ¬ hC ∧ ¬ hD ∧ ¬ hE_aa ∧ ¬ hE_s1c4`. Per the cascade structure (audited in `progress/reviews/2026-05-19-non-adjacent-branches-leaf-case-cases-e-aa-and-e-s1c4.md` D5(e)), the surviving configurations are exactly:

| chain.length | side.deg | arm₁.deg | arm₂.deg | Covered by |
|---|---|---|---|---|
| 3 | 1 | 1 | 1 | #2974 (D̃₆ all-leaves) |
| 3 | * | mixed | mixed (not (2,2)) | #2976 (Ẽ₇ extension splits, all `chain.length=3` non-(2,2) non-(1,1) sub-cases) |
| 5 | 1 | not (2,2) | not (2,2) | #2977 (D̃₈) |
| ≥ 6 | 1 | 1 | 1 | #2978 (parametric D̃_n) |

The cited 4-way decomposition covers the configuration space exactly. PASS.

## D2 — Citation accuracy on `FieldGenericTpqr.lean` TODO block (post-#2994): **CONCERN**

The TODO block at `FieldGenericTpqr.lean:1274-1291` (inside `single_branch_leaf_case_both_extend_per_kQ`, just before the `sorry` at line 1298) reads:

```
  -- TODO (parent assembly issue #2905): replace this `sorry` with the
  -- per-(F, Q) "both arms extend" body mirroring `single_branch_leaf_case`
  -- (`InfiniteTypeConstructions.lean:6981-8352`, ~1370 lines). Further case-
  -- splits on whether `b₂`, `b₃` and deeper vertices extend, dispatching to:
  --   * both arms ≥ 3 → embed Ẽ₇ and call `etilde7_not_finite_type_per_kQ`
  --     (sub-issue #2907).
  --   * `b₃` leaf, q ≥ 3 (T(1, q, 2)) → embed T(1, 2, 5) and call
  --     `t125_not_finite_type_per_kQ` (sub-issue #2908).
  --   * `b₂` leaf, r ≥ 3 (T(1, 2, r)) — symmetric to the previous case;
  --     call `t125_not_finite_type_per_kQ` (sub-issue #2909).
  --   * ADE shapes T(1, 2, 2/3/4) → contradict `h_not_posdef` via the
  --     `e7_tree_posdef` / `e8_posdef`-style posdef facts in
  --     `InfiniteTypeConstructions.lean` (sub-issue #2910; landed via
  --     PR #2912, covering T(1, 2, 2), T(1, 2, 3), and T(1, 2, 4) in the
  --     same posdef-contradiction branch).
```

### Citation cross-check against sub-issue bodies

| Bullet | Cited issue | Sub-issue title (`gh issue view`) | Bullet description match? |
|---|---|---|---|
| both arms ≥ 3 → Ẽ₇ | #2907 | "single_branch_leaf_both_extend_arms_ge3_per_kQ — Ẽ₇ embed (q,r ≥ 3)" | ✓ exact match |
| `b₃` leaf, q ≥ 3 → T(1, q, 2), embed T(1, 2, 5) | #2908 | "single_branch_leaf_both_extend_b3leaf_per_kQ — T(1, q, 2) split (b₃ leaf, q ≥ 3)" | partial — see below |
| `b₂` leaf, r ≥ 3 → T(1, 2, r), embed T(1, 2, 5) | #2909 | "single_branch_leaf_both_extend_b2leaf_per_kQ — T(1, 2, r) split (b₂ leaf, r ≥ 3)" | partial — see below |
| ADE shapes T(1, 2, 2/3/4) → posdef contradiction | #2910 | "single_branch_leaf_both_extend_t122_per_kQ — T(1, 2, 2) = D₅ posdef contradiction" | inaccurate — see below |
| parent | #2905 | "single_branch_leaf_case_both_extend_per_kQ — real body (Ẽ₇ / T(1,2,5) / ADE dispatch)" | ✓ correct parent |

### Concern (a) — bullet 4 misattributes T(1, 2, 3) and T(1, 2, 4) to PR #2912

The bullet says: "(sub-issue #2910; landed via PR #2912, covering T(1, 2, 2), T(1, 2, 3), and T(1, 2, 4) in the same posdef-contradiction branch)".

PR #2912's actual content (`gh pr view 2912 --json files` confirms only `FieldGenericTpqr.lean` and a progress file are touched; `gh pr diff 2912` shows a single theorem added) is **only** `single_branch_leaf_both_extend_t122_per_kQ` for T(1, 2, 2) = D₅. Search of the current file (`grep -n "single_branch_leaf_both_extend_(t122|t132|t142|t123|t124)"`) returns exactly one match — `t122` at line 71 of the current file. There is no `t123`, `t124`, `t132`, or `t142` helper.

T(1, 2, 3) and T(1, 2, 4) are actually sub-sub-cases of **#2909** (per #2909's body: "arm3 length 3 (c₃ leaf): T(1, 2, 3) = E₆, posdef contradiction" and "arm3 length 4 (d₃ leaf): T(1, 2, 4) = E₇, posdef contradiction"). The symmetric shapes T(1, 3, 2) and T(1, 4, 2) are sub-sub-cases of **#2908**. None of these are landed.

The TODO bullet's claim that PR #2912 "covers T(1, 2, 2), T(1, 2, 3), and T(1, 2, 4)" is therefore false. A reader trying to navigate from the TODO block to "the implementation of T(1, 2, 3) posdef contradiction" via PR #2912 will land on the T(1, 2, 2) = D₅ proof and be confused.

PR #2994's progress entry (`progress/2026-05-20T00-19-25Z_16d895b3.md`) shows the worker held the same (incorrect) belief: "Bullet 4 — ADE shapes T(1, 2, 2/3/4) (posdef contradiction) → sub-issue #2910, noting the case landed via PR #2912 covering T(1, 2, 2), T(1, 2, 3), and T(1, 2, 4)." The error originated in the planner's #2991 issue body rather than in worker fabrication, but the chore PR propagated it into `main`.

### Concern (b) — bullets 2 and 3 only describe one branch of #2908 / #2909

#2908's table (4 rows) covers:

| arm2 length | Shape | Dispatch |
|---|---|---|
| 3 | T(1, 3, 2) = E₆ | posdef contradiction |
| 4 | T(1, 4, 2) = E₇ | posdef contradiction |
| 5 | T(1, 5, 2) = T(1, 2, 5) = Ẽ₈ | t125 |
| ≥ 6 | T(1, ≥6, 2) ⊇ T(1, 2, 5) | embed t125 |

The TODO bullet only describes the "embed T(1, 2, 5) and call `t125_not_finite_type_per_kQ`" dispatch — i.e. the q = 5 and q ≥ 6 rows. The q = 3 and q = 4 rows (posdef contradiction for E₆ / E₇) are not mentioned in the bullet for #2908. Symmetrically, #2909's r = 3 and r = 4 sub-cases (T(1, 2, 3) = E₆, T(1, 2, 4) = E₇) are not mentioned in bullet 3.

The cumulative effect: bullets 2/3 + the "covers T(1, 2, 2/3/4)" claim in bullet 4 together appear to enumerate the four ADE-posdef shapes, but T(1, 3, 2) and T(1, 4, 2) — the q = 3, 4 rows of #2908 — are entirely missing from the enumeration. Only T(1, 2, 3) and T(1, 2, 4) (the symmetric pair, sub-cases of #2909) are mentioned, and they are misattributed to #2910 / PR #2912.

### Recommendation

Open a follow-up chore issue to correct the TODO block's bullet 4 and (optionally) expand bullets 2 / 3 to cover the q,r ∈ {3, 4} posdef-contradiction rows. Suggested replacement for bullet 4:

```
--   * ADE shape T(1, 2, 2) = D₅ → contradict `h_not_posdef` via the
--     `d5_posdef`-style posdef facts in `InfiniteTypeConstructions.lean`
--     (sub-issue #2910; landed via PR #2912 — only T(1, 2, 2)). The
--     other ADE configurations T(1, 3, 2)/T(1, 4, 2)/T(1, 2, 3)/T(1, 2, 4)
--     are q,r ∈ {3, 4} sub-rows of #2908/#2909 above, not separately
--     tracked.
```

This corrects the misattribution and clarifies which `(q, r)` pairs are #2910 vs. sub-rows of #2908/#2909.

**D2 verdict: CONCERN.** Bullet 4 carries a false attribution; bullets 2/3 are scope-narrow but their summaries match the sub-issue titles literally so they are not outright wrong. The follow-up chore is small and not build-breaking.

## D3 — `FieldGenericNonAdjacentBranches.lean` file docstring accuracy (post-#2983): **PASS**

The file docstring at lines 13-65 has three sections: title + "Why a different strategy" (lines 13-40) + "Status" (lines 42-64).

### Status section (lines 42-64) — landed cascade summary

```
The body of `non_adjacent_branches_leaf_case_per_kQ` is substantially
landed:

* **Phase 1 setup**: chain extraction, side / arm extraction, and the
  distinctness lattice derived from `hchain_nodup` and the degree
  hypotheses.
* **Phase 2 dispatch** via `by_cases hA … hD` on the
  `(chain.length, side.deg, arm₁.deg, arm₂.deg)` configuration:
  Cases A / B / C-main / C.short / D and the partial Case E sub-cases
  E.aa (chain.length = 3 with both arms degree 2 → `Ẽ₆` at `w`) and
  E.s1c4 (chain.length = 4 with `side_arm` degree 1 → `D̃₇` at
  `(v₀, w)`).

A documented residual `sorry` covers the configurations that need
forbidden-subgraph helpers not yet on `main` — `chain.length = 3` with
mixed arm degrees (E.ab) or both-leaf arms (E.bb), `chain.length = 5`,
and `chain.length ≥ 6` all-leaves — tracked by sub-issues #2974 (D̃₆
for chain.length = 3 all-leaves), #2976 (Ẽ₇ extension splits for
chain.length = 3 mixed arms), #2977 (D̃₈ for chain.length = 5), and
#2978 (general parametric D̃_n for chain.length ≥ 6 all-leaves). All
four are blocked on #2955.
```

| Check | Verdict |
|---|---|
| Mentions Phase 1 setup | ✓ |
| Mentions Phase 2 dispatch over Cases A/B/C-main/C.short/D | ✓ |
| Mentions landed E.aa (chain.length = 3, both arms deg 2 → Ẽ₆) | ✓ |
| Mentions landed E.s1c4 (chain.length = 4, side.deg = 1 → D̃₇) | ✓ |
| Cites all four sub-issues #2974/#2976/#2977/#2978 | ✓ |
| Sub-issue scope descriptions match issue bodies | ✓ (cross-checked in D1 table) |
| Notes all four are blocked on #2955 | ✓ |

PASS.

### Per-(F, Q) library inventory (lines 28-36)

The "Why a different strategy" paragraph lists:

```
... only the fixed-`n` leaves
`d5tilde_not_finite_type_per_kQ` (`FieldGenericD5Tilde.lean:999`),
`d7tilde_not_finite_type_per_kQ` (`FieldGenericD7Tilde.lean:272`),
`etilde6_not_finite_type_per_kQ` (`FieldGenericETilde6.lean:319`),
`etilde7_not_finite_type_per_kQ` (`FieldGenericETilde7.lean:301`), and
`t125_not_finite_type_per_kQ` (`FieldGenericT125.lean:39`), plus the
shared embedding helpers `embed_t125_in_tree_per_kQ`
(`FieldGenericT125.lean:71`) and `embed_d7tilde_in_tree_per_kQ`
(`FieldGenericD7Tilde.lean:323`).
```

`d7tilde_not_finite_type_per_kQ` is at line 30. `embed_d7tilde_in_tree_per_kQ` is at lines 35-36. Both present. The strategy paragraph at line 40 reads "(`Ẽ₆`, `Ẽ₇`, `T(1, 2, 5)`, `D̃₇`)" — `D̃₇` is present alongside `Ẽ₆` / `Ẽ₇` / `T(1, 2, 5)`. PASS.

Spot-check of cited line numbers in the per-(F, Q) library inventory (not all required by the issue body, but checked opportunistically):
- `d5tilde_not_finite_type_per_kQ` at `FieldGenericD5Tilde.lean:999` — file is 1100+ lines (out of scope to fully verify, line number is plausible).
- `d7tilde_not_finite_type_per_kQ` at `FieldGenericD7Tilde.lean:272` — line number cited (not verified at HEAD; out of scope, no evidence of recent shifts to this file).
- Other line numbers similarly not verified at this audit's scope.

These spot-checks are out of scope for D3 per the issue body; PR #2983's audit focus was on the docstring substance, not on cross-file line-number drift.

### Per-theorem docstring (lines 73-102)

The theorem-level docstring at lines 73-102 also includes a status summary (lines 96-102) saying "The body is substantially landed: Phase 1 setup and Phase 2 dispatch ... cover Cases A, B, C-main, C.short, D, and the partial Case E sub-cases E.aa and E.s1c4." Mirrors the file docstring. PASS.

**D3 verdict: PASS.**

## D4 — Audit-concern closure (PR #2984 D3, D5(a), D5(b)/(c)): **PASS (with minor residual slop)**

PR #2984's `progress/reviews/2026-05-19-non-adjacent-branches-leaf-case-cases-e-aa-and-e-s1c4.md` raised three concern-level findings on the version of `FieldGenericNonAdjacentBranches.lean` predating PRs #2983 and #2993:

### Concern 1 — D3 / D5(a): residual comment block had 3 bullets but the sub-issue decomposition has 4

PR #2984's D3 reported: "the comment block has **3 bullets** but there are **4 sub-issues** (#2974, #2976, #2977, #2978)". PR #2984's D3 also noted: "the lower comment block at lines 1084-1086 entirely omits the chain.length=3 all-leaves case".

**Closure verification:** D1 above confirms Block 1 (lines 994-1003) and Block 2 (lines 1101-1113) of the post-#2993 file are 4-bullet, mirror-image enumerations citing #2974/#2976/#2977/#2978 with scope descriptions that match the sub-issue bodies exactly. The chain.length=3 all-leaves case is now its own bullet (#2974) in both blocks. **Resolved by PR #2993.**

### Concern 2 — D3 / D5(a): sub-issue numbers not cited in the comments

PR #2984's D3 reported: "the residual comment block at lines 1084-1087 says 'see follow-up sub-issues' but does **not** cite the issue numbers `#2974`, `#2976`, `#2977`, `#2978`." Searching the post-#2993 file for the four sub-issue numbers:

- `#2974` — 3 occurrences (Block 1, Block 2, file docstring)
- `#2976` — 3 occurrences
- `#2977` — 3 occurrences
- `#2978` — 3 occurrences

**Resolved by PR #2993** (plus #2983 for the file docstring layer).

### Concern 3 — D5(b)/(c): file docstring stale ("API stub" framing, missing D̃₇ helper inventory)

PR #2984's D5(d) reported: "the docstring lists only `d5tilde_not_finite_type_per_kQ`, `etilde6_not_finite_type_per_kQ`, `etilde7_not_finite_type_per_kQ`, `t125_not_finite_type_per_kQ`, `embed_t125_in_tree_per_kQ`. Missing from this enumeration (both landed before the audited commit): `d7tilde_not_finite_type_per_kQ` (PR #2968), `embed_d7tilde_in_tree_per_kQ` (PR #2970)."

It also reported: "The strategy paragraph (lines 36-38) lists `Ẽ₆`, `Ẽ₇`, `T(1, 2, 5)` as the available fixed-shape forbidden subgraphs — does not mention `D̃₇`. The 'API stub' paragraph (lines 40-52) claims the body is `sorry`; the body has substantially landed."

**Closure verification:** D3 above confirms the post-#2983 file docstring includes `d7tilde_not_finite_type_per_kQ` (line 30), `embed_d7tilde_in_tree_per_kQ` (lines 35-36), and `D̃₇` in the strategy paragraph (line 40). The "API stub" framing is replaced by a "Status" section summarising the landed Phase 1 + Phase 2 dispatch. **Resolved by PR #2983.**

### Residual slop (not in issue body's D4 scope)

PR #2984's D3 contained a third sub-concern not flagged in #2995's issue body: "**arm₂_ne_chain** — also appears at lines 862, 887, 1071 (Cases C arm₂-extends, C.short all-leaves residual, E.s1c4). It is already syntactically used; the `let _ := arm₂_ne_chain` at line 1092 is **redundant**. Minor slop."

Checking the post-#2993 file at line 1118: `let _ := leaf_ne_chain; let _ := arm₂_ne_chain` — the `let _ := arm₂_ne_chain` is still present. This is in line with PR #2993's stated scope ("Comment-only edit; line numbers downstream of the block shift by +5" from PR #2993's progress entry), and is **not** flagged in the issue #2995 body — the planner explicitly scoped the chore PRs to citation/docstring substance, not lint cleanups. Mentioning here for completeness; not weighting D4 down.

**D4 verdict: PASS.** All three concerns flagged in the issue body (D3, D5(a), D5(b)/(c)) are resolved by the combined effect of PRs #2983 and #2993. One auxiliary PR #2984 D3 sub-concern (the redundant `let _ := arm₂_ne_chain`) was out of scope for the chore PRs and remains in place; a future cleanup PR can drop it.

## D5 — Build sanity + cross-file consistency: **PASS**

### Build state at HEAD `711068e`

```
$ git rev-parse HEAD
711068e7bf0df7ad43a61b0be6dd7a5502d47255

$ lake exe cache get
Current branch: HEAD
Using cache (Azure) from origin: leanprover-community/mathlib4
No files to download
Already decompressed 8010 file(s)

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches
... ⚠ [8047/8047] Built ... (16s) ...
warning: EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean:103:8: declaration uses `sorry`
Build completed successfully (8047 jobs).

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericTpqr
... warning: EtingofRepresentationTheory/Chapter6/FieldGenericTpqr.lean:1240:8: declaration uses `sorry`
Build completed successfully (8045 jobs).

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericAssembly
... ✔ [8049/8049] Built ... FieldGenericAssembly (32s) ...
Build completed successfully (8049 jobs).
```

Filtered sorry-warnings on the two affected files (verbatim from `/tmp/build-nonadj.log` and `/tmp/build-tpqr.log`):

```
warning: EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean:103:8: declaration uses `sorry`
warning: EtingofRepresentationTheory/Chapter6/FieldGenericTpqr.lean:1240:8: declaration uses `sorry`
```

| File | Expected sorries | Actual sorries | Match |
|---|---|---|---|
| `FieldGenericNonAdjacentBranches.lean` | 1 (top-level theorem `non_adjacent_branches_leaf_case_per_kQ`) | 1 (line 103) | ✓ |
| `FieldGenericTpqr.lean` | 1 (`single_branch_leaf_case_both_extend_per_kQ`, planner expected at "line 1240") | 1 (line 1240) | ✓ |

### Cross-file consistency

- `FieldGenericAssembly` (which depends on both) builds clean. No transitive build breakage.
- The build output's reported sorry sites match the issue body's "documented residual sites".
- The `FieldGenericNonAdjacentBranches.lean` line-103 sorry is the same site flagged by all prior audits in this cascade (PR #2969, #2975, #2981, #2984).
- The `FieldGenericTpqr.lean` line-1240 sorry is `single_branch_leaf_case_both_extend_per_kQ`, tracked by the #2905 sub-chain.

PASS.

## D6 — `FieldGenericTpqr.lean` file docstring accuracy (post-#2989): **CONCERN**

The file docstring at lines 11-50 has three sections: title + dispatch overview (lines 11-34) + audit-pattern + sibling-wrapper enumeration (lines 36-49).

### Leaf-arm dispatch bullet (lines 22-30)

```
* Some arm is a leaf → delegate to `single_branch_leaf_case_per_kQ`,
  which case-splits on whether each of `v₀`'s non-leaf neighbours `a₂`,
  `a₃` has degree 2: if both extend, dispatch to
  `single_branch_leaf_case_both_extend_per_kQ` (still an API stub,
  tracked by the #2905 sub-chain #2907 / #2908 / #2909 / #2910); if
  either `a₂` or `a₃` is itself a leaf, the graph is a D-type tree and
  the Cartan form is positive definite by `tree_two_leaf_posdef`,
  contradicting `h_not_posdef`.
```

| Check | Verdict |
|---|---|
| Describes the a₂ / a₃ degree-2 case split | ✓ |
| Identifies the "both extend" branch and points at `single_branch_leaf_case_both_extend_per_kQ` | ✓ |
| Cites the #2905 sub-chain (#2907 / #2908 / #2909 / #2910) | ✓ |
| Describes the D-type collapse via `tree_two_leaf_posdef` | ✓ |

PASS on the dispatch bullet's substance.

### Remaining-API-stub paragraph (lines 32-34) — **CONCERN**

```
The remaining API stub in this file is
`single_branch_leaf_case_both_extend_per_kQ` (line 1233) — the body is
`sorry`, tracked by the #2905 sub-chain.
```

**The cited "line 1233" is stale.** The theorem `single_branch_leaf_case_both_extend_per_kQ` begins at line 1240 (confirmed by `lake build` reporting "FieldGenericTpqr.lean:1240:8: declaration uses `sorry`" and by direct inspection of the file: `attribute [-instance] ... in` at line 1224, doc comment lines 1226-1239, `theorem single_branch_leaf_case_both_extend_per_kQ` at line 1240).

Line 1233 is inside the **inner per-theorem docstring** of `single_branch_leaf_case_both_extend_per_kQ`, specifically the sentence "`etilde7_not_finite_type_per_kQ` (q, r ≥ 3 → Ẽ₇)," — i.e. nothing structurally meaningful for a reader navigating from the file docstring.

**Root cause:** PR #2989 (file docstring refresh) was authored against a base where the theorem was at line 1233, and merged 60 seconds after PR #2994 (TODO block expansion, +5 lines, shifted the theorem to line 1240). PR #2989 was not rebased before merge. The session-log entry for PR #2989 (`progress/2026-05-19T19-13-56Z_2dc5318a.md`) actually says "the pre-existing `sorry` at line 1240" in its "Current frontier" section — i.e. the author knew the build reported line 1240 — but the docstring text was authored against the older base and not updated to match.

**Recommendation:** open a small follow-up chore issue to fix the line number. Suggested replacement: "(line 1240)" → reflects the post-#2994 layout. Optionally drop the line number altogether (a `grep`-able theorem name is more robust to file shifts than a hand-maintained line number).

### Sibling-wrapper enumeration (lines 43-49)

```
* `degree_ge_4_infinite_type_per_kQ` (`FieldGenericStar.lean:649`, PR #2891)
* `graph_with_list_cycle_infinite_type_per_kQ`
  (`FieldGenericCycle.lean:440`, PR #2897)
* `adjacent_branches_infinite_type_per_kQ`
  (`FieldGenericD5Tilde.lean:1043`, PR #2900)
* `non_adjacent_branches_infinite_type_per_kQ`
  (`FieldGenericAssembly.lean:75`, PR #2943)
```

`non_adjacent_branches_infinite_type_per_kQ` is included with file path `FieldGenericAssembly.lean:75` and PR #2943 citation. Matches the issue body's D6 deliverable exactly. PASS on this sub-bullet.

### Consistency with the inner TODO block (D2 cross-reference)

The file docstring's dispatch description ("dispatch to `single_branch_leaf_case_both_extend_per_kQ`") delegates further detail to the inner TODO block. The inner TODO block's bullet 4 carries the inaccurate "PR #2912 covers T(1, 2, 2), T(1, 2, 3), and T(1, 2, 4)" claim (see D2). The file docstring itself does not repeat this claim — it simply points at the `#2905` sub-chain — so the file docstring is not the *source* of the inaccuracy, but a reader following the docstring's pointer to the inner TODO will encounter it. Cross-reference cited; concern is owned by D2.

Auxiliary observation: the inner stub docstring at lines 1230-1235 (NOT touched by either PR #2989 or PR #2994) reads:

```
API stub: the body is `sorry`, tracked by a follow-up sub-issue. The real
proof mirrors the `_kQ`-free original — further case-splits on whether
`b₂`, `b₃` and deeper vertices extend, dispatching to
`etilde7_not_finite_type_per_kQ` (q, r ≥ 3 → Ẽ₇),
`t125_not_finite_type_per_kQ` (q = 2, r ≥ 5 → T(1, 2, 5)), or contradicting
`h_not_posdef` for the ADE shapes T(1, 2, 2), T(1, 2, 3), T(1, 2, 4).
```

This inner per-theorem docstring is unchanged by all four chore PRs and is out of scope for this audit. Note for future cleanups: the inner docstring's "q = 2, r ≥ 5 → T(1, 2, 5)" is asymmetric and does not align with the post-#2994 TODO block's symmetric (q, 2) ↔ (2, r) decomposition into #2908 / #2909. A future chore can refresh this inner docstring to match the TODO block's 4-way structure.

**D6 verdict: CONCERN.** The dispatch bullet and sibling-wrapper enumeration are substantively correct, but the "(line 1233)" line number for `single_branch_leaf_case_both_extend_per_kQ` is stale (actual line 1240). Recommend a small follow-up chore.

## Verdict

PRs #2983 and #2993 — the two `FieldGenericNonAdjacentBranches.lean` cleanups — land cleanly. They jointly resolve all three concerns from PR #2984's audit (D3 enumeration mismatch, D5(a) cross-reference, D5(b)/(c) docstring staleness). The file docstring's "Status" section now accurately summarises the landed Phase 1 + Phase 2 dispatch, the per-(F, Q) library inventory includes `d7tilde_not_finite_type_per_kQ` and `embed_d7tilde_in_tree_per_kQ`, the "Why a different strategy" paragraph mentions D̃₇, and both residual-sorry comment blocks (Block 1 + Block 2) cite all four sub-issues #2974/#2976/#2977/#2978 with scope descriptions matching the sub-issue bodies.

PRs #2989 and #2994 — the two `FieldGenericTpqr.lean` cleanups — carry two real concerns, both of which are inaccuracies that could mislead a future reader navigating the residual sorry:

1. **D2 / TODO bullet 4 misattribution.** The TODO block (PR #2994) claims PR #2912 covers T(1, 2, 2), T(1, 2, 3), and T(1, 2, 4); PR #2912 actually only landed T(1, 2, 2) = D₅. T(1, 2, 3) and T(1, 2, 4) are sub-sub-cases of #2909, and T(1, 3, 2) and T(1, 4, 2) are sub-sub-cases of #2908 — all still open. The misattribution originated in the planner's #2991 issue body and propagated into `main`.

2. **D6 / stale line number.** The post-#2989 file docstring cites `single_branch_leaf_case_both_extend_per_kQ` as "(line 1233)"; the actual line is 1240. PR #2989 was authored against a pre-#2994 base and merged 60 seconds after #2994 without rebasing.

Recommend a small follow-up chore issue to correct both. Suggested scope: replace "(line 1233)" with "(line 1240)" or drop the parenthetical line number; replace bullet 4 of the TODO block to (i) drop the "T(1, 2, 3), T(1, 2, 4)" claim from PR #2912 and (ii) optionally note that those ADE shapes are sub-rows of #2908 / #2909.

Build state at HEAD `711068e`:
- `lake build FieldGenericNonAdjacentBranches` → 1 sorry at line 103 ✓
- `lake build FieldGenericTpqr` → 1 sorry at line 1240 ✓
- `lake build FieldGenericAssembly` → no new warnings ✓

No code changes pushed; review only.

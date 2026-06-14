# Review: PR #2943 — `non_adjacent_branches_infinite_type_per_kQ` outer assembly

**Verdict: FAIL on D3 (build-breaking call-site stale-arg).** Fix
landed in the same PR (5 lines added to derive the new hypothesis,
3 call sites updated). All other dimensions PASS.

- PR audited: #2943 (merge commit `49f34bc`, merged
  2026-05-19T00:08Z)
- Follow-up PR #2941 (merge commit `6fc9d40`, merged 2026-05-19T00:11Z)
  strengthened the dispatch helper's signature **3 minutes after**
  #2943 landed, without updating the call sites added by #2943.
- Issue: #2944 (this audit)
- Session: `0aec819e`

## Summary of defect

PR #2943 added three dispatches to `non_adjacent_branches_leaf_case_per_kQ`
at `FieldGenericAssembly.lean:151-158`. The dispatch arguments matched
the helper's signature **as it existed at the moment #2943 was reviewed**.

Three minutes later, PR #2941 strengthened the helper by inserting a new
hypothesis between two existing ones:

```
-- before #2941
… (h_no_adj_branch : …) (leaf : Fin n) …

-- after #2941
… (h_no_adj_branch : …)
  (h_no_adj_branch_w : ∀ u, adj w u = 1 → vertexDegree adj u < 3)
  (h_v₀w_nonadj : adj v₀ w ≠ 1)
  (leaf : Fin n) …
```

(The pre-strengthening signature also lacked `h_v₀w_nonadj` as a
hypothesis; that was already added by #2941 as well.)

#2941's diff (`6fc9d40`) touched only
`FieldGenericNonAdjacentBranches.lean`, `FieldGenericETilde{6,7}.lean`,
and a progress entry. It did **not** touch
`FieldGenericAssembly.lean`, leaving the three call sites positional-
arg-aligned against the **old** signature. Result: the first
argument-by-position after `h_no_adj_branch` is `h_v₀w_nonadj`, which
Lean then tries to elaborate as the new `h_no_adj_branch_w` slot:

```
error: EtingofRepresentationTheory/Chapter6/FieldGenericAssembly.lean:152:46:
  Application type mismatch: The argument
    h_v₀w_nonadj
  has type
    adj v₀ w ≠ 1
  but is expected to have type
    ∀ (u : Fin n), adj w u = 1 → vertexDegree adj u < 3
  in the application
    non_adjacent_branches_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn
      h_acyclic h_deg v₀ w hv₀ hw hne h_no_adj_branch h_v₀w_nonadj
```

…repeated at lines 155 and 158. `main` at commit `7dcc9f3` does not
build the audited file. (The audit issue body's claim that "PR #2943
was merged with passing CI" is correct for the moment of #2943's
merge; the breakage was introduced by the subsequent #2941 merge
without a coupled call-site bump. No CI run between #2941 and
the present has built this file successfully on `main` — most likely
the cascade of intermediate PRs (#2945, #2947, #2952, #2956, #2958)
each rebuilt only their own files. PR #2952's commit message says
"Phase 1 setup for non_adjacent_branches_leaf_case_per_kQ" but did
not detect the upstream caller stale-arg.)

## Fix (landed in this PR)

`FieldGenericAssembly.lean:150-160` now derives `h_no_adj_branch_w`
inline from the negated existential `h_adj_exists` (after `push_neg`
applied at line 106), in the same pattern used to derive `h_no_adj`
in `acyclic_branch_not_posdef_infinite_type_per_kQ`
(`FieldGenericAssembly.lean:424-428`):

```lean
have h_no_adj_branch_w : ∀ u, adj w u = 1 → vertexDegree adj u < 3 := by
  intro u hu
  have := h_adj_exists w u hu hw
  have := h_deg u
  omega
```

The post-`push_neg` shape of `h_adj_exists` is
`∀ x y, adj x y = 1 → vertexDegree adj x = 3 → vertexDegree adj y ≠ 3`
(curried implication chain, not a disjunction — verified empirically
against the elaboration error from a first-draft `rcases` derivation
that assumed the disjunctive shape). Each of the three call sites is
updated to pass `h_no_adj_branch_w` as the 15th positional arg.

`lake build EtingofRepresentationTheory.Chapter6.FieldGenericAssembly`
now succeeds (no errors, expected pre-existing transitive sorry
warnings for `FieldGenericD5Tilde.lean:798,974`,
`FieldGenericTpqr.lean:1233`, and `FieldGenericNonAdjacentBranches.lean:87`).

A doc-comment update at `FieldGenericAssembly.lean:42-44` removes the
stale "(this file, sorry-bodied; tracked by #2919)" footnote — the
body of `non_adjacent_branches_infinite_type_per_kQ` is no longer a
sorry as of #2943; the residual sorry lives in
`FieldGenericNonAdjacentBranches.lean` and is tracked by #2939.

## D1 — Signature fidelity (PASS)

`non_adjacent_branches_infinite_type_per_kQ`
(`FieldGenericAssembly.lean:74-99`) mirrors
`non_adjacent_branches_infinite_type`
(`InfiniteTypeConstructions.lean:9682-9699`) on every shared parameter:
`{n}` (implicit), `adj`, `hn`, `hsymm`, `hdiag`, `h01`, `hconn`,
`h_acyclic`, `h_deg`, `v₀ w`, `hv₀`, `hw`, `hne`, `h_no_adj_branch`.
All hypothesis types are byte-identical.

The per-(F, Q) tail `(F : Type) [Field F] [IsAlgClosed F] (Q :
@Quiver.{0, 0} (Fin n)) [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q
a b)] (hOrient : @Etingof.IsOrientationOf n Q adj)` matches the shape
on every sibling per-(F, Q) leaf in the file: see
`adjacent_branches_infinite_type_per_kQ`
(`FieldGenericD5Tilde.lean:1055-1058`),
`non_adjacent_branches_leaf_case_per_kQ`
(`FieldGenericNonAdjacentBranches.lean:109-112`),
`acyclic_branch_not_posdef_infinite_type_per_kQ`
(`FieldGenericAssembly.lean:407-410`),
and `not_posdef_infinite_type_per_kQ`
(`FieldGenericAssembly.lean:464-467`) — all five lines line up.

Conclusion `¬ Set.Finite {d : Fin n → ℕ | ∃ V :
@Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))}`
matches the canonical per-(F, Q) infinite-type predicate exactly.

`[IsAlgClosed F]` is carried because the all-deg-2 case transitively
dispatches into `etilde6_not_finite_type_per_kQ`, which requires it
via the `field-generic` chain.

## D2 — Case-tree fidelity (PASS)

| Per-(F, Q) line | Branch | Universal line |
|---|---|---|
| 100-104 | (a) adjacent-pair fallback → `adjacent_branches_infinite_type_per_kQ` | 9700-9703 |
| 105-149 | setup: `S₀` extraction, `u₁/u₂/u₃` extraction, `h_v₀w_nonadj`, `h_no_adj_branch_w` (this PR's fix) | 9704-9776 |
| 161-163 | (b) `u₁` leaf → `non_adjacent_branches_leaf_case_per_kQ` | 10317-10319 |
| 164-166 | (c) `u₂` leaf → `non_adjacent_branches_leaf_case_per_kQ` | 10320-10321 |
| 167-169 | (d) `u₃` leaf → `non_adjacent_branches_leaf_case_per_kQ` | 10322-10323 |
| 170-384 | (e) all-deg-2 → embed Ẽ₆ via `subgraph_infinite_type_transfer_per_kQ` + `etilde6_not_finite_type_per_kQ` | 10324-10597 |

Five branches, same order, no fusion or splitting. The per-(F, Q)
version **does** refactor the universal `leaf_case` `have`-block
(universal lines 9770-10316, ~547 lines) out of line and into the
external helper `non_adjacent_branches_leaf_case_per_kQ` (stubbed by
#2933, body in flight as #2939). This is a deliberate per-(F, Q)
strategy change documented in the helper's file docstring
(`FieldGenericNonAdjacentBranches.lean:21-37`) — the universal
`leaf_case` embeds `D̃_{k+5}` parameterised in chain length, but the
per-(F, Q) library has no `dTilde_not_finite_type_per_kQ` for general
`n` and must dispatch into fixed-shape `Ẽ₆`, `Ẽ₇`, or `T(1, 2, 5)`
instead. This refactor is *not* a case-tree divergence — branches
(b)/(c)/(d) still call the same logical helper at the same point in
the case tree.

## D3 — Inner-dispatch correctness (PASS with fix; was FAIL pre-fix)

### (a) Adjacent-pair fallback (PASS)

Call at `FieldGenericAssembly.lean:103-104`:
```lean
exact adjacent_branches_infinite_type_per_kQ adj hsymm hdiag h01 h_acyclic
  x y hx hy hxy F Q hOrient
```
Sibling signature (`FieldGenericD5Tilde.lean:1043-1062`):
`adj hsymm hdiag h01 h_acyclic v₀ w hv₀_deg hw_deg hvw_adj F [Field] [IsAlgClosed] Q [Sub] hOrient`.
Arguments line up — `(x, y, hx, hy, hxy)` slot into
`(v₀, w, hv₀_deg, hw_deg, hvw_adj)`. ✓

### (b)/(c)/(d) Leaf-case dispatches (PASS post-fix)

Each of the three dispatches at lines 161-163, 164-166, 167-169
(post-fix) calls
```lean
non_adjacent_branches_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic
  h_deg v₀ w hv₀ hw hne h_no_adj_branch h_no_adj_branch_w h_v₀w_nonadj
  uᵢ huᵢ_adj huᵢ_leaf F Q hOrient
```
matching the strengthened signature
(`FieldGenericNonAdjacentBranches.lean:87-116`)
arg-for-arg. **Pre-fix this was the FAIL** — the call passed
`h_v₀w_nonadj` in the `h_no_adj_branch_w` position.

### (e) All-deg-2 → Ẽ₆ embedding (PASS)

Closing dispatch at `FieldGenericAssembly.lean:370-372`:
```lean
exact subgraph_infinite_type_transfer_per_kQ φ F Q
  (etilde6_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
    (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))
```

The shape matches the per-(F, Q) recipe used elsewhere
(see `embed_t125_in_tree_per_kQ` at `FieldGenericT125.lean:434-436`,
which audited PASS in `2026-05-19-embed-t125-in-tree-per-kQ.md`).
Signatures verified:
- `subgraph_infinite_type_transfer_per_kQ`
  (`FieldGenericInfiniteType.lean:374`) takes `(φ : Fin m ↪ Fin n)
  (F) (Q)` then the per-Q witness on the sub-graph.
- `etilde6_not_finite_type_per_kQ`
  (`FieldGenericETilde6.lean:319`) takes `(F) (Q : @Quiver (Fin 7))
  [Sub] (hOrient_sub)`.
- `restrictOrientationViaEmb_isOrientationOf`
  (`FieldGenericInfiniteType.lean:345`) closes the orientation
  carriage with the `hembed : ∀ i j, adj_sub i j = adj (φ i) (φ j)`
  bridge.

The embedding `φ_fun : Fin 7 → Fin n` at lines 347-350 maps
`0→v₀, 1→u₁, 2→u₁', 3→u₂, 4→u₂', 5→u₃, 6→u₃'`, matching the
T(2,2,2) shape of `etilde6Adj`
(`InfiniteTypeConstructions.lean:1246-1250` — edges 0-1, 1-2, 0-3,
3-4, 0-5, 5-6 in both directions). Verbatim identical to the
universal version (lines 10572-10575).

The `hembed` proof at lines 356-369 uses the same
`fin_cases <;> simp <;> norm_num <;> linarith` shape with a
30-fact `adj_comm` / `hdiag` curated list — byte-identical to the
universal version (lines 10582-10595) up to the let-binding name.

## D4 — Sorry-propagation accounting (PASS with delta)

Pre-this-PR sorry count in `FieldGenericAssembly.lean`: **0** proof-body
sorries (PR #2943 already closed the lone proof-body sorry; the only
remaining `sorry` references in the file before this PR were two
doc-comment strings at lines 42 and 62).

After this PR: still **0** proof-body sorries. The doc-comment
update at lines 42-44 removes one of the two stale `sorry`
references in doc text (the one at line 62 is in the docstring of
`acyclic_branch_not_posdef_infinite_type_per_kQ` and refers to a
correctly-described transitive sorry in
`non_adjacent_branches_leaf_case_per_kQ` — kept as-is).

Sorry-count delta on this PR: **0** (proof-body) / **−1** (doc-comment
references to the now-filled body).

Transitive sorry trace from `non_adjacent_branches_infinite_type_per_kQ`:
- branches (b)/(c)/(d) → `non_adjacent_branches_leaf_case_per_kQ`
  (`FieldGenericNonAdjacentBranches.lean:87`, body still sorry'd;
  partial Phase 1/2 progress via #2952/#2956/#2958, tracked by
  #2939 and Case C/D/E sub-issues from the planner cycle that
  decomposed #2939).
- branch (e) → `etilde6_not_finite_type_per_kQ`
  (`FieldGenericETilde6.lean:319`), still sorry'd in body.

No new sorry surface introduced.

## D5 — Light pattern audit (PASS)

- `set_option maxHeartbeats 6400000 in` at line 51 matches universal
  `InfiniteTypeConstructions.lean:9674`. ✓
- `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in` prefix at line 57-58 applied
  per the per-(F, Q) recipe (D2.degree4 audit catalog,
  `2026-05-18-degree4-per-kQ-placement.md`). ✓
- Variable naming `S₀ / Sw / Su₁ / Su₂ / Su₃`, `u₁ / u₂ / u₃ / u₁' /
  u₂' / u₃'`, `arm₁ / arm₂`, `side_arm`, `chain`: identical to
  universal. ✓
- `path_nodup4 / path_edges4 / path_nodup5 / path_edges5` helpers:
  identical body and naming. ✓
- `acyclic_no_triangle` / `acyclic_path_nonadj` usage shape: identical
  argument order, identical pivot vertex naming. ✓
- One pattern-level *improvement* over the universal version: the
  per-(F, Q) version derives `h_v₀w_nonadj` and (this PR) the new
  `h_no_adj_branch_w` *outside* the `leaf_case` helper, before the
  three leaf-case dispatches. The universal version derives
  `h_v₀w_nonadj` *inside* the `have leaf_case` block (universal
  9773-9776), causing it to be re-derived three times. Per-(F, Q)
  hoists it once; this is a strict win on duplicated work and is
  consistent with the refactor that lifted `leaf_case` to an external
  helper.

No non-trivial divergence flagged.

## Builds

- `lake exe cache get` — no files to download (Mathlib already cached).
- `lake build EtingofRepresentationTheory.Chapter6.FieldGenericAssembly`
  pre-fix: **FAIL** (3 application-type errors at lines 152, 155, 158).
- `lake build EtingofRepresentationTheory.Chapter6.FieldGenericAssembly`
  post-fix: **PASS** (8048/8048 jobs, only pre-existing transitive
  sorry warnings).

## Why fix landed here rather than as a follow-up issue

`main` was build-broken at commit `7dcc9f3` for the audited file. The
audit issue's verification step requires `lake build … succeeds`,
which is impossible without the fix. Filing a follow-up issue would
have left `main` red for at least another planner+worker cycle
(~10-30 min) while every parallel agent's session would have hit the
same build failure when touching anything that imports
`FieldGenericAssembly.lean` — at the very least every downstream
session on `Chapter6.FieldGenericAssembly`'s reverse dependencies,
plus any Chapter 2 work touching `Theorem2_1_2.lean`.

The fix itself is 5 lines (one `have` block) plus 3 call-site arg
additions (one identifier per call). It is mechanical given the
strengthened signature: `h_no_adj_branch_w` is derivable from the
hypotheses already in scope by the same `omega` pattern the file
already uses to derive `h_no_adj` at line 424. No mathematical
content is added.

This audit is therefore a **mixed audit-and-repair** PR. The audit
verdict (FAIL on D3, with fix) is recorded above.

## Follow-ups

No new issues opened. The fix is complete, the build is green, and
the dispatch chain is structurally correct.

Recommendation for future planner cycles: when a planner creates a
"strengthen signature X" issue (#2932 in this case), it should also
either (a) include the caller-update in the same issue's deliverables,
or (b) create a paired caller-update issue immediately and link the
two. The two-PR-three-minutes-apart race that broke `main` here was
avoidable in planning.

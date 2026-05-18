## Current state

Sub-deliverable D2.single of #2877 (per-(F, Q) `not_posdef_infinite_type_per_kQ` assembly + Theorem 2.1.2 bridge). Three D2 sub-deliverables have landed (D2.degree4 PR #2891, D2.cycle PR #2897, D2.adjacent PR #2900). The audit verdict from PR #2894 (`progress/reviews/2026-05-18-degree4-per-kQ-placement.md`) documents the per-(F, Q) wrapper recipe and recommends D2.single as the next natural sub-deliverable to dispatch among the three remaining (D2.single, D2.nonadj, D2.outer + D3).

### Target

`single_branch_not_posdef_infinite_type_per_kQ` — the per-(F, Q) version of `single_branch_not_posdef_infinite_type` (`EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean:8401-8706`, ~305 lines body). Handles the case where a connected acyclic non-positive-definite graph with all degrees ≤ 3 has exactly one degree-3 vertex (a T(p,q,r) graph), dispatching to Ẽ₆ / Ẽ₇ / T(1,2,5) leaves depending on arm geometry.

### Internal structure of the `_kQ`-free original (8401-8706)

The body has two top-level branches:

1. **All three arms length ≥ 2** (lines 8458-8672, ~215 lines): builds a `Fin 6 ↪ Fin n` embedding of Ẽ₆ on `v₀, a₁, a₂, a₃, b₁, b₂, b₃` (the branch vertex, its three neighbours, and one further neighbour of each), then dispatches to `etilde6_not_finite_type` via `subgraph_infinite_type_transfer φ adj etilde6Adj hsymm ... hembed etilde6_not_finite_type` (line 8671).
2. **At least one neighbour of v₀ is a leaf** (lines 8673-8699, three branches): each delegates to the private helper `single_branch_leaf_case` (defined at `InfiniteTypeConstructions.lean:6901-8400`, ~1500 lines). That helper internally dispatches to Ẽ₆ / Ẽ₇ / T(1,2,5) depending on T(1,q,r) shape.

### Dependency leaves on `main`

| Leaf | Status |
|---|---|
| `etilde6_not_finite_type_per_kQ` (`FieldGenericETilde6.lean:319`) | LIVE (Wall-1 sorry inside) |
| `etilde7_not_finite_type_per_kQ` (`FieldGenericETilde7.lean:301`) | LIVE (Wall-1 sorry inside) |
| `t125_not_finite_type_per_kQ` (`FieldGenericT125.lean:39`) | LIVE (stub, sorry'd body — tracked by #2793) |
| `subgraph_infinite_type_transfer_per_kQ` (`FieldGenericInfiniteType.lean:374`) | LIVE |
| `restrictOrientationViaEmb_isOrientationOf` (`FieldGenericInfiniteType.lean:345`) | LIVE |

All per-(F, Q) leaves the worker needs to dispatch to exist on `main`. The two stubs (`etilde6` / `etilde7` carry Wall-1 sorries, `t125` is a fresh stub from #2875 D1) propagate through the per-(F, Q) chain per spec-driven development — they are not blockers for filing this issue.

## Deliverables

### D1. `single_branch_not_posdef_infinite_type_per_kQ` outer body

Mirror the structure of `single_branch_not_posdef_infinite_type` (`InfiniteTypeConstructions.lean:8401-8706`):

- **Signature**: append the canonical per-(F, Q) suffix per the audit recipe (`progress/reviews/2026-05-18-degree4-per-kQ-placement.md` §"Pattern recipe"):
  - `(F : Type) [Field F] [IsAlgClosed F]` (required — the Ẽ₆ / Ẽ₇ / T(1,2,5) leaves all carry it)
  - `(Q : @Quiver.{0,0} (Fin n))`
  - `[∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]`
  - `(hOrient : @Etingof.IsOrientationOf n Q adj)`
  - Conclusion: `¬ Set.Finite { d : Fin n → ℕ | ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q, V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F)) }`
- **Body**: copy the `_kQ`-free body verbatim, then:
  - In the all-arms-length-≥-2 branch, replace the final `subgraph_infinite_type_transfer φ adj etilde6Adj hsymm ... hembed etilde6_not_finite_type` (line 8671) with `subgraph_infinite_type_transfer_per_kQ φ F Q (etilde6_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q) (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))` — pattern from `adjacent_branches_infinite_type_per_kQ` (`FieldGenericD5Tilde.lean:1043`).
  - In the three leaf-case dispatches, call the helper `single_branch_leaf_case_per_kQ` introduced in D2.
- **Attribute prefix**: `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver CategoryTheory.ReflQuiver.toQuiver in` per recipe step 4.
- **`maxHeartbeats`**: carry through the same `set_option maxHeartbeats N in` value as the `_kQ`-free original if present, with a reason comment.

### D2. `single_branch_leaf_case_per_kQ` API stub

Introduce a `theorem single_branch_leaf_case_per_kQ` mirroring the signature of `single_branch_leaf_case` (`InfiniteTypeConstructions.lean:6901-8400`, ~1500 lines body) with the same per-(F, Q) suffix. Body is `by sorry` — this stub lets D1 dispatch by name. The real proof of D2 is out of scope for this issue and will be filed as a follow-up sub-issue (likely decomposed further by T(1,q,r) shape, since the leaf case internally splits into Ẽ₆ / Ẽ₇ / T(1,2,5) sub-dispatches).

Place the stub immediately before `single_branch_not_posdef_infinite_type_per_kQ` in the chosen host file. Add a short docstring noting the body is a stub tracked by a follow-up sub-issue (the worker should file that issue when creating the PR).

### Placement

Per the audit's recipe step 3 ("pick the existing file with the largest overlap of already-imported dispatch leaves; create a new file only if the wrapper crosses the ~300-line threshold or is the assembly point for multiple wrappers"):

- **Preferred**: a new file `EtingofRepresentationTheory/Chapter6/FieldGenericTpqr.lean` importing `FieldGenericInfiniteType`, `FieldGenericETilde6`, `FieldGenericETilde7`, `FieldGenericT125`. D1's body is ~305 lines; together with D2's stub it would push `FieldGenericETilde7.lean` (currently 327 lines) over the ~500-line soft cap. The audit recipe explicitly cites D2.single as the case that justifies `FieldGenericTpqr.lean`.
- **Alternative**: cross-import `FieldGenericT125` into `FieldGenericETilde7.lean` and place both deliverables there. Acceptable if the worker prefers it, but the audit's preference is the new file.

Worker may deviate with justification per the recipe.

## Verification

- `lake build EtingofRepresentationTheory.Chapter6.<new-host-file>` passes (no new warnings/errors on the new theorems).
- `lake build EtingofRepresentationTheory.Chapter6` passes (no downstream regressions).
- D1's body contains no `sorry` (only the inherited sorries from the dispatch leaves `etilde6_not_finite_type_per_kQ` / `etilde7_not_finite_type_per_kQ` / `t125_not_finite_type_per_kQ` / `single_branch_leaf_case_per_kQ` propagate).
- D2's body is exactly `by sorry` — the stub carries a docstring noting it is a sub-deliverable awaiting its own follow-up issue.
- Net sorry-count delta on `main`: **+1** (D2's stub contributes one new sorry; D1 closes no existing sorry). This is expected and matches the #2875 D1 stub introduction pattern.

## Context

- Parent: #2877 (umbrella D2 + D3 for #2875).
- Audit-pattern recipe: `progress/reviews/2026-05-18-degree4-per-kQ-placement.md`, §"Pattern recipe" + §"Recommended placement for each remaining D2 sub-deliverable" (the D2.single row).
- Sibling pre-splits already landed:
  - D2.degree4 → `degree_ge_4_infinite_type_per_kQ` (`FieldGenericStar.lean:649`, PR #2891).
  - D2.cycle → `graph_with_list_cycle_infinite_type_per_kQ` (`FieldGenericCycle.lean:440`, PR #2897).
  - D2.adjacent → `adjacent_branches_infinite_type_per_kQ` (`FieldGenericD5Tilde.lean:1043`, PR #2900).
- Remaining D2 sub-deliverables after this lands: D2.nonadj (~900 lines, needs its own audit pass per #2877's body), D2.outer + D3 (~150 lines, assembles into Theorem 2.1.2).
- Inherited sorry chains transitively blocking the real proof of D2's stub: Wall 1 (#2436), T(1,2,5) D1 stub (#2793). None block filing this issue.

## Notes for the worker

- The all-arms-length-≥-2 branch (~215 lines) is the structurally heaviest part; budget session capacity accordingly. The three leaf-case dispatches are one line each in the `_kQ`-free version and remain one line each (calling the D2 stub).
- D2's stub should be filed as a follow-up sub-issue immediately on PR creation, with `replan` label so the planner triages it next cycle.
- If session capacity is tight, the worker may split this issue into two: D1 alone, then D2 as a separate stub-introduction PR. Either ordering is fine — D1's body just needs D2's stub name to exist at the call site (a `axiom`-style declaration without body, or a one-line `theorem ... := by sorry` placed first, both work).
- If the worker chooses the new-file path, add `EtingofRepresentationTheory/Chapter6/FieldGenericTpqr.lean` to whatever module manifest the project uses (check `lakefile.lean` and any `EtingofRepresentationTheory.lean` aggregator).

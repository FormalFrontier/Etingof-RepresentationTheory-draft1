# Review: PR #2891 — `degree_ge_4_infinite_type_per_kQ` placement + `[IsAlgClosed F]` pattern

**Verdict: PASS** on deliverables 1 + 2. Pattern-decision notes for
downstream D2 sub-PRs in deliverable 3.

- PR: #2891 (commit `354a3c3`, merged into `733bd0d` on `main`)
- Issue: #2892 (this audit)
- Parent feature: #2889 (closed by #2891); umbrella #2877
- Session: `794b5739`

## D1 — Statement fidelity (PASS)

`degree_ge_4_infinite_type_per_kQ`
(`Chapter6/FieldGenericStar.lean:649-662`) mirrors the `_kQ`-free
original `degree_ge_4_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:4064-4068`) at the statement
level. Diff:

| Aspect | `_kQ`-free | `_per_kQ` |
|---|---|---|
| `adj, hsymm, hdiag, h01, v, hv` | identical | identical |
| field args | — | `(F : Type) [Field F] [IsAlgClosed F]` appended |
| quiver args | — | `(Q : @Quiver.{0,0} (Fin n)) [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]` appended |
| orientation arg | — | `(hOrient : @Etingof.IsOrientationOf n Q adj)` appended |
| conclusion | `¬ IsFiniteTypeQuiver n adj` | `¬ Set.Finite {d \| ∃ V, V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))}` |

The conclusion shape matches the canonical per-(F, Q) form used by
`etilde6_not_finite_type_per_kQ` (`FieldGenericETilde6.lean:319-327`),
`d5tilde_not_finite_type_per_kQ`,
`star_subgraph_not_finite_type_per_kQ`
(`FieldGenericStar.lean:579-594`), and the rest of the leaf API. No
deviation.

`hv : 4 ≤ vertexDegree adj v` unfolds directly to `4 ≤ S.card` where
`S := Finset.univ.filter (fun w => adj v w = 1)`, matching the
definition `vertexDegree adj i = (Finset.univ.filter (fun j => adj i j = 1)).card`
(`DynkinForward.lean:29-30`).

## D2 — Proof body correctness (PASS)

The body is **textually parallel** to the `_kQ`-free original at every
line. Walk-through:

### Neighbor extraction (lines 663-676)

Identical to `InfiniteTypeConstructions.lean:4070-4083`:
`set S`, `hS_card`, `Finset.exists_subset_card_eq`, `Fintype.equivFinOfCardEq`,
`neighbors`, `h_adj`, `h_ne`, `h_inj`. The only formatting nit is the
parenthesisation of `(e.injective (Subtype.val_injective hab))` which
matches the original. `h_inj : Function.Injective neighbors` is
correctly derived via `Subtype.val_injective` (since
`neighbors i = (e i).val` and `e` is an `Equiv`, hence injective).

### Pairwise-non-adjacent branch (lines 679-681)

Dispatches to `star_subgraph_not_finite_type_per_kQ`
(`FieldGenericStar.lean:579`). Argument order matches that theorem's
signature: `adj hsymm hdiag center ⟨neighbors, h_inj⟩ hleaves_ne hadj_edge hadj_indep F Q hOrient`.
The wrapper passes `v` as `center`, `⟨neighbors, h_inj⟩` as the
embedding `Fin 4 ↪ Fin n`, then `h_ne, h_adj, h_indep` as the three
hypotheses, then `F Q hOrient`.

### Triangle branch (lines 682-695)

`push_neg at h_indep` produces `∃ i j, adj (neighbors i) (neighbors j) ≠ 0`.
`h_one : adj (neighbors i) (neighbors j) = 1` is derived correctly
from `h01` via the case-split (zero case is absurd via `h_nonzero`).
`hij : neighbors i ≠ neighbors j` is derived correctly by contradiction:
if equal, then `adj x x = 1` contradicts `hdiag x = 0`.

Dispatches to `triangle_infinite_type_per_kQ`
(`FieldGenericCycle.lean:398`). Argument order matches:
`adj hsymm hdiag _h01 a b c hab hbc hac h_ab h_bc h_ac F Q hOrient`.
The wrapper passes `v, neighbors i, neighbors j` as `a, b, c` with
- `hab := (h_ne i).symm` (proves `v ≠ neighbors i`),
- `hbc := hij` (proves `neighbors i ≠ neighbors j`),
- `hac := (h_ne j).symm` (proves `v ≠ neighbors j`),
- `h_ab := h_adj i` (proves `adj v (neighbors i) = 1`),
- `h_bc := h_one` (proves `adj (neighbors i) (neighbors j) = 1`),
- `h_ac := h_adj j` (proves `adj v (neighbors j) = 1`),

all of which type-check against the leaf signature.

### Build verification

`lake build EtingofRepresentationTheory.Chapter6` passes at
**8080/8080 jobs** on `main` (commit `733bd0d`), reproducing the PR
author's count. Sorry inventory unchanged at **9**, all pre-existing:

| File:Line | Note |
|---|---|
| `InfiniteTypeConstructions.lean:3331` | pre-existing |
| `InfiniteTypeConstructions.lean:3588` | pre-existing |
| `InfiniteTypeConstructions.lean:3815` | pre-existing |
| `FieldGenericT125.lean:39` | D1 stub (#2793) |
| `FieldGenericStar.lean:543` | wave-54 Wall 1 (#2789 / #2801) |
| `FieldGenericETilde6.lean:291` | wave-54 Wall 1 |
| `FieldGenericD5Tilde.lean:798` | D̃₅ leaf eq (#2853 / #2851) |
| `FieldGenericD5Tilde.lean:974` | D̃₅ leaf eq |
| `FieldGenericETilde7.lean:273` | wave-54 Wall 1 |

The new theorem body introduces **no new `sorry`**. The two warnings on
`FieldGenericStar.lean:160` (unscoped `maxHeartbeats`) and
`FieldGenericCycle.lean:84` (`show` linter) are pre-existing and not
adjacent to the new theorem.

## D3 — Pattern-decision notes for downstream D2 sub-PRs

### Placement rationale (option 1 vs 2 vs 3)

PR #2891 chose **option 1**: cross-import
`import EtingofRepresentationTheory.Chapter6.FieldGenericCycle` into
`FieldGenericStar.lean`, place the wrapper at the bottom of Star.

Why this was right for D2.degree4: the wrapper dispatches to **both**
`star_subgraph_not_finite_type_per_kQ` (Star) **and**
`triangle_infinite_type_per_kQ` (Cycle), so a single host file must
import both. Three placement options exist:

| Option | Host | Cost |
|---|---|---|
| 1 (chosen) | `FieldGenericStar.lean` | one new import (`FieldGenericCycle`) in Star |
| 2 | `FieldGenericCycle.lean` | one new import (`FieldGenericStar`) in Cycle |
| 3 | new `FieldGenericDegree4.lean` | one new file + two imports |

Option 1 is the cheapest in file-count terms. Option 2 is symmetric in
import cost but worse for Cycle's role as a foundational module (Cycle
is currently imported by Star, ETilde6, ETilde7, D5Tilde — adding
Star as a dependency of Cycle creates a downward import flow against
the natural layering). Option 3 adds a file for ~60 lines, which is
overkill at this stage. **Option 1 is the correct precedent for "both
leaves are in disjoint files" wrappers.**

### Per-(F, Q) leaf `[IsAlgClosed F]` catalog

Audit of all current `_per_kQ` leaves (`Chapter6/FieldGeneric*.lean`):

| Leaf | `[IsAlgClosed F]`? | File |
|---|---|---|
| `cycle_not_finite_type_per_kQ` | **no** | `FieldGenericCycle.lean:326` |
| `chordless_cycle_infinite_type_per_kQ` | **no** | `FieldGenericCycle.lean:373` |
| `triangle_infinite_type_per_kQ` | **no** | `FieldGenericCycle.lean:398` |
| `star_not_finite_type_per_kQ` | yes | `FieldGenericStar.lean:543` |
| `star_subgraph_not_finite_type_per_kQ` | yes | `FieldGenericStar.lean:579` |
| `t125_not_finite_type_per_kQ` | yes | `FieldGenericT125.lean:39` |
| `etilde6_not_finite_type_per_kQ` | yes | `FieldGenericETilde6.lean:319` |
| `etilde7_not_finite_type_per_kQ` | yes | `FieldGenericETilde7.lean:301` |
| `d5tilde_not_finite_type_per_kQ` | yes | `FieldGenericD5Tilde.lean:999` |

**Rule of thumb for D2 sub-deliverables**: a wrapper carries
`[IsAlgClosed F]` **iff any of its dispatch leaves does**. The current
shape — `star`, `t125`, `etilde6`, `etilde7`, `d5tilde` all need it,
cycle/triangle do not — means:

| D2 sub-deliverable | Dispatches to | `[IsAlgClosed F]`? |
|---|---|---|
| D2.cycle (`graph_with_list_cycle_infinite_type_per_kQ`) | `chordless_cycle_*_per_kQ` | **no** |
| D2.degree4 (landed in #2891) | `star_subgraph_*` + `triangle_*` | yes |
| D2.adjacent (`adjacent_branches_infinite_type_per_kQ`) | `d5tilde_*` (D̃₅) | yes |
| D2.single (`single_branch_not_posdef_infinite_type_per_kQ`) | `etilde6_*` + `etilde7_*` + `t125_*` | yes |
| D2.nonadj (`non_adjacent_branches_infinite_type_per_kQ`) | `d5tilde_*` + `etilde6_*` + `etilde7_*` | yes |
| D2.outer (`acyclic_branch_not_posdef_infinite_type_per_kQ`) | D2.adjacent + D2.single + D2.nonadj | yes |

### Recommended placement for each remaining D2 sub-deliverable

These are *recommendations* for the next planner cycle to encode in the
pre-split sub-issues; the worker may deviate with justification.

- **D2.cycle** → `FieldGenericCycle.lean` (natural host; no cross-import
  needed; no `[IsAlgClosed F]`). Asymmetric to D2.degree4 because the
  only leaf needed lives in Cycle itself.
- **D2.adjacent** → `FieldGenericD5Tilde.lean` (already imports Star;
  needs nothing more). Carries `[IsAlgClosed F]`.
- **D2.single** → cross-import: add `import FieldGenericT125` to
  `FieldGenericETilde7.lean` (which already imports ETilde6) and place
  there. Avoids creating a new file. Or, if `FieldGenericETilde7.lean`
  grows past ~500 lines after the wrapper (currently ~301; adding ~300
  pushes near the soft cap), prefer a new file
  `FieldGenericTpqr.lean` importing ETilde6, ETilde7, T125.
- **D2.nonadj** → cross-import: add `import FieldGenericD5Tilde` to
  `FieldGenericETilde7.lean` (no cycle: D5Tilde does not import ETilde7
  yet) and place there; or, given the ~900-line size, a new
  `FieldGenericNonAdjacent.lean` is justified. **Strong recommendation
  for a new file** — D2.nonadj is the largest sub-deliverable, and
  putting it in a dedicated host keeps `FieldGenericETilde7.lean`
  focused.
- **D2.outer** → new `FieldGenericNotPosdef.lean` (or extend an
  existing host that already imports all of D2.adjacent / D2.single /
  D2.nonadj's host files). Carries `[IsAlgClosed F]`. This is the
  natural seam between the leaf catalog and the Theorem 2.1.2 bridge
  (D3), so a dedicated file is justified.

### Pattern recipe (for citation by future D2 sub-PRs)

When opening a per-(F, Q) wrapper sub-PR:

1. **Statement template**: append `(F : Type) [Field F] [IsAlgClosed F]?`
   (drop `IsAlgClosed` only if every dispatch leaf does too),
   `(Q : @Quiver.{0,0} (Fin n))`,
   `[∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]`,
   `(hOrient : @Etingof.IsOrientationOf n Q adj)` to the `_kQ`-free
   signature; replace the conclusion with the canonical per-(F, Q)
   `¬ Set.Finite {d | ∃ V, ...}` shape.
2. **Proof template**: copy the `_kQ`-free body verbatim, then suffix
   every `subgraph_infinite_type_transfer` dispatch with `_per_kQ` and
   append `F Q hOrient` (or, for direct leaf dispatch as in this PR,
   suffix the leaf name with `_per_kQ` and append `F Q hOrient`).
3. **Placement**: pick the existing file with the largest overlap of
   already-imported dispatch leaves. Cross-import the others if and
   only if no single existing file dominates. Create a new file only
   if the wrapper crosses the ~300-line threshold or is the assembly
   point for multiple wrappers (e.g. D2.outer).
4. **Attribute**: prefix the theorem with
   `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver CategoryTheory.ReflQuiver.toQuiver in`
   — required at every `_per_kQ` wrapper site to prevent the
   `(F, Q)` quiver from being shadowed by the category-theory quiver
   instance synthesised from `Field F`.

### Audit precedent

This is the 5th wave-61 audit (after #2861, #2866, #2879, #2885), all
PASS. The audit cadence has caught no defects, indicating the per-(F, Q)
recipe is stable. The remaining audit value is **pattern documentation
for downstream workers**, not defect detection — calibrate future
review-issue scope accordingly.

## No code changes

This audit recommends **no edits to `main`**. Sorry-count delta: **0**.

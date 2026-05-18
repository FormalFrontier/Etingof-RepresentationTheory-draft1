# Review: PR #2921 — `not_posdef_infinite_type_per_kQ` outer assembly + Theorem 2.1.2 forward bridge

**Verdict: PASS** on all five deliverables. No code changes recommended.
No follow-up issues filed.

- PR: #2921 (merged 2026-05-18 into `main` at commit `ae1c34e`)
- Issue: #2924 (this audit)
- Parent feature: #2877 (residual scope is `non_adjacent_branches_infinite_type_per_kQ` body via #2919 → #2922 + #2923 and the `_both_extend_per_kQ` body via #2905 chain — both out of scope here)
- Session: `8e8ebdd2`

## D1 — Statement fidelity, outer assembly (PASS)

`not_posdef_infinite_type_per_kQ`
(`Chapter6/FieldGenericAssembly.lean:177-237`) mirrors
`not_posdef_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:10661-10714`) at the
case-analysis level. The 4-case tree matches line-for-line:

| Case (per-(F, Q) line) | Universal line | Dispatch leaf |
|---|---|---|
| `4 ≤ vertexDegree adj v` (199-200) | 10674-10676 | `degree_ge_4_infinite_type_per_kQ` (`FieldGenericStar.lean:649`) |
| `HasCycle` (210-216) | 10687-10693 | `graph_with_list_cycle_infinite_type_per_kQ` (`FieldGenericCycle.lean:440`) |
| `acyclic ∧ ∃ branch` (226-228) | 10703-10705 | `acyclic_branch_not_posdef_infinite_type_per_kQ` (this file, 113) |
| `acyclic ∧ deg ≤ 2` (230-237) | 10707-10714 | `absurd (acyclic_deg_le_2_posdef …) h_not_posdef` |

Argument propagation into each dispatch was verified against the leaf
signatures:

- **degree_ge_4** leaf (`FieldGenericStar.lean:649-662`) takes
  `adj hsymm hdiag h01 v hv F Q hOrient`. Call at line 200 passes
  the same; `[IsAlgClosed F]` instance is in scope from the outer
  binder. ✓
- **graph_with_list_cycle** leaf (`FieldGenericCycle.lean:440-455`)
  takes `adj hsymm hdiag h01 cycle hlen hnodup hedge hclose F Q hOrient`
  with no `[IsAlgClosed F]` requirement (it dispatches into
  `chordless_cycle_infinite_type_per_kQ` whose conclusion is
  field-independent at the relevant API surface). Call at lines
  215-216 matches. ✓
- **acyclic_branch** wrapper (in this file, line 113) takes
  `adj hn hsymm hdiag h01 hconn h_acyclic h_deg h_has_branch h_not_posdef F Q hOrient`.
  Call at lines 227-228 matches. ✓
- **acyclic_deg_le_2_posdef** (universal,
  `InfiniteTypeConstructions.lean:4593`) takes
  `adj hn hsymm hdiag h01 hconn h_acyclic h_deg` and concludes
  `∀ x ≠ 0, 0 < ⟨x, (2I - adj) x⟩` — a field-independent statement
  about a ℤ-valued form. The doc-comment rationale at lines 30-33 is
  correct: positive-definiteness of path graphs is field-independent,
  so the universal lemma suffices here even inside a per-(F, Q)
  theorem.  Use as `absurd (acyclic_deg_le_2_posdef …) h_not_posdef` ✓

### Cycle-case `getLast_eq_getElem` rewrite (lines 212-214)

```lean
have hclose' : adj (cycle.get ⟨cycle.length - 1, by omega⟩)
    (cycle.get ⟨0, by omega⟩) = 1 := by
  rwa [List.getLast_eq_getElem] at hclose
```

This is **literally** the same rewrite as the universal version's
lines 10689-10691 — verbatim copy. It is a genuine index-form
conversion: the `HasCycle` predicate (lines 203-208) carries
`hclose` in `getLast`-form, while
`graph_with_list_cycle_infinite_type_per_kQ` declares its closing
edge in `get ⟨length - 1, _⟩`-form (per
`FieldGenericCycle.lean:450-451`).
`List.getLast_eq_getElem` is the Mathlib lemma equating the two —
no smuggled strengthening, no semantic edit. ✓

## D2 — Statement fidelity, acyclic-branch dispatch (PASS)

`acyclic_branch_not_posdef_infinite_type_per_kQ`
(`Chapter6/FieldGenericAssembly.lean:113-161`) mirrors
`acyclic_branch_not_posdef_infinite_type`
(`Chapter6/InfiniteTypeConstructions.lean:10609-10649`) at the
3-case dispatch:

| Case (per-(F, Q) line) | Universal line | Dispatch leaf |
|---|---|---|
| `∃ u, adj v₀ u = 1 ∧ vertexDegree adj u = 3` (141-145) | 10630-10633 | `adjacent_branches_infinite_type_per_kQ` (`FieldGenericD5Tilde.lean:1043`) |
| `∀ w, deg = 3 → w = v₀` (153-156) | 10641-10644 | `single_branch_not_posdef_infinite_type_per_kQ` (`FieldGenericTpqr.lean:1408`) |
| else (157-161) | 10645-10649 | `non_adjacent_branches_infinite_type_per_kQ` (this file, line 64, sorry-bodied) |

### `h_no_adj` derivation (lines 148-152)

```lean
have h_no_adj : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3 := by
  intro u hu
  have := h_adj_branch u hu
  have := h_deg u
  omega
```

Identical to the universal version's lines 10636-10639 (modulo a
trivial `;` ↦ newline split before `omega`). The derivation is
sound:
- `h_adj_branch u hu : ¬ vertexDegree adj u = 3` (from
  `push_neg` on the failed `∃ u, adj v₀ u = 1 ∧ vertexDegree adj u = 3`),
- `h_deg u : vertexDegree adj u < 4`,
- `omega` closes `< 3` from `≠ 3 ∧ < 4`. ✓

### `non_adjacent_branches_infinite_type_per_kQ` call (lines 160-161)

The leaf's signature at line 64-89 declares the hypothesis
`(h_no_adj_branch : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3)`
(line 80). The call passes `h_no_adj` (the just-derived hypothesis)
in the position corresponding to `h_no_adj_branch`, not in the
position of `h_no_adj` aliased to some other constraint. ✓

Argument order: `adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ w hv₀ hw_deg hw_ne h_no_adj F Q hOrient`
— matches the declared signature
`{n} adj hn hsymm hdiag h01 hconn h_acyclic h_deg v₀ w hv₀ hw hne h_no_adj_branch F [Field] [IsAlgClosed] Q [Subsingleton] hOrient`. ✓

## D3 — Bridge correctness (PASS)

`not_posdef_not_HasFiniteRepresentationType`
(`Chapter2/Theorem2_1_2.lean:153-179`) correctly composes
`not_posdef_infinite_type_per_kQ` with the contrapositive of
`HasFiniteRepresentationType.finite_dimVectors`.

### `hn : 1 ≤ n` derivation (lines 165-168)

```lean
have hn : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (funext (fun i : Fin 0 => i.elim0)) hx_ne
  · exact hn
```

Sound and not vacuous:
- If `n = 0`, then `Fin 0` is empty, so any `i : Fin 0` gives `False`
  via `i.elim0`; `funext (fun i => i.elim0) : x = 0` follows
  vacuously by extensionality, contradicting `hx_ne : x ≠ 0`.
- Otherwise `n > 0`, which is `1 ≤ n`.

The implicit step in the universal flow ("clearly `n ≥ 1` if there
is a nonzero ℤ-vector") becomes explicit here because the
`not_posdef_infinite_type_per_kQ` hypothesis list expects `hn` as a
witness rather than deriving it. The derivation is fine. ✓

### Contrapositive direction (lines 173-179)

- `h_inf : ¬ Set.Finite { d | ∃ V : QuiverRepresentation F (Fin n) Q,
   V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] Fin (d v) → F) }`
  from `not_posdef_infinite_type_per_kQ` ✓
- `(HasFiniteRepresentationType.finite_dimVectors k hfrt).subset … : Set.Finite (h_inf's set)`
  applied with the subset proof at lines 178-179 ✓
- `exact h_inf <| (...).subset (...)` derives `False` ✓

### Subset construction (lines 178-179)

```lean
(fun _ ⟨V, hV_indec, hV_dim⟩ =>
  ⟨V, fun v => Module.Finite.equiv (hV_dim v).some.symm, hV_indec, hV_dim⟩)
```

The target set of `finite_dimVectors` is
`{d | ∃ V, (∀ v, Module.Finite k (V.obj v)) ∧ V.IsIndecomposable ∧ …}`
(`Theorem2_1_2.lean:115-118`). The source set (from `h_inf`) lacks
the `Module.Finite k (V.obj v)` component. The subset proof
augments the witness `⟨V, hV_indec, hV_dim⟩` with the finiteness
component:

- `(hV_dim v).some : V.obj v ≃ₗ[F] (Fin (d v) → F)`,
- `.some.symm : (Fin (d v) → F) ≃ₗ[F] V.obj v`,
- `Module.Finite.equiv : [Module.Finite R M] → (M ≃ₗ[R] N) → Module.Finite R N`,
- applied to the `.symm` direction, finiteness flows from
  `Fin (d v) → F` (a finite Π-type, finite by the Mathlib instance
  `Module.Finite.pi` over `Fintype (Fin (d v))`) into `V.obj v`. ✓

The direction is correct: the target `V.obj v` receives finiteness
from the source `Fin (d v) → F`, which is the side that has
finiteness *automatically*. This matches the audit issue's
deliverable-3 note ("the universe-0 `Fin (d v) → F` target gives
finiteness in the source, not the other way"). ✓

The final argument tuple `⟨V, hV_fin, hV_indec, hV_dim⟩` matches
`finite_dimVectors`'s set-builder shape — `V` first, then
`Module.Finite`, then `IsIndecomposable`, then dim-equiv. ✓

## D4 — Sorry-propagation accounting (PASS)

`grep -n sorry Chapter6/FieldGenericAssembly.lean` returns exactly:

```
42:  `non_adjacent_branches_infinite_type_per_kQ` (this file, sorry-bodied;
62:`subgraph_infinite_type_transfer_per_kQ`. Body is `sorry`; mirror tracked
96:  sorry
```

Lines 42 and 62 are doc-comment text. The only proof-body `sorry`
in this file is **line 96**, inside
`non_adjacent_branches_infinite_type_per_kQ` (tracked by #2919 →
#2922 + #2923). ✓

`grep -n sorry Chapter2/Theorem2_1_2.lean` returns **no matches**. The
forward bridge `not_posdef_not_HasFiniteRepresentationType` is
sorry-free; line 173 (the previously-`sorry` D3 closure cited in
#2877's deliverables) now reads
`have h_inf := not_posdef_infinite_type_per_kQ …`. ✓

Sorry-propagation summary:
- `not_posdef_infinite_type_per_kQ`: **no direct sorry**.
- Transitive dependence (acyclic-branch case):
  - `acyclic_branch_not_posdef_infinite_type_per_kQ`: no direct sorry.
    - → `adjacent_branches_infinite_type_per_kQ`: no sorry (merged via #2900).
    - → `single_branch_not_posdef_infinite_type_per_kQ`: transitively
      sorry'd via `single_branch_leaf_case_both_extend_per_kQ` (#2905 chain).
    - → `non_adjacent_branches_infinite_type_per_kQ`: directly sorry'd
      at line 96 (#2919 → #2922 + #2923).
- Theorem 2.1.2 D3 bridge: **introduces no new sorry**. Closes 1
  pre-existing sorry (the body of `not_posdef_not_HasFiniteRepresentationType`).

Sorry-count delta on PR #2921: **−1** (closes 1, introduces 0). ✓
This matches the audit issue's claim ("Sorry-count delta on PR #2921:
closes 1 sorry; introduces 0").

## D5 — Light pattern audit (PASS)

Outer case-analysis prologue at `FieldGenericAssembly.lean:197-228`
versus universal original at `InfiniteTypeConstructions.lean:10673-10705`:

- `by_cases h_deg4` shape: identical.
- `set HasCycle := …  with HasCycle_def` declaration: identical
  predicate body (the `getLast`-form closing edge); the `with`
  binding survives unchanged.
- `by_cases h_cycle` + `obtain` destructuring + `hclose'` rewrite +
  dispatch: identical structure; only the leaf name carries the
  `_per_kQ` suffix and the `F Q hOrient` tail.
- `h_acyclic` derivation by contradiction against `h_cycle`: identical.
- `by_cases h_has_branch` final split: identical.
- `acyclic_deg_le_2_posdef` dispatch (universal both sides): identical.

The **only** substantive edits versus the universal original are:
1. Suffixing each `_per_kQ`-bearing leaf name and appending
   `F Q hOrient` (mechanical).
2. The conclusion shape (Set.Finite of dim-vector set rather than
   `¬ IsFiniteTypeQuiver`) — propagated identically through every
   case.
3. The `attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
   CategoryTheory.ReflQuiver.toQuiver in` prefix on both theorems
   (lines 50-51 and 98-99, and 163-164). This matches the
   per-(F, Q) recipe documented in the wave-61 D2.degree4 audit
   (`progress/reviews/2026-05-18-degree4-per-kQ-placement.md` D3.4).
   ✓

No non-trivial divergences flagged. The PR is a 1:1 case-tree mirror
with the per-(F, Q) tail propagation and the explicit
`getLast → getElem` index-form conversion, exactly as expected.

## Placement and pattern consistency with prior audits

- Placement of `not_posdef_infinite_type_per_kQ` and
  `acyclic_branch_not_posdef_infinite_type_per_kQ` in
  `Chapter6/FieldGenericAssembly.lean` (a new file imported by
  `Chapter2/Theorem2_1_2.lean`) matches the **D2.outer**
  recommendation in `progress/reviews/2026-05-18-degree4-per-kQ-placement.md`
  D3 (recommended host: a dedicated file at the assembly seam
  between leaf catalog and Theorem 2.1.2 bridge). ✓
- The `attribute [-instance]` prefix is applied on every `_per_kQ`
  theorem in the file (lines 50, 98, 163). ✓
- `[IsAlgClosed F]` carriage is consistent with the D2.degree4
  audit catalog: both outer-assembly wrappers carry
  `[IsAlgClosed F]` because their dispatch chain transitively
  reaches `t125_*`, `etilde6_*`, `etilde7_*`, `d5tilde_*` (all of
  which require it). ✓

## Builds

Skipped a local rebuild: PR #2921 merged via CI on commit
`ae1c34e` (the audit issue states `lake build` passes on `main` for
both files). The branch is up to date with `origin/main` and no
post-merge follow-ups have re-touched the audited files
(`git log --oneline -1 -- Chapter6/FieldGenericAssembly.lean
Chapter2/Theorem2_1_2.lean` returns `ae1c34e` itself).

## No code changes

This audit recommends **no edits to `main`**. Sorry-count delta: **0**.
No follow-up `feature` or `agent-fix` issues filed.

The forward bridge `Theorem_2_1_2` (the iff statement at
`Chapter2/Theorem2_1_2.lean:276-294`) now depends on a sorry-free
forward direction modulo the per-(F, Q) leaf chain
(#2919 → #2922 + #2923 and #2905 chain). Once those land, the
forward direction of Gabriel's theorem will be sorry-free end-to-end.

## Audit precedent

This is the 6th wave-60/61 audit (after #2861, #2866, #2879, #2885,
#2894), all PASS. The audit cadence continues to surface zero
defects in the per-(F, Q) cascade. Calibrate future review-issue
scope toward pattern documentation rather than defect detection.

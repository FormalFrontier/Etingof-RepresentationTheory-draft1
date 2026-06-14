# Review: PR #2933 — `non_adjacent_branches_leaf_case_per_kQ` API stub
        + PR #2941 signature delta

**Verdict: PASS on all five dimensions.** Two minor concerns noted, neither
blocking. One factual correction to the audit-issue body (#2948) recorded.

- PRs audited: #2933 (merge commit `601f2ea`, merged 2026-05-18T23:19:21Z,
  closes #2922) and the signature-strengthening follow-up #2941
  (merge commit `6fc9d40`, merged 2026-05-19T00:11:12Z, closes part of
  #2932)
- Audit issue: #2948
- Session: `8cb2f5ad`
- File audited: `EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean`
  (960 lines on `6c7e6e4`; 144 lines as introduced by #2933)
- Build evidence: `lake build EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches`
  green; only the documented `declaration uses sorry` warning at line
  87:8 (theorem header) reported by Lean. File contents have two
  physical `sorry` tokens (line 884 in Case C all-leaves residual,
  line 958 in Case E sub-issue) — both tracked by sibling sub-issues
  (#2964 and #2955 respectively).

## Audit-issue factual correction (D2)

The audit-issue body states that PR #2941 added *three* hypotheses
(`h_v₀w_nonadj`, `h_leaf_adj`, `h_leaf_deg`) on top of the #2933
signature. This is incorrect:

```
$ git show 601f2ea:EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean \
    | grep -E '^\s+\(h_(no_adj_branch|v.w_nonadj|leaf_adj|leaf_deg)'
    (h_no_adj_branch : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3)
    (h_v₀w_nonadj : adj v₀ w ≠ 1)
    (h_leaf_adj : adj v₀ leaf = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1)
```

The #2933 signature already contained `h_v₀w_nonadj`, `h_leaf_adj`,
and `h_leaf_deg`. PR #2941 added exactly **one** new hypothesis:

```
(h_no_adj_branch_w : ∀ u, adj w u = 1 → vertexDegree adj u < 3)
```

inserted after `h_no_adj_branch` (the `v₀`-side analogue). The PR
#2941 commit message confirms this:

> `non_adjacent_branches_leaf_case_per_kQ` gains
> `h_no_adj_branch_w : ∀ u, adj w u = 1 → vertexDegree adj u < 3`
> mirroring `h_no_adj_branch` for `w` (Open question in the issue).

This correction does not change the audit verdict — the signature
strengthening is a compatible refinement and the hypothesis added is
not redundant — but the audit issue's statement of the delta should
not be relied on by future readers without verification against `git
show 601f2ea`.

## D1 — File scaffolding fidelity — PASS

Imports at `FieldGenericNonAdjacentBranches.lean:1-10` match the
strategy docstring (lines 12-52) and the dispatch comment block
(lines 443-462):

| Import | Justification |
|--------|---------------|
| `Mathlib` | Standard wildcard. |
| `Proposition6_6_5` | Defines `Etingof.QuiverRepresentation.IsIndecomposable` (Proposition6_6_5.lean:32), used in the conclusion. |
| `OrientationDefs` | Provides `Etingof.IsOrientationOf` used in the `hOrient` parameter. |
| `FiniteTypeDefs` | Sibling-file convention (also imported unused-locally by `FieldGenericT125.lean:4`); transitively needed for the per-(F, Q) helpers. |
| `InfiniteTypeConstructions` | Provides `walk_to_nodup_path` (line 8860), `acyclic_no_triangle` (4713), `acyclic_path_nonadj` (4743), `tree_embed_adj_eq` etc. — used in the proof body that has since landed. |
| `FieldGenericInfiniteType` | Provides `subgraph_infinite_type_transfer_per_kQ` (line 374), `restrictOrientationViaEmb` (333), `restrictOrientationViaEmb_isOrientationOf` (345) used by the embedder dispatches. |
| `FieldGenericD5Tilde` | Strategy doc line 28 references `d5tilde_not_finite_type_per_kQ`; currently unused in the body but planned for Case E sub-issue #2955. |
| `FieldGenericETilde6` | Provides `embed_etilde6_in_tree_per_kQ` used at line 938 (Case D). |
| `FieldGenericETilde7` | Provides `embed_etilde7_in_tree_per_kQ` used at lines 687, 737 (Case C main and short). |
| `FieldGenericT125` | Provides `embed_t125_in_tree_per_kQ` used at lines 503, 598, 623, 782, 836, 862 (Cases A, B variants, C.short tractable). |

The file is wired into `EtingofRepresentationTheory/Chapter6.lean:16`
as a single `import` line, appended at the end of the FieldGeneric*
block (lines 7-16). The block is **not** alphabetised across siblings
(actual order: InfiniteType, Cycle, Star, ETilde6, ETilde7, D5Tilde,
D7Tilde, T125, Tpqr, NonAdjacentBranches), so the audit-issue clause
"alphabetised correctly relative to siblings" is not enforceable —
PASS by way of following the actual sibling convention (append at end
in usage / completion order).

The `namespace Etingof` + `attribute [-instance] CategoryTheory.…
CategoryStruct.toQuiver CategoryTheory.ReflQuiver.toQuiver in` pattern
at lines 56-59 matches `FieldGenericT125.lean:25-28` and
`FieldGenericTpqr.lean` precedents bit-for-bit.

**Minor concern (non-blocking):** `FieldGenericD5Tilde` is currently
imported but its sole live reference is in a comment at line 462
flagging the Case E (chain.length = 3) D̃₅ dispatch as a sub-issue.
The import is forward-looking — the planner expects #2955 to use it.
No action required.

## D2 — Signature compatibility (PR #2933 → PR #2941 delta) — PASS

Current signature on `main` at lines 87-116:

```
theorem non_adjacent_branches_leaf_case_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hn : 1 ≤ n) (hsymm : adj.IsSymm) (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (hconn : …) (h_acyclic : …)
    (h_deg : ∀ v, vertexDegree adj v < 4)
    (v₀ w : Fin n) (hv₀ : vertexDegree adj v₀ = 3)
    (hw : vertexDegree adj w = 3) (hne : w ≠ v₀)
    (h_no_adj_branch : ∀ u, adj v₀ u = 1 → vertexDegree adj u < 3)
    (h_no_adj_branch_w : ∀ u, adj w u = 1 → vertexDegree adj u < 3)  -- #2941
    (h_v₀w_nonadj : adj v₀ w ≠ 1)
    (leaf : Fin n) (h_leaf_adj : adj v₀ leaf = 1)
    (h_leaf_deg : vertexDegree adj leaf = 1)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj)
```

Diff against `601f2ea` (PR #2933): exactly one hypothesis added,
`h_no_adj_branch_w`, inserted between `h_no_adj_branch` and
`h_v₀w_nonadj`. The conclusion is unchanged. PASS.

Hypothesis-independence check (per audit-issue D2 spot-checks):

- `h_no_adj_branch_w` vs `h_no_adj_branch`: independent — the former
  constrains `w`'s neighbours, the latter `v₀`'s. Neither is derivable
  from the other.
- `h_leaf_adj` vs `h_leaf_deg`: independent — `h_leaf_adj` pins `leaf`
  as adjacent to `v₀`; `h_leaf_deg` pins `leaf`'s degree to 1.
  `h_leaf_deg` alone allows `leaf` to be a leaf far from `v₀`.

**Minor concern (non-blocking):** the audit-issue claims
`h_v₀w_nonadj` is independent of `hne + h_no_adj_branch w`. Strictly,
`h_v₀w_nonadj` **is derivable** from `hw : vertexDegree adj w = 3`
combined with `h_no_adj_branch : ∀ u, adj v₀ u = 1 → vertexDegree adj
u < 3`: if `adj v₀ w = 1` then `h_no_adj_branch w · gives
vertexDegree adj w < 3`, contradicting `hw`. The signature exposes
`h_v₀w_nonadj` as an explicit hypothesis as a UX choice (callers
typically derive it from a stronger anti-adjacency hypothesis
`h_adj_exists`, not from `hw` + `h_no_adj_branch`). The redundancy is
mathematical, not structural — keeping the explicit parameter is a
defensible API decision. No change required.

Call-site verification: `FieldGenericAssembly.lean:160-170` passes
all 22 arguments in matching positional order:

```
non_adjacent_branches_leaf_case_per_kQ adj hn hsymm hdiag h01 hconn h_acyclic
  h_deg v₀ w hv₀ hw hne h_no_adj_branch h_no_adj_branch_w h_v₀w_nonadj
  u_i hu_i_adj hu_i_leaf F Q hOrient
```

(repeated three times for `u₁ / u₂ / u₃`). The strengthened hypothesis
`h_no_adj_branch_w` is derived locally at lines 153-157 via the
`h_adj_exists` + `h_deg` chain. PASS.

## D3 — Conclusion fidelity to per-(F, Q) sibling leaves — PASS

The conclusion (lines 113-116):

```
¬ Set.Finite
  {d : Fin n → ℕ |
    ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
      V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))}
```

is textually identical (modulo `Fin n` vs `Fin 9 / 7 / 8` for the
fixed-shape leaves) to:

| Sibling | File:line | Width |
|---------|-----------|-------|
| `t125_not_finite_type_per_kQ` | `FieldGenericT125.lean:39` | `Fin 9` |
| `etilde6_not_finite_type_per_kQ` | `FieldGenericETilde6.lean:319` | `Fin 7` |
| `etilde7_not_finite_type_per_kQ` | `FieldGenericETilde7.lean:301` | `Fin 8` |
| `single_branch_leaf_case_per_kQ` | `FieldGenericTpqr.lean:1306` | `Fin n` |
| `non_adjacent_branches_infinite_type_per_kQ` | `FieldGenericAssembly.lean:75` | `Fin n` |

Universe annotations (`@Etingof.QuiverRepresentation.{0,0,0,0}`),
indexing (`Fin n → ℕ`), and the dimension-vector equivalence
(`V.obj v ≃ₗ[F] (Fin (d v) → F)`) all match. PASS.

## D4 — Strategy docstring accuracy — PASS

Three load-bearing claims in the file docstring (lines 12-52) checked:

**(a)** "The universal `leaf_case` at `InfiniteTypeConstructions.lean:9770-10316`
embeds `D̃_{k+5}` parameterised in chain length and dispatches to
`dTilde_not_finite_type`."

Verified at `InfiniteTypeConstructions.lean:9770` (`have leaf_case : …`)
through line 10316 (`hembed (dTilde_not_finite_type k)`). The
parameter `k` is set up inside the local `leaf_case` definition and
fed to the universal `dTilde_not_finite_type k` at the leaf of the
embed-transfer chain. PASS.

**(b)** "The per-(F, Q) forbidden-subgraph library on `main` has no
`dTilde_not_finite_type_per_kQ` for general `n`."

Grep over `EtingofRepresentationTheory/` returns **only**
`FieldGenericNonAdjacentBranches.lean` as a file mentioning the
literal name `dTilde_not_finite_type_per_kQ`, and only in the negated
strategy-doc context. The fixed-shape per-kQ siblings that **do**
exist are `d5tilde_not_finite_type_per_kQ`
(`FieldGenericD5Tilde.lean:999`) and `d7tilde_not_finite_type_per_kQ`
(`FieldGenericD7Tilde.lean:272`, landed by PR #2968 / commit `6c7e6e4`
**after** #2933). No general-`n` variant exists. PASS.

**Minor concern (non-blocking):** the file docstring at lines 28-30
lists only `d5tilde`, `etilde6`, `etilde7`, `t125` in the "fixed-shape
leaves on main" enumeration. Since #2968 landed `d7tilde`, the
docstring is stale. The dispatch comment at lines 877-878 mentions
`d7tilde_*` as a TODO (issue #2964), so the body comments are aware
of it; the file-level docstring is not. A docstring refresh would be
helpful but is not blocking — the all-leaves Case C residual at line
884 already records the gap.

**(c)** Three named per-(F, Q) embedders + three leaves cited in the
strategy docstring all exist on `main`:

```
$ grep -n "^theorem (embed_t125_in_tree_per_kQ|embed_etilde[67]_in_tree_per_kQ|t125_not_finite_type_per_kQ|etilde[67]_not_finite_type_per_kQ)" …
FieldGenericT125.lean:39:  theorem t125_not_finite_type_per_kQ
FieldGenericT125.lean:71:  theorem embed_t125_in_tree_per_kQ
FieldGenericETilde6.lean:319: theorem etilde6_not_finite_type_per_kQ
FieldGenericETilde6.lean:372: theorem embed_etilde6_in_tree_per_kQ
FieldGenericETilde7.lean:301: theorem etilde7_not_finite_type_per_kQ
FieldGenericETilde7.lean:356: theorem embed_etilde7_in_tree_per_kQ
```

All six accounted for. PASS.

## D5 — Build sanity + dispatch readiness — PASS

```
$ lake exe cache get
No files to download
Already decompressed 8010 file(s)

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches
⚠ [8046/8046] Built EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches (18s)
warning: EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean:87:8: declaration uses `sorry`
Build completed successfully (8046 jobs).
```

The audit-issue mentioned the expected sorry-warning location as
"line 153" — this referred to the #2933 file shape. The file has
grown to 960 lines through the cascade of case-fill PRs (#2956,
#2958, #2961, #2966, #2968's call-site update). The warning now
reports at line 87:8 (theorem header), which is the standard Lean
location for declaration-level sorry warnings. The two physical
`sorry` tokens in the file are:

- line 884 — Case C all-leaves residual at `chain.length = 4`,
  `x.deg = arm₁.deg = arm₂.deg = 1` (D̃₇-shaped); tracked by
  follow-up after #2968 lands `d7tilde_not_finite_type_per_kQ`.
- line 958 — Case E (`chain.length = 3`) + asymmetric short-chain +
  long-chain all-leaves residuals; tracked by #2955.

Both correspond to single transitive `declaration uses sorry`
warnings.

Dispatch readiness: the outer assembly
`non_adjacent_branches_infinite_type_per_kQ`
(`FieldGenericAssembly.lean:75`, audited in flight as #2944) calls
this helper three times at lines 160, 164, 168, each passing all 22
arguments in matching positional order including the new
`h_no_adj_branch_w` derived locally at lines 153-157. PASS.

## Notes for future planners

- Docstring at lines 28-30 is stale relative to PR #2968; a small
  refresh PR could list `d7tilde_not_finite_type_per_kQ` alongside
  the existing four per-kQ fixed-shape leaves.
- The audit-issue body (#2948) incorrectly attributes
  `h_v₀w_nonadj`, `h_leaf_adj`, `h_leaf_deg` to PR #2941; they were
  already in #2933. Future audits comparing #2933 ↔ #2941 should
  diff against `601f2ea`, not rely on the issue body's enumeration.

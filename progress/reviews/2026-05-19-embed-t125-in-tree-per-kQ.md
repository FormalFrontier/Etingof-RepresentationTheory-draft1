# Review: `embed_t125_in_tree_per_kQ` shared helper + both d₂/d₃-extends call sites

**Verdict: PASS** on all five deliverables. No code changes recommended.
No follow-up issues filed.

- Helper: `Chapter6/FieldGenericT125.lean:71-439` (introduced by PR
  #2917, merge commit `edbe14f`, 2026-05-18; reused by PR #2918, merge
  commit `9847ad1`, 2026-05-18).
- Universal reference: `Chapter6/InfiniteTypeConstructions.lean:4918-5279`.
- Issue: #2928 (this audit).
- Reviewed at `main` = `c86c23a` (the helper and both call sites are
  merged).
- Session: `5023485b`.

## D1 — Signature fidelity (PASS)

The 9-vertex T(1, 2, 5) embedding helper takes the same parameters in
the same order as the universal version, plus exactly the per-(F, Q)
carriage at the tail. Side-by-side:

| Parameter group | Universal (lines 4918-4935) | Per-(F, Q) (lines 71-87) |
|---|---|---|
| Implicit arity | `{n : ℕ}` | `{n : ℕ}` ✓ |
| Adjacency matrix | `(adj : Matrix (Fin n) (Fin n) ℤ)` | identical ✓ |
| Symmetry | `(hsymm : adj.IsSymm)` | identical ✓ |
| Diagonal | `(hdiag : ∀ i, adj i i = 0)` | identical ✓ |
| 0/1-valued | `(h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)` | identical ✓ |
| Acyclicity | `(h_acyclic : …)` (4923-4927) | identical (76-80) ✓ |
| 9 vertices | `(v₀ u₁ p₁ p₂ q₁ q₂ q₃ q₄ q₅ : Fin n)` | identical ✓ |
| 8 adjacencies | `hu₁ hp₁ hp₂ hq₁ hq₂ hq₃ hq₄ hq₅` (4929-4931) | identical (82-84) ✓ |
| 8 distinctness facts | `hu₁_ne_p₁ … hq₅_ne_q₃` (4933-4935) | identical (85-87) ✓ |

Per-(F, Q) appends the standard carriage at lines 88-91:

```lean
(F : Type) [Field F] [IsAlgClosed F]
(Q : @Quiver.{0, 0} (Fin n))
[∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
(hOrient : @Etingof.IsOrientationOf n Q adj)
```

This matches the carriage specified by issue #2928 verbatim. No extra
hypotheses, no missing distinctness facts. The 8 structurally-required
ne hypotheses match the universal version's pattern (level 1 from
v₀-emerging arms, level 2 for the far-end-vs-v₀ pairs, level 3 along
the long arm).

The universal helper is `private theorem`; the per-(F, Q) version is
public `theorem`. This is intentional — the per-(F, Q) helper is
exported and used from `FieldGenericTpqr.lean` (cross-file), whereas
the universal version is consumed only inside
`InfiniteTypeConstructions.lean`.

## D2 — Conclusion fidelity (PASS)

| | Universal (4936) | Per-(F, Q) (92-95) |
|---|---|---|
| Conclusion | `¬ Etingof.IsFiniteTypeQuiver n adj` | `¬ Set.Finite { d : Fin n → ℕ \| ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q, V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F)) }` |

The per-(F, Q) conclusion matches the conclusion shape of the sibling
per-(F, Q) leaves on `main`:

- `t125_not_finite_type_per_kQ` (`FieldGenericT125.lean:44-47`):
  same predicate, fixed at `Fin 9`.
- `etilde7_not_finite_type_per_kQ` (`FieldGenericETilde7.lean:301`):
  same predicate shape at `Fin 8`.
- `subgraph_infinite_type_transfer_per_kQ`
  (`FieldGenericInfiniteType.lean:385-389`): identical
  conclusion at `Fin n`.

The `@Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q` form with
the explicit universe levels and the `_` for the `Quiver` instance is
the canonical per-(F, Q) form across all per-(F, Q) leaves on `main`.
No drift.

## D3 — Embedding construction fidelity (PASS)

The body of `embed_t125_in_tree_per_kQ` (lines 96-436) is
**bit-identical** to the body of `embed_t125_in_tree` (lines 4937-5277).
Verified by `diff`:

```
$ diff <(sed -n '4937,5277p' InfiniteTypeConstructions.lean) \
       <(sed -n '96,436p' FieldGenericT125.lean)
# (no output — files identical, 341 lines each)
```

This covers:

- The `adj_comm` and `ne_of_adj'` lifts (lines 96-98).
- All 8 same-arm distinctness derivations from adjacency (100-107).
- The 7 reversed-edge facts (109-115).
- All 9 distance-2 non-edge derivations via `acyclic_no_triangle` (117-140).
- The 4-level cascade of cross-arm distinctness facts (142-148, 293-297,
  326-329, 357-359, 384).
- All distance-{3, 4, 5, 6, 7} non-edge derivations via `path_nodup{4–8}`
  and `path_edges{4–8}` and `acyclic_path_nonadj` (252-395).
- The `φ_fun : Fin 9 → Fin n` map (398-409) — with the same vertex
  assignment `0→v₀, 1→u₁, 2→p₁, 3→p₂, 4→q₁, 5→q₂, 6→q₃, 7→q₄, 8→q₅`
  (5238 / 397). No vertex swap.
- The injectivity proof (403-408) and `Fin 9 ↪ Fin n` packaging (409).
- The `hembed : ∀ i j, t125Adj i j = adj (φ i) (φ j)` proof, including
  the full 50-fact `linarith` argument list (410-436). The list of
  `adj_comm`, edge, and distance-{1–7} non-edge facts in lines 414-436
  is identical to the universal version's lines 5255-5277 — symmetry
  bookkeeping preserved exactly.

The only divergence between the two functions is the *final*
`exact …` line (one tactic), which is the dispatch and is audited
in D4 below. Everything that constructs the embedding object is
preserved byte-for-byte.

## D4 — Dispatch fidelity (PASS)

| | Universal (5278-5279) | Per-(F, Q) (437-439) |
|---|---|---|
| Closing tactic | `exact subgraph_infinite_type_transfer φ adj t125Adj hsymm (fun v h => by linarith [hdiag v]) hembed t125_not_finite_type` | `exact subgraph_infinite_type_transfer_per_kQ φ F Q (t125_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q) (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))` |

This is the expected port:

- Universal transfer `subgraph_infinite_type_transfer` takes
  `(φ, adj, adj_sub, hsymm_sub, hdiag_sub, hembed, infinite_subgraph)`
  and concludes infinite type on the ambient graph.
- Per-(F, Q) transfer `subgraph_infinite_type_transfer_per_kQ`
  (`FieldGenericInfiniteType.lean:374-389`) takes
  `(φ, F, Q, h_inf)` where `h_inf` is "infinite indecomposable
  dimension vectors for the restricted orientation". The subgraph's
  `adj` and adjacency-matrix invariants are not passed explicitly
  because the conclusion of `t125_not_finite_type_per_kQ` is already
  in the right form (it concludes for `t125Adj` directly).
- `t125_not_finite_type_per_kQ`
  (`FieldGenericT125.lean:39-47`) takes `F`, the orientation on the
  subgraph, and a proof `IsOrientationOf _ t125Adj`. This is exactly
  what is supplied:
  `restrictOrientationViaEmb φ Q` and
  `restrictOrientationViaEmb_isOrientationOf φ hembed hOrient`.
- `restrictOrientationViaEmb_isOrientationOf`
  (`FieldGenericInfiniteType.lean:345-361`) takes
  `(φ, hembed : ∀ i j, adj_sub i j = adj (φ i) (φ j), hOrient)` —
  the `hembed` it expects is exactly the form already constructed
  inside the body (`∀ i j, t125Adj i j = adj (φ i) (φ j)`). The
  `adj_sub` is inferred as `t125Adj` from the goal context.

Argument threading is in the same order as the universal trio
(transfer → leaf → orientation-restriction), with no swaps and with
`F`, `Q`, `hOrient` consistently propagated from the outer binder.

## D5 — Call-site fidelity (PASS, both uses)

Two call sites on `main`, identified via
`Grep "embed_t125_in_tree_per_kQ"`:

1. **d₂-extends in `single_branch_leaf_both_extend_b3leaf_per_kQ`**
   (`Chapter6/FieldGenericTpqr.lean:607-612`, introduced by PR #2917).
2. **d₃-extends in `single_branch_leaf_both_extend_b2leaf_per_kQ`**
   (`Chapter6/FieldGenericTpqr.lean:971-976`, introduced by PR #2918).

### Call site 1 (lines 607-612, d₂-extends)

```lean
exact embed_t125_in_tree_per_kQ adj hsymm hdiag h01 h_acyclic
    v₀ leaf a₃ b₃ a₂ b₂ c₂ d₂ e₂
    h_leaf_adj ha₃_adj hb₃_adj ha₂_adj hb₂_adj hc₂_adj hd₂_adj he₂_adj
    ha₃_ne_leaf.symm ha₂_ne_leaf.symm ha₂₃.symm hb₃_ne_v₀ hb₂_ne_v₀
    hc₂_ne_a₂ hd₂_ne_b₂ he₂_ne_c₂
    F Q hOrient
```

Vertex renaming `(v₀, u₁, p₁, p₂, q₁, q₂, q₃, q₄, q₅) ↦ (v₀, leaf, a₃, b₃, a₂, b₂, c₂, d₂, e₂)`.
The two arms are: `p`-arm of length 2 = `a₃-b₃` (the side branch's
neighbour and its extension), `q`-arm of length 5 = `a₂-b₂-c₂-d₂-e₂`
(the main branch's extension under `h_d2_ext`).

Verification by position:

| Helper parameter | Expected | Passed | Verdict |
|---|---|---|---|
| `hu₁ : adj v₀ u₁ = 1` | `adj v₀ leaf = 1` | `h_leaf_adj` | ✓ |
| `hp₁ : adj v₀ p₁ = 1` | `adj v₀ a₃ = 1` | `ha₃_adj` | ✓ |
| `hp₂ : adj p₁ p₂ = 1` | `adj a₃ b₃ = 1` | `hb₃_adj` | ✓ |
| `hq₁ : adj v₀ q₁ = 1` | `adj v₀ a₂ = 1` | `ha₂_adj` | ✓ |
| `hq₂ : adj q₁ q₂ = 1` | `adj a₂ b₂ = 1` | `hb₂_adj` | ✓ |
| `hq₃ : adj q₂ q₃ = 1` | `adj b₂ c₂ = 1` | `hc₂_adj` | ✓ |
| `hq₄ : adj q₃ q₄ = 1` | `adj c₂ d₂ = 1` | `hd₂_adj` | ✓ |
| `hq₅ : adj q₄ q₅ = 1` | `adj d₂ e₂ = 1` | `he₂_adj` | ✓ |
| `hu₁_ne_p₁ : u₁ ≠ p₁` | `leaf ≠ a₃` | `ha₃_ne_leaf.symm` | ✓ |
| `hu₁_ne_q₁ : u₁ ≠ q₁` | `leaf ≠ a₂` | `ha₂_ne_leaf.symm` | ✓ |
| `hp₁_ne_q₁ : p₁ ≠ q₁` | `a₃ ≠ a₂` | `ha₂₃.symm` (where `ha₂₃ : a₂ ≠ a₃`) | ✓ |
| `hp₂_ne_v₀ : p₂ ≠ v₀` | `b₃ ≠ v₀` | `hb₃_ne_v₀` | ✓ |
| `hq₂_ne_v₀ : q₂ ≠ v₀` | `b₂ ≠ v₀` | `hb₂_ne_v₀` | ✓ |
| `hq₃_ne_q₁ : q₃ ≠ q₁` | `c₂ ≠ a₂` | `hc₂_ne_a₂` | ✓ |
| `hq₄_ne_q₂ : q₄ ≠ q₂` | `d₂ ≠ b₂` | `hd₂_ne_b₂` | ✓ |
| `hq₅_ne_q₃ : q₅ ≠ q₃` | `e₂ ≠ c₂` | `he₂_ne_c₂` | ✓ |

`F Q hOrient` is threaded from the outer `single_branch_leaf_both_extend_b3leaf_per_kQ` binder; the `[IsAlgClosed F]` and `[Subsingleton …]` instances flow through. ✓

### Call site 2 (lines 971-976, d₃-extends)

```lean
exact embed_t125_in_tree_per_kQ adj hsymm hdiag h01 h_acyclic
    v₀ leaf a₂ b₂ a₃ b₃ c₃ d₃ e₃
    h_leaf_adj ha₂_adj hb₂_adj ha₃_adj hb₃_adj hc₃_adj hd₃_adj he₃_adj
    ha₂_ne_leaf.symm ha₃_ne_leaf.symm ha₂₃ hb₂_ne_v₀ hb₃_ne_v₀
    hc₃_ne_a₃ hd₃_ne_b₃ he₃_ne_c₃
    F Q hOrient
```

Vertex renaming `(v₀, u₁, p₁, p₂, q₁, q₂, q₃, q₄, q₅) ↦ (v₀, leaf, a₂, b₂, a₃, b₃, c₃, d₃, e₃)` — the symmetric counterpart to call site 1: the
two arms swap (now `p`-arm = `a₂-b₂` is the side branch, `q`-arm =
`a₃-b₃-c₃-d₃-e₃` is the main branch extended under `h_d3_ext`).

Verification by position:

| Helper parameter | Expected | Passed | Verdict |
|---|---|---|---|
| `hu₁ : adj v₀ u₁ = 1` | `adj v₀ leaf = 1` | `h_leaf_adj` | ✓ |
| `hp₁ : adj v₀ p₁ = 1` | `adj v₀ a₂ = 1` | `ha₂_adj` | ✓ |
| `hp₂ : adj p₁ p₂ = 1` | `adj a₂ b₂ = 1` | `hb₂_adj` | ✓ |
| `hq₁ : adj v₀ q₁ = 1` | `adj v₀ a₃ = 1` | `ha₃_adj` | ✓ |
| `hq₂ : adj q₁ q₂ = 1` | `adj a₃ b₃ = 1` | `hb₃_adj` | ✓ |
| `hq₃ : adj q₂ q₃ = 1` | `adj b₃ c₃ = 1` | `hc₃_adj` | ✓ |
| `hq₄ : adj q₃ q₄ = 1` | `adj c₃ d₃ = 1` | `hd₃_adj` | ✓ |
| `hq₅ : adj q₄ q₅ = 1` | `adj d₃ e₃ = 1` | `he₃_adj` | ✓ |
| `hu₁_ne_p₁ : u₁ ≠ p₁` | `leaf ≠ a₂` | `ha₂_ne_leaf.symm` | ✓ |
| `hu₁_ne_q₁ : u₁ ≠ q₁` | `leaf ≠ a₃` | `ha₃_ne_leaf.symm` | ✓ |
| `hp₁_ne_q₁ : p₁ ≠ q₁` | `a₂ ≠ a₃` | `ha₂₃` (bare, since renaming places `a₂` in `p₁` slot here) | ✓ |
| `hp₂_ne_v₀ : p₂ ≠ v₀` | `b₂ ≠ v₀` | `hb₂_ne_v₀` | ✓ |
| `hq₂_ne_v₀ : q₂ ≠ v₀` | `b₃ ≠ v₀` | `hb₃_ne_v₀` | ✓ |
| `hq₃_ne_q₁ : q₃ ≠ q₁` | `c₃ ≠ a₃` | `hc₃_ne_a₃` | ✓ |
| `hq₄_ne_q₂ : q₄ ≠ q₂` | `d₃ ≠ b₃` | `hd₃_ne_b₃` | ✓ |
| `hq₅_ne_q₃ : q₅ ≠ q₃` | `e₃ ≠ c₃` | `he₃_ne_c₃` | ✓ |

Cross-check between call sites: `ha₂₃ : a₂ ≠ a₃` is the same fact in
both files (no asymmetric ne convention). Call site 1 places `a₃` in
the `p₁` slot and `a₂` in the `q₁` slot, so it needs `a₃ ≠ a₂` and
passes `ha₂₃.symm`. Call site 2 places `a₂` in the `p₁` slot and `a₃`
in the `q₁` slot, so it needs `a₂ ≠ a₃` and passes `ha₂₃` directly.
Consistent. ✓

`F Q hOrient` is threaded from `single_branch_leaf_both_extend_b2leaf_per_kQ`'s outer binder. ✓

## Build sanity

`lake build EtingofRepresentationTheory.Chapter6.FieldGenericT125 EtingofRepresentationTheory.Chapter6.FieldGenericTpqr` from `main` (`c86c23a`) completes (8045 jobs). The only non-warning is a pre-existing
`sorry` at `FieldGenericTpqr.lean:1233`, unrelated to the helper or its
two call sites. A handful of `linter.unusedSimpArgs` style warnings
elsewhere in `FieldGenericTpqr.lean` (lines 455, etc.) are also
pre-existing and untouched by PRs #2917 / #2918.

## Future-impact note (informational, no action)

The universal `embed_t125_in_tree` is invoked four times in the
universal infinite-type pipeline
(`InfiniteTypeConstructions.lean:7373, 7380, 7679, 7686`). The
per-(F, Q) helper currently supports two of those four call patterns
(both d-extends slots inside `single_branch_leaf_both_extend_*`). The
helper is structurally ready to support the other two (the
`b3leaf_per_kQ` and `b2leaf_per_kQ` siblings that PR #2911 / the
sub-A line will queue) without modification: signature, dispatch, and
embedding are all general over `(F, Q)` and the 9-vertex T(1, 2, 5)
data. No drift was found that would block those future call sites.

## Summary table

| Deliverable | Verdict | Recommendation |
|---|---|---|
| D1 Signature fidelity | PASS | none |
| D2 Conclusion fidelity | PASS | none |
| D3 Embedding construction fidelity | PASS (bit-identical body) | none |
| D4 Dispatch fidelity | PASS | none |
| D5 Call-site fidelity (both uses) | PASS | none |

No fix issues filed.

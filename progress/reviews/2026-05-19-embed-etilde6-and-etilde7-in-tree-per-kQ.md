# Audit: `embed_etilde6/etilde7_in_tree_per_kQ` bodies (PRs #2945 + #2947)

Issue: #2949. Combined audit of the Ẽ₆ and Ẽ₇ embedder helpers
introduced as stubs in PR #2941 and filled in PRs #2945 (Ẽ₆) and
#2947 (Ẽ₇).

## Subjects

| | Ẽ₆ helper | Ẽ₇ helper |
|---|---|---|
| File | `Chapter6/FieldGenericETilde6.lean` | `Chapter6/FieldGenericETilde7.lean` |
| Theorem | `embed_etilde6_in_tree_per_kQ` (line 372) | `embed_etilde7_in_tree_per_kQ` (line 356) |
| Body PR | #2945 (merge `aaaaaad`, +279/-15) | #2947 (merge `23e7a62`, +347/-19) |
| Shape | T(2, 2, 2), 7 vertices, 6 edges | T(1, 3, 3), 8 vertices, 7 edges |
| `Fin` arity | 7 | 8 |

Both bodies are written to the `embed_t125_in_tree_per_kQ` pattern
(`FieldGenericT125.lean:71`), which has been audited PASS by #2928
(`progress/reviews/2026-05-19-embed-t125-in-tree-per-kQ.md`). Unlike
T(1, 2, 5), neither has a universal counterpart in
`InfiniteTypeConstructions.lean` — these are genuinely new per-(F, Q)
constructions following the T125 template, not line-cloned copies.

## D1 — Signature fidelity to PR #2941 stub

Compared the on-`main` signatures to the stub introduced by PR #2941
(commit `6fc9d40`, hand-extracted via `git show
6fc9d40:EtingofRepresentationTheory/Chapter6/FieldGenericETilde{6,7}.lean`).

| Stub vs. landed | Ẽ₆ | Ẽ₇ |
|---|---|---|
| `{n}`, `adj`, `hsymm`, `hdiag`, `h01`, `h_acyclic` | identical | identical |
| Vertex tuple | `v₀ c₁ d₁ c₂ d₂ c₃ d₃` (7) | `v₀ u₁ c₂ d₂ e₂ c₃ d₃ e₃` (8) |
| Edge hypotheses | 6: `hc₁ hd₁ hc₂ hd₂ hc₃ hd₃` | 7: `hu₁ hc₂ hd₂ he₂ hc₃ hd₃ he₃` |
| Same-level distinctness | 3: `hc₁_ne_c₂ hc₁_ne_c₃ hc₂_ne_c₃` | 3: `hu₁_ne_c₂ hu₁_ne_c₃ hc₂_ne_c₃` |
| Leaf-side distinctness | 3: `hd₁_ne_v₀ hd₂_ne_v₀ hd₃_ne_v₀` | 2 + 2: `hd₂_ne_v₀ hd₃_ne_v₀ he₂_ne_c₂ he₃_ne_c₃` |
| `F`, `Q`, subsingleton, `hOrient` | identical | identical |
| Conclusion type | identical | identical |

**Verdict (D1, both): PASS.** Every named parameter in the stub appears
in the landed body, in the same order, with the same type. No
hypotheses added, removed, or renamed.

## D2 — Distinctness lattice exhaustiveness

### Ẽ₆ (`FieldGenericETilde6.lean:413-524`)

7 vertices → C(7, 2) = 21 pairs. The lattice derives:

| Class | Count | Locations | Pairs |
|---|---|---|---|
| Same-arm edges | 6 | hypotheses + `adj_comm` (407-412) | `(v₀,cᵢ)`, `(cᵢ,dᵢ)` for i=1,2,3 |
| Triangle non-edges | 6 | `acyclic_no_triangle` 413-432 | `v₀-dᵢ` (3, apex cᵢ); `cᵢ-cⱼ` (3, apex v₀) |
| Distance-3 non-edges | 6 | `acyclic_path_nonadj` 475-504 | `cᵢ-dⱼ` for i≠j |
| Distance-4 non-edges | 3 | `acyclic_path_nonadj` 510-524 | `dᵢ-dⱼ` for i≠j |
| **Total** | **21** | | matches C(7, 2) |

Cross-arm `≠` facts are derived in two waves (434-439, 506-508) by
rewriting an edge hypothesis against a freshly-proven non-edge, before
they are consumed in the next wave of `acyclic_path_nonadj` calls.

Spot-check (apex/witness threading, `acyclic_no_triangle (v a b) (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (ha) (hb)`):

- `hv₀d₁` (414-416): apex `c₁`, a=`v₀`, b=`d₁`. Args:
  `hd₁_ne_v₀.symm` (v₀≠d₁), `hv₀_ne_c₁` (v₀≠c₁), `hc₁_ne_d₁.symm`
  (d₁≠c₁), `hc₁_v₀` (adj c₁ v₀=1), `hd₁` (adj c₁ d₁=1). ✓
- `hc₁c₂` (424-426): apex `v₀`, a=`c₁`, b=`c₂`. Args:
  `hc₁_ne_c₂` (c₁≠c₂), `hv₀_ne_c₁.symm` (c₁≠v₀), `hv₀_ne_c₂.symm`
  (c₂≠v₀), `hc₁` (adj v₀ c₁=1), `hc₂` (adj v₀ c₂=1). ✓
- `hc₁d₂` (475-479): path `[d₂, c₂, v₀, c₁]`, last=c₁, first=d₂ →
  proves `adj c₁ d₂ = 0`. Edges `hd₂_c₂, hc₂_v₀, hc₁`. ✓
- `hd₁d₂` (510-514): path `[d₂, c₂, v₀, c₁, d₁]`, last=d₁, first=d₂ →
  proves `adj d₁ d₂ = 0`. Edges `hd₂_c₂, hc₂_v₀, hc₁, hd₁`. ✓

**Verdict (D2 / Ẽ₆): PASS.**

### Ẽ₇ (`FieldGenericETilde7.lean:400-601`)

8 vertices → C(8, 2) = 28 pairs.

| Class | Count | Locations | Pairs |
|---|---|---|---|
| Edges | 7 | hypotheses + `adj_comm` (393-399) | `(v₀,u₁), (v₀,cᵢ), (cᵢ,dᵢ), (dᵢ,eᵢ)` |
| Triangle non-edges | 7 | 402-424 | `u₁-cᵢ` (apex v₀, 2), `cᵢ-cⱼ` (apex v₀, 1), `v₀-dᵢ` (apex cᵢ, 2), `cᵢ-eᵢ` (apex dᵢ, 2) |
| Distance-3 non-edges | 6 | 512-541 | `u₁-dᵢ`, `dᵢ-cⱼ` (i≠j), `v₀-eᵢ` |
| Distance-4 non-edges | 5 | 549-573 | `u₁-eᵢ`, `dᵢ-dⱼ`, `cᵢ-eⱼ` (i≠j, 2 of 4 needed) |
| Distance-5 non-edges | 2 | 579-590 | `dᵢ-eⱼ` (i≠j) |
| Distance-6 non-edges | 1 | 594-601 | `e₂-e₃` |
| **Total** | **28** | | matches C(8, 2) |

Lines 350-352 of the docstring announce the exact same distribution
(7 + 6 + 5 + 2 + 1 = 21 non-edges).

Spot-checks:

- `hc₂e₂` (419-421): apex `d₂`, a=`c₂`, b=`e₂`. Args:
  `he₂_ne_c₂.symm` (c₂≠e₂), `hc₂_ne_d₂` (c₂≠d₂), `hd₂_ne_e₂.symm`
  (e₂≠d₂), `hd₂_c₂` (adj d₂ c₂=1), `he₂` (adj d₂ e₂=1). ✓
- `hv₀e₂` (532-536): path `[e₂, d₂, c₂, v₀]`, last=v₀, first=e₂ →
  proves `adj v₀ e₂ = 0`. Edges `he₂_d₂, hd₂_c₂, hc₂_v₀`. ✓
- `he₂c₃` (569-573): path `[c₃, v₀, c₂, d₂, e₂]`, last=e₂, first=c₃
  → proves `adj e₂ c₃ = 0`. Edges `hc₃_v₀, hc₂, hd₂, he₂`. ✓
- `he₂e₃` (594-601, the 7-vertex path): path
  `[e₃, d₃, c₃, v₀, c₂, d₂, e₂]`, last=e₂, first=e₃ → proves
  `adj e₂ e₃ = 0`. The 21-pair `path_nodup7` argument list verified
  exhaustively (a=e₃, b=d₃, c=c₃, d=v₀, e=c₂, f=d₂, g=e₂; every pair
  `(x, y)` for x<y in `[a,b,c,d,e,f,g]` is covered with the correct
  `.symm` orientation). Edges `he₃_d₃, hd₃_c₃, hc₃_v₀, hc₂, hd₂, he₂`. ✓

**Verdict (D2 / Ẽ₇): PASS.**

## D3 — Embedding map + injectivity + `hembed`

`etilde6Adj` definition (`InfiniteTypeConstructions.lean:1246-1250`):
edges = `{(0,1), (1,2), (0,3), (3,4), (0,5), (5,6)}`. Map
`0→v₀, 1→c₁, 2→d₁, 3→c₂, 4→d₂, 5→c₃, 6→d₃` sends:

- (0,1) → (v₀, c₁) needs `adj v₀ c₁ = 1` — `hc₁`. ✓
- (1,2) → (c₁, d₁) needs `adj c₁ d₁ = 1` — `hd₁`. ✓
- (0,3) → (v₀, c₂) needs `adj v₀ c₂ = 1` — `hc₂`. ✓
- (3,4) → (c₂, d₂) needs `adj c₂ d₂ = 1` — `hd₂`. ✓
- (0,5) → (v₀, c₃) needs `adj v₀ c₃ = 1` — `hc₃`. ✓
- (5,6) → (c₃, d₃) needs `adj c₃ d₃ = 1` — `hd₃`. ✓

Non-edges: all other 15 pairs map to non-edges established in D2.

`etilde7Adj` definition (`InfiniteTypeConstructions.lean:3435-3440`):
edges = `{(0,1), (0,2), (2,3), (3,4), (0,5), (5,6), (6,7)}`. Map
`0→v₀, 1→u₁, 2→c₂, 3→d₂, 4→e₂, 5→c₃, 6→d₃, 7→e₃` sends:

- (0,1) → (v₀, u₁) — `hu₁`. ✓
- (0,2) → (v₀, c₂) — `hc₂`. ✓
- (2,3) → (c₂, d₂) — `hd₂`. ✓
- (3,4) → (d₂, e₂) — `he₂`. ✓
- (0,5) → (v₀, c₃) — `hc₃`. ✓
- (5,6) → (c₃, d₃) — `hd₃`. ✓
- (6,7) → (d₃, e₃) — `he₃`. ✓

Both `φ_fun` definitions are total `match`-on-`Fin.val` exhausting all
indices (`FieldGenericETilde6.lean:527-531`, `…ETilde7.lean:604-608`).
Injectivity proof: `fin_cases i <;> fin_cases j <;> first | rfl |
absurd hij ‹_› | absurd hij.symm ‹_›`, relying on the (in-context)
distinctness lattice from D2. Since D2 derives every cross-pair `≠`,
the `‹_›` resolution closes every off-diagonal case.

`hembed` proof: 49-case (Ẽ₆) / 64-case (Ẽ₇) `fin_cases <;>
simp only [etildeNAdj, φ, φ_fun] <;> norm_num <;> linarith [...]`
with curated fact lists. Spot-checked the fact lists exhaustively:

- Ẽ₆ list (543-556): 7 `hdiag`, 6 edges, 21 `adj_comm`, 6 triangle +
  6 distance-3 + 3 distance-4 = 15 non-edges. Matches D2 inventory. ✓
- Ẽ₇ list (620-637): 8 `hdiag`, 7 edges, 28 `adj_comm`, 7 + 6 + 5 +
  2 + 1 = 21 non-edges. Matches D2 inventory. ✓

The successful build (D5) confirms `linarith` closes every case.

**Verdict (D3, both): PASS.**

## D4 — Dispatch chain shape

Both bodies close with the same shape (`FieldGenericETilde6.lean:557-559`,
`FieldGenericETilde7.lean:638-640`):

```lean
exact subgraph_infinite_type_transfer_per_kQ φ F Q
  (etildeN_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
    (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))
```

Compared against the audited template at
`FieldGenericT125.lean:437-439`:

```lean
exact subgraph_infinite_type_transfer_per_kQ φ F Q
  (t125_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
    (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))
```

Only the leaf differs: `t125_not_finite_type_per_kQ` →
`etilde6_not_finite_type_per_kQ` / `etilde7_not_finite_type_per_kQ`.

Signatures cross-checked:

- `subgraph_infinite_type_transfer_per_kQ`
  (`FieldGenericInfiniteType.lean:374`): `(φ : Fin m ↪ Fin n) (F : Type)
  [Field F] (Q : Quiver (Fin n)) [subsingleton] (h_inf : …) : ¬ Set.Finite
  {d : Fin n → ℕ | … Q …}` — both helpers pass `φ : Fin {7,8} ↪ Fin n`,
  `F`, `Q`, then the leaf result. ✓
- `restrictOrientationViaEmb_isOrientationOf`
  (`FieldGenericInfiniteType.lean:345`): takes `φ`, `hembed : ∀ i j,
  adj_sub i j = adj (φ i) (φ j)`, `hOrient`. Both helpers thread
  `hembed : ∀ i j, etildeNAdj i j = adj (φ i) (φ j)` (D3) and the
  caller-supplied `hOrient` unchanged. ✓
- `etilde6_not_finite_type_per_kQ` (`FieldGenericETilde6.lean:319`)
  and `etilde7_not_finite_type_per_kQ` (`FieldGenericETilde7.lean:301`):
  both take `(F)(Q : Quiver (Fin {7,8}))(hOrient : IsOrientationOf Q
  etildeNAdj)` and return the infinite-set conclusion on `Fin {7,8}`.
  The `Q` argument is supplied as `restrictOrientationViaEmb φ Q`
  (`Quiver (Fin {7,8})`), and the `hOrient` argument as the orientation
  derived by `restrictOrientationViaEmb_isOrientationOf`. ✓

**Verdict (D4, both): PASS.**

## D5 — Targeted builds

Built from a fresh checkout on `main` = `7e4a8ab` (which is a
descendant of merge commits `aaaaaad` and `23e7a62`):

```
$ lake exe cache get
Using cache (Azure) from origin: leanprover-community/mathlib4
No files to download
Already decompressed 8010 file(s)

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericETilde6
…
warning: EtingofRepresentationTheory/Chapter6/FieldGenericETilde6.lean:291:8: declaration uses `sorry`
Build completed successfully (8042 jobs).

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericETilde7
…
warning: EtingofRepresentationTheory/Chapter6/FieldGenericETilde7.lean:273:8: declaration uses `sorry`
Build completed successfully (8043 jobs).
```

Captured logs at `/tmp/build-etilde6.log`, `/tmp/build-etilde7.log`.

Sorries remaining:

| File | Line | Declaration | Status |
|---|---|---|---|
| `FieldGenericETilde6.lean` | 291 (matches issue's 266-289 docstring band) | `etilde6Rep_kQ_isIndecomposable` | pre-existing wave-54 framework wall |
| `FieldGenericETilde7.lean` | 273 (matches issue's 247-271 docstring band) | `etilde7Rep_kQ_isIndecomposable` | pre-existing wave-54 framework wall |

No new sorries introduced by either PR; the only remaining sorries
match exactly the pre-existing ones flagged by the issue body's D5
expectations.

The two unrelated style-linter warnings on
`FieldGenericStar.lean:160` (maxHeartbeats, unscoped option) and the
`sorry` warning on `FieldGenericStar.lean:543` are also pre-existing
and unrelated to either PR.

**Verdict (D5, both): PASS.**

## Combined verdict

| Dimension | Ẽ₆ (#2945) | Ẽ₇ (#2947) |
|---|---|---|
| D1 — Signature fidelity | **PASS** | **PASS** |
| D2 — Distinctness lattice | **PASS** | **PASS** |
| D3 — Embedding + injectivity + hembed | **PASS** | **PASS** |
| D4 — Dispatch chain | **PASS** | **PASS** |
| D5 — Build green, no new sorries | **PASS** | **PASS** |

Both PRs land clean, structurally faithful copies of the T(1, 2, 5)
template tuned to the T(2, 2, 2) and T(1, 3, 3) shapes. The shared
`path_nodup{4..7}` / `path_edges{4..7}` helpers are kept local to each
file (intentional, per the commit messages — avoids widening shared
API for a single use-site); a follow-up could lift them into
`FieldGenericInfiniteType.lean` if a fourth caller appears.

No follow-up issues required.

## Notes for future audits

- The Ẽ₇ `path_nodup7` invocation at line 596-601 has 21 pairwise
  distinctness arguments in canonical order
  (a≠b, a≠c, …, a≠g, b≠c, …, f≠g). Manual verification is tedious
  but mechanical; a small Lean tactic that orders these arguments
  by `Fin`-index would catch transposition errors at definition
  time. Not raised as an issue — the current body builds, so any
  such error is already caught.
- The local `path_nodup{4..7}` / `path_edges{4..7}` helpers now
  appear in three places (`FieldGenericT125.lean`,
  `FieldGenericETilde6.lean`, `FieldGenericETilde7.lean`). A fourth
  copy would be a clear signal to lift them. Two more upcoming
  callers from sibling Ẽ₈ / Ẽ₉ work would tip the balance.

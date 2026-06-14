# Review: Case C.short residual + per-(F, Q) D̃₇ helper (PRs #2966, #2968, #2970)

**Issue:** https://github.com/kim-em/Etingof-RepresentationTheory-draft1/issues/2973
**PRs audited:**
- #2966 (Case C.short tractable sub-cases, merge `1b4e901`)
- #2968 (per-(F, Q) D̃₇ helper, merge `6c7e6e4`)
- #2970 (Case C.short all-leaves residual via D̃₇ dispatch, merge `7e4a8ab`)

**Audited commit:** `2a9398f` (current `main`)
**Target files:**
- `EtingofRepresentationTheory/Chapter6/FieldGenericD7Tilde.lean`
- `EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean`
- `EtingofRepresentationTheory/Chapter6.lean`

## Summary

| Dim | #2966 | #2968 | #2970 |
|-----|:-----:|:-----:|:-----:|
| D1 D̃₇ module fidelity to D̃₅ precedent | n/a | **PASS** | n/a |
| D2 Case C.short dispatch coverage      | **PASS** | n/a   | n/a |
| D3 embed_d7tilde helper + dispatch     | n/a | n/a   | **PASS** |
| D4 build sanity (combined)             | **PASS** | **PASS** | **PASS** |
| D5 cross-file consistency (combined)   | **CONCERN** | **CONCERN** | **CONCERN** |

No build-breaking issues. No code changes pushed.

## D1 — D̃₇ module structural fidelity (PR #2968): **PASS**

`Chapter6/FieldGenericD7Tilde.lean` (578 lines, new file) is a faithful
adaptation of the `Chapter6/FieldGenericD5Tilde.lean` precedent to the
extended-Dynkin D̃₇ shape (8 vertices, two non-adjacent degree-3
branch points joined by a length-3 internal chain).

**(a) `d7tildeAdj` shape**
(`FieldGenericD7Tilde.lean:60-68`). 7 undirected edges encoded as 14
`match`-arms returning `1`:
- left-leaves `0-2`, `1-2` (vertex 2 is left branch point),
- internal chain `2-3`, `3-4`, `4-5`,
- right-leaves `5-6`, `5-7` (vertex 5 is right branch point).

Matches the `dTildeQuiver 2` shape from
`InfiniteTypeConstructions.lean:2003-2011` (with `k+6 = 8`, `k+3 = 5`,
`k+4 = 6`, `k+5 = 7`). The choice of `match`-form for adjacency
(vs the `if`-chain in `d5tildeAdj` at `InfiniteTypeConstructions.lean:
1369-1376`) is a stylistic improvement — explicit cases are easier to
audit. The 8-vertex degree pattern is `(1, 1, 3, 2, 2, 3, 1, 1)`,
consistent with two degree-3 branch points + four leaves + two interior
chain vertices.

**(b) `_symm` / `_diag` / `_01`**
(`FieldGenericD7Tilde.lean:70-79`). All three discharge by `fin_cases`
on `Fin 8`, giving 64-, 8-, and 64-case decidable simp. No typo can
hide here — the proofs reduce mechanically. Equivalent to D̃₅'s
proofs (`InfiniteTypeConstructions.lean:1378-1389`).

**(c) `d7tildeQuiver` + `_subsingleton` + `_isOrientationOf`**
(`FieldGenericD7Tilde.lean:86-126`). Canonical sink orientation
arrows: `0→2, 1→2, 2→3, 3→4, 4→5, 6→5, 7→5`. Each leaf points
inward to its branch point; the internal chain runs left-to-right.
This matches `dTildeArrowPred 2` (with `k+3=5`, `k+4=6`, `k+5=7`)
from `InfiniteTypeConstructions.lean:2040-2043`. The
`d7tildeOrientation_isOrientationOf` proof:
- Non-edges: via an extracted helper
  `d7tilde_arrow_implies_edge` (`FieldGenericD7Tilde.lean:97-105`),
  cleaner than D̃₅'s inline `simp [d5tildeAdj] at hij`.
- Edge-has-arrow: `fin_cases i <;> fin_cases j` followed by
  `simp [d7tildeAdj] at hij` and a `first | (left; ...) | (right; ...)`
  dispatch. 64 cases reduced mechanically.
- Antisymmetry: 7×7 = 49 `rcases` pairs discharged by `omega` — same
  pattern as D̃₅ (`InfiniteTypeConstructions.lean:1442-1444`).

The signature `@Etingof.IsOrientationOf 8 d7tildeQuiver d7tildeAdj`
matches `d5tildeOrientation_isOrientationOf` exactly (with `6 → 8`).

**(d) `d7tildeRepMap_kQ` direction-awareness**
(`FieldGenericD7Tilde.lean:156-181`). 14 directed-edge match-arms, one
per `(a, b)` direction of each of the 7 undirected edges, plus a
catch-all `0` for non-edges:

| Edge          | Canonical (`a→b` in `d7tildeQuiver`)    | Reverse                  |
|---------------|----------------------------------------|--------------------------|
| `{0,2}` (leaf) | `0→2 = starEmbed1_F`                   | `2→0 = starFirst_F`      |
| `{1,2}` (leaf) | `1→2 = starEmbed2_F`                   | `2→1 = starSecond_F`     |
| `{2,3}` (γ)   | `2→3 = d5tildeGamma_F`                  | `3→2 = d5tildeGammaInv_F`|
| `{3,4}` (chain)| `3→4 = LinearMap.id`                   | `4→3 = LinearMap.id`     |
| `{4,5}` (chain)| `4→5 = LinearMap.id`                   | `5→4 = LinearMap.id`     |
| `{5,6}` (leaf) | `6→5 = starEmbed1_F`                   | `5→6 = starFirst_F`      |
| `{5,7}` (leaf) | `7→5 = starEmbed2_F`                   | `5→7 = starSecond_F`     |

The canonical leaf edges reuse `starEmbed{1,2}_F` from
`FieldGenericStar.lean` (consistent with D̃₅ at
`FieldGenericD5Tilde.lean:141-160`). The leaf-edge reverses use the
plain `starFirst_F` / `starSecond_F` projections, consistent with the
post-#2846 D̃₅ pattern (which moved from the K_{1,4}-specific
`starProj1_F` / `starProj2_F` to the plain projections).

The internal-chain edges `{3,4}` and `{4,5}` use `LinearMap.id` in
**both** directions. This is mathematically sound: chain edges in
D̃_n are between equal-dimension blocks `Fin (2(m+1)) → F`, so the
canonical map is identity and the reverse is identity (`I⁻¹ = I`).
This matches the universal `dTildeRep`'s prescription at
`InfiniteTypeConstructions.lean:2092` ("`i→(i+1)` for `i=3,...,k+2`:
identity").

The new central γ-edge `{2,3}` reuses `d5tildeGamma_F` and
`d5tildeGammaInv_F` from `FieldGenericD5Tilde.lean` directly. The
D̃₇ shape has the *same* central γ-edge as D̃₅ — both have exactly
one γ-edge at the left branch's outgoing chain step, with the rest
being identities. Reuse is correct.

**(e) Sorry count**
(`FieldGenericD7Tilde.lean:254`). Exactly one `sorry`:
`d7tildeRep_kQ_isIndecomposable`. The follow-up issue
https://github.com/kim-em/Etingof-RepresentationTheory-draft1/issues/2967
is open, titled `feat(Ch6 #2964 follow-up): fill d7tildeRep_kQ_isIndecomposable proof body`.
The downstream `d7tilde_not_finite_type_per_kQ`
(`FieldGenericD7Tilde.lean:272-298`) carries this sorry transitively,
properly documented in its docstring. The downstream
`embed_d7tilde_in_tree_per_kQ` (Section 7) also carries this sorry
transitively. This precisely mirrors the D̃₅ precedent
(`d5tildeRep_kQ_isIndecomposable` at `FieldGenericD5Tilde.lean:974`,
sorry at line 981, tracked by #2834).

**Minor docstring nit (non-blocking):**
- `FieldGenericD7Tilde.lean:41`, `230`: the cross-reference to
  D̃₅'s indecomposability proof claims line 980, but the actual
  declaration starts at `FieldGenericD5Tilde.lean:974` (sorry at 981).
  Off by ±6 lines.

## D2 — Case C.short dispatch coverage (PR #2966): **PASS**

The C.short residual at
`FieldGenericNonAdjacentBranches.lean:699-895` (within Case C,
`637-895`) splits the `vertexDegree adj x ≠ 2` branch into the
following decision tree, where `x` is `side_arm`'s unique non-`v₀`
neighbour and Case C's hypothesis is
`4 ≤ chain.length ∧ chain.length < 6 ∧ vertexDegree adj side_arm = 2`:

```
C.short (¬ hxdeg: x.deg ≠ 2)
├── hxdeg3: x.deg = 3       → Ẽ₇ at v₀ via embed_etilde7_in_tree_per_kQ
└── ¬hxdeg3: x.deg = 1
    ├── hlen5: chain.length = 5    → T(1,2,5) at v₀ via embed_t125_in_tree_per_kQ
    │                                (long arm: chain[1..4]=w, arm₁)
    └── ¬hlen5: chain.length = 4
        ├── h_arm₁_deg2: arm₁.deg = 2 → T(1,2,5) at v₀ via embed_t125
        │                                (long arm: chain[1], chain[2], w, arm₁, z₁)
        ├── h_arm₂_deg2: arm₂.deg = 2 → T(1,2,5) at v₀ via embed_t125
        │                                (long arm: chain[1], chain[2], w, arm₂, z₂)
        └── residual all-leaves    → SORRY (closed by PR #2970)
```

That is **three umbrella tractable dispatches** as advertised by the
issue body:
1. `x.deg = 3` → Ẽ₇ (one dispatch);
2. `x.deg = 1 ∧ chain.length = 5` → T(1,2,5) (one dispatch);
3. `x.deg = 1 ∧ chain.length = 4 ∧ (arm₁.deg = 2 ∨ arm₂.deg = 2)` →
   T(1,2,5) (one dispatch split into two symmetric `by_cases` arms).

**Per-dispatch argument checks (spot-checked):**

**Sub-case C.short.3** (Ẽ₇ via `x → y₁` extension)
`FieldGenericNonAdjacentBranches.lean:702-748`.
- Hypotheses destructure correctly: `hxdeg3 : vertexDegree adj x = 3`,
  giving `Sx.card = 3`; the `Finset.erase side_arm` set has card 2 and
  is `Nonempty`; `y₁` picked as an arbitrary element.
- Vertex map at the dispatch call (`735-737`): `0→v₀, 1→leaf,
  2→side_arm, 3→x, 4→y₁` (length-3 arm via side_arm-x-y₁),
  `5→chain[1], 6→chain[2], 7→chain[3]` (length-3 arm via chain).
- Edge args passed: `h_leaf_adj, hside_adj, hx_adj, hy₁_adj`
  (leaf-arm + side_arm-arm + chain-arm initial steps);
  `hc1_adj, hc12, hc23` (chain path). All seven `embed_etilde7`
  edge hypotheses present in the right order.
- Distinctness args (7): `hside_ne_leaf.symm, hleaf_ne_c1, hside_ne_c1,
  hx_ne_v₀, hc2_ne_v₀, hy₁_ne_side, hc3_ne_c1`. Match the
  `embed_etilde7_in_tree_per_kQ` signature at
  `FieldGenericETilde7.lean:370-372`
  (`hu₁_ne_c₂, hu₁_ne_c₃, hc₂_ne_c₃, hd₂_ne_v₀, hd₃_ne_v₀,
   he₂_ne_c₂, he₃_ne_c₃`) given the vertex map
  (e.g., `hside_ne_leaf.symm : leaf ≠ side_arm` plays the role of
  `hu₁_ne_c₂ : u₁ ≠ c₂` with the map `leaf→u₁`, `side_arm→c₂`).

**Sub-case C.short.1.5** (T(1,2,5) via `chain[4]=w` + arm₁)
`FieldGenericNonAdjacentBranches.lean:751-791`.
- `hc4_eq_w` derived from `chain.length = 5 ∧ chain[len-1] = w` via
  `Fin.ext` and `omega` (chain[4] = chain[len-1] = w); `hc4_arm`
  rewrites `harm₁_adj` accordingly.
- Vertex map: `0→v₀, 1→leaf, 2→side_arm, 3→x` (length-2 arm),
  `4→chain[1], ..., 7→chain[4]=w, 8→arm₁` (length-5 arm of
  six vertices).
- 9 edges + 9 distinctness facts dispatched; spot-checked
  `harm₁_ne_c3 := arm₁_ne_chain 3 (by omega)` against
  `arm₁_ne_chain` defined at line 322 (uses `acyclic_path_nonadj`).

**Sub-case C.short.1.4.arm₁** (T(1,2,5) via chain[1..2]-w-arm₁)
`FieldGenericNonAdjacentBranches.lean:817-845`.
- `Sarm1 := filter (adj arm₁ · = 1)`, `card = 2 = h_arm₁_deg2`, erase
  `w` to get the unique non-`w` neighbour `z₁`.
- `hc2_w` derived: `chain[2] = chain[len-2]` via `Fin.ext`+`omega`
  (`hc2_eq_pre` at line 799), then `adj_comm` to flip
  `hw_chain_adj : adj w chain[len-2] = 1`.
- Vertex map: `0→v₀, 1→leaf, 2→side_arm, 3→x, 4→chain[1],
  5→chain[2], 6→w, 7→arm₁, 8→z₁`.

**Sub-case C.short.1.4.arm₂** is mirror-symmetric (lines 846-871),
same shape with `arm₂, z₂`.

**Residual (all-leaves)**
`FieldGenericNonAdjacentBranches.lean:872-895`.
PR #2966 originally left this case as `sorry` (commit diff
shows the literal `sorry` token) under the comment:
> "All-leaves residual: chain.length = 4, x.deg = 1,
>   arm₁.deg = arm₂.deg = 1. ... Awaiting `d7tilde_not_finite_type_per_kQ`
>   (issue #2964); residual fill tracked separately."

The breadcrumb references #2964 (the D̃₇ helper) correctly. PR #2970
then closed this sorry — see D3 below.

**Coverage check.** Inside the Case C arm (`hC` true), every leaf in
the decision tree closes. Outside the Case C arm (`¬hC`), control
flows to Case D/E (lines 896+), which is out of scope for #2966. No
fourth `by_cases` is silently dropped:
- Case C's `by_cases hxdeg : ... = 2` is exhaustive (the negative
  branch is C.short).
- C.short's `by_cases hxdeg3 : ... = 3` together with the side_arm-x
  edge (forcing `x.deg ≥ 1`) and `h_no_adj_branch` (forcing
  `x.deg < 3`) gives `x.deg ∈ {1, 2}`; the C.short branch already
  excluded `2`, so the negative `hxdeg3` branch is `x.deg = 1`.
- The chain.length split is `{4, 5}` exhaustively (from `hlen4 ∧ hlen6`
  giving `chain.length ∈ {4, 5}`).
- The arm₁/arm₂ deg=2 split is exhaustive: if neither is 2 and both
  are `< 3` (from `h_no_adj_branch_w`), both are 1, giving the
  all-leaves residual.

**Sorry introduced by this PR for Case C.short:** exactly one (the
all-leaves residual, line ≈ 893 of the post-#2966 file), and it is
closed by PR #2970. No other new sorry on the Case C.short subtree.

**Minor issue-body inaccuracy (non-blocking):**
- The issue body's bullet 2 describes the C.short.1 dispatches as
  "T(1, 2, 5) at w", but the actual code embeds T(1,2,5) at **v₀**
  (vertex map starts `0→v₀`). The "at w" claim is mistaken in the
  issue body; the code is internally consistent. Not a code bug.

## D3 — D̃₇ embed helper + dispatch (PR #2970): **PASS**

**(a) Signature of `embed_d7tilde_in_tree_per_kQ`**
(`FieldGenericD7Tilde.lean:323-348`).
Parameters: `a b p q r s u v : Fin n` (8 vertices), with the following
correspondence to the canonical D̃₇ adjacency labelling
(`d7tildeAdj` vertex 0..7):
- `a` ↔ `0` (left leaf 1 of left branch),
- `b` ↔ `1` (left leaf 2 of left branch),
- `p` ↔ `2` (left branch point),
- `q` ↔ `3` (chain interior 1),
- `r` ↔ `4` (chain interior 2),
- `s` ↔ `5` (right branch point),
- `u` ↔ `6` (right leaf 1 of right branch),
- `v` ↔ `7` (right leaf 2 of right branch).

Edge hypotheses (7): `hap, hbp` (left leaves), `hpq, hqr, hrs`
(internal chain), `hsu, hsv` (right leaves). Non-edge input (1):
`hps : adj p s = 0`. Distinctness hypotheses (7): `hab, haq, hbq,
huv, hru, hrv, hps_ne : p ≠ s`. Field/orientation
`F, Q, hOrient` as usual.

**(b) Distinctness lattice exhaustiveness**
(`FieldGenericD7Tilde.lean:349-544`). The body derives the remaining
21 non-edge facts to fill out C(8, 2) = 28 unordered pairs (7 edges +
21 non-edges):

| Level                | Count | Lemma                                  |
|---------------------|------:|----------------------------------------|
| Triangle non-edges  |   8   | `acyclic_no_triangle`                  |
| Distance-3 (4-path) |   4   | `acyclic_path_nonadj` + `path_nodup4`  |
| Distance-4 (5-path) |   4   | `acyclic_path_nonadj` + `path_nodup5`  |
| Distance-5 (6-path) |   4   | `acyclic_path_nonadj` + `path_nodup6`  |
| Input non-edge      |   1   | `hps` (p-s, distance-3 on the chain)   |
| **Total non-edges** |  **21** |                                      |
| + 7 input edges     |       |                                      |
| = **28 = C(8, 2)**  |       |                                      |

Spot-checked entries:
- `hpr0` (`p-r` apex `q`): line 441-442. Requires `hpr_ne` from
  line 439 (derived: if `p = r` then `hrs : adj r s = 1` and
  `hps : adj p s = 0` contradict).
- `hqs0` (`q-s` apex `r`): line 446-447. Requires `hqs_ne` from
  line 444.
- `has0` (`a-s` distance-4 via `[a, p, q, r, s]`): line 483-489.
  Uses `path_nodup5` with the 10 pairwise distinctness facts
  derived above.
- `hbv0` (`b-v` distance-5 via `[b, p, q, r, s, v]`): line 538-544.
  Uses `path_nodup6` with the 15 pairwise distinctness facts.

The hypothesis-derivation chain is internally consistent: each ne
fact used in `path_nodupK` is either an input distinctness hypothesis,
an `ne_of_adj'` from an edge, or a `linarith` from a previously
proved zero adjacency.

**Note on issue body lattice numerology.** The issue body's count
"7 edge non-edges + 7 triangle non-edges + 6 distance-3 + 5 distance-4
+ 2 distance-5 + 1 distance-6 = 28 (matching the Ẽ₇ embedder's
lattice count)" describes a different distance distribution than the
file's actual `8 + 4 + 4 + 4 + 1` D̃₇ shape. The Ẽ₇ T(1,3,3)
embedder at `FieldGenericETilde7.lean:356` does indeed have the
`7+6+5+2+1` distance signature (its diameter is 6), but D̃₇ has
diameter 5 (`a` to `u`/`v` traverses 5 edges through the central
chain). The code is correct for D̃₇; the issue body's reference to
"Ẽ₇'s lattice count" was a misleading shorthand.

**(c) `φ_fun : Fin 8 → Fin n`**
(`FieldGenericD7Tilde.lean:546-549`). Pattern-match on the underlying
`val` field: `0→a, 1→b, 2→p, 3→q, 4→r, 5→s, 6→u, 7→v`. Matches the
adjacency labelling (a). Injectivity proof (`φ_inj`, 550-555) is a
64-case `fin_cases i <;> fin_cases j` discharged by `rfl` for
diagonals or by `exact absurd hij ‹_›` against the pairwise
distinctness facts (which by this point include all 28 pair
distinctnesses).

**`hembed` proof**
(`FieldGenericD7Tilde.lean:557-573`). Verifies
`d7tildeAdj i j = adj (φ i) (φ j)` for all 64 (i, j) ∈ Fin 8 × Fin 8.
Reduced via `fin_cases <;> simp [d7tildeAdj, φ_fun] <;> norm_num
<;> linarith [...]`. The `linarith` hypothesis list provides the
21 zero adjacency facts and their `adj_comm` flips, plus the 8 hdiag
facts and the 14 edge facts. The `set_option maxHeartbeats 800000`
preamble (line 311) bumps the limit from the default 200k for this
sizeable linarith — documented inline.

The dispatch is then via `subgraph_infinite_type_transfer_per_kQ`
(line 574-576), passing `d7tilde_not_finite_type_per_kQ` over the
restricted orientation. Standard precedent.

**(d) Dispatch in `FieldGenericNonAdjacentBranches.lean:872-895`.**
Vertex map: `a=leaf, b=side_arm, p=v₀, q=chain[1], r=chain[2], s=w,
u=arm₁, v=arm₂`. (Note: `x` is excluded — in the all-leaves case
`x.deg = 1`, so it does not participate in the embedded D̃₇.)
Edge hypotheses passed (in `embed_d7tilde_in_tree_per_kQ` signature
order):
- `hap = h_leaf_adj` (adj v₀ leaf = 1) ✓
- `hbp = hside_adj` (adj v₀ side_arm = 1) ✓
- `hpq = hc1_adj` (adj v₀ chain[1] = 1) ✓
- `hqr = hc12` (adj chain[1] chain[2] = 1, from `hchain_edges 1`) ✓
- `hrs = hc2_w` (adj chain[2] w = 1, derived via `adj_comm` from
  `hw_chain_adj` and the index identity `chain[2] = chain[len-2]`) ✓
- `hsu = harm₁_adj` ✓
- `hsv = harm₂_adj` ✓
- `hps = hps_eq : adj v₀ w = 0`
  (`= (h01 v₀ w).resolve_right h_v₀w_nonadj`) ✓

Distinctness hypotheses:
- `hab = hside_ne_leaf.symm` (leaf ≠ side_arm) ✓
- `haq = hleaf_ne_c1` (leaf ≠ chain[1]) ✓
- `hbq = hside_ne_c1` (side_arm ≠ chain[1]) ✓
- `huv = harm₁₂` (arm₁ ≠ arm₂) ✓
- `hru = harm₁_ne_c2` (= `(arm₁_ne_chain 2 _).symm`) ✓
- `hrv = harm₂_ne_c2` ✓
- `hps_ne = hne.symm` (v₀ ≠ w) ✓

All 8 edge/non-edge + 7 distinctness arguments are present in the
right slots.

**(e) Residual closure.** Greps on the post-#2970 source confirm the
only `sorry` left in `non_adjacent_branches_leaf_case_per_kQ` is the
Case-E residual at line ~1093 (`chain.length = 3` mixed degrees,
`chain.length = 5`, `chain.length ≥ 6` all-leaves — gated on
follow-ups #2974/#2976/#2977/#2978, not on this PR). The Case
C.short all-leaves arm itself is genuinely closed by the D̃₇
dispatch.

## D4 — Build sanity at current `main`: **PASS**

```
lake build \
  EtingofRepresentationTheory.Chapter6.FieldGenericD7Tilde \
  EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches \
  EtingofRepresentationTheory.Chapter6.FieldGenericAssembly
```

at commit `2a9398f`: **Build completed successfully (8049 jobs).**
Zero errors. The relevant target completions:

```
⚠ [8043/8049] Built ...FieldGenericD5Tilde (21s)
⚠ [8044/8049] Built ...FieldGenericETilde6 (22s)
⚠ [8045/8049] Built ...FieldGenericD7Tilde (29s)
⚠ [8046/8049] Built ...FieldGenericETilde7 (30s)
⚠ [8047/8049] Built ...FieldGenericNonAdjacentBranches (18s)
✔ [8049/8049] Built ...FieldGenericAssembly (32s)
```

**`declaration uses sorry` warnings in build scope (12):**

```
InfiniteTypeConstructions.lean:3331, 3588, 3815  (pre-existing)
FieldGenericStar.lean:543                          (pre-existing)
FieldGenericT125.lean:39                           (pre-existing — t125 api stub #2875)
FieldGenericD5Tilde.lean:798, 974                  (pre-existing — d5tilde precedent)
FieldGenericETilde6.lean:291                       (pre-existing)
FieldGenericD7Tilde.lean:247                       (NEW — d7tildeRep_kQ_isIndecomposable, tracked by #2967)
FieldGenericETilde7.lean:273                       (pre-existing)
FieldGenericNonAdjacentBranches.lean:88            (pre-existing — top-level theorem, Case E residual)
FieldGenericTpqr.lean:1233                         (pre-existing)
```

The only **new** sorry introduced by these three PRs combined is
`FieldGenericD7Tilde.lean:247` (`d7tildeRep_kQ_isIndecomposable`),
tracked by https://github.com/kim-em/Etingof-RepresentationTheory-draft1/issues/2967
exactly as the audit issue body predicts. The
`FieldGenericNonAdjacentBranches.lean:88` warning is the top-level
theorem header, whose body still contains the Case-E residual (gated
on #2974/#2976/#2977/#2978, outside this audit's scope); the Case
C.short subtree itself contributes no new sorry.

Net sorry delta from these three PRs: **+1** (the new
`d7tildeRep_kQ_isIndecomposable`). PR #2966 added one residual sorry
in C.short.all-leaves (gated on #2964); PR #2970 closed that
residual. PR #2968 introduced one new sorry
(`d7tildeRep_kQ_isIndecomposable`).

## D5 — Cross-file consistency: **CONCERN**

**Chapter6.lean import (PR #2968).** PASS.
`EtingofRepresentationTheory/Chapter6.lean:13` correctly imports
`FieldGenericD7Tilde` next to `FieldGenericD5Tilde`. This was added
by PR #2968 alongside the new file. ✓

**`embed_d7tilde_in_tree_per_kQ` file placement (PR #2970).** PASS.
The embed helper lives in `FieldGenericD7Tilde.lean:323` (Section 7),
co-located with the underlying `d7tilde_not_finite_type_per_kQ` it
consumes. This is consistent with the established precedent:
- `embed_etilde6_in_tree_per_kQ` in `FieldGenericETilde6.lean:372`,
- `embed_etilde7_in_tree_per_kQ` in `FieldGenericETilde7.lean:356`,
- `embed_t125_in_tree_per_kQ` in `FieldGenericT125.lean:71`.

`FieldGenericNonAdjacentBranches.lean` imports the helper via the
top-level `import EtingofRepresentationTheory.Chapter6.FieldGenericD7Tilde`
(added by PR #2970 at line 8). ✓

**Docstring on `FieldGenericNonAdjacentBranches.lean:28-33`.**
**CONCERN (still stale).**
The file docstring's enumeration of available fixed-shape
infinite-type leaves remains:

> "no `dTilde_not_finite_type_per_kQ` for general `n` — only the
> fixed-`n` leaves `d5tilde_not_finite_type_per_kQ`
> (`FieldGenericD5Tilde.lean:999`),
> `etilde6_not_finite_type_per_kQ` (`FieldGenericETilde6.lean:319`),
> `etilde7_not_finite_type_per_kQ` (`FieldGenericETilde7.lean:301`),
> and `t125_not_finite_type_per_kQ` (`FieldGenericT125.lean:39`),
> plus the shared embedding helper `embed_t125_in_tree_per_kQ`
> (`FieldGenericT125.lean:71`)."

After PR #2968 added `d7tilde_not_finite_type_per_kQ` and PR #2970
added `embed_d7tilde_in_tree_per_kQ`, this list should be extended.
The prior audit
`progress/reviews/2026-05-19-non-adjacent-branches-leaf-case-api-stub.md`
already flagged the missing `d7tilde_not_finite_type_per_kQ`
mention. Neither PR refreshed the docstring. Non-blocking; CONCERN
applies to all three PRs. A 4-line cleanup (one line per helper in
the enumeration) would close it.

**Cross-reference accuracy nit.**
`FieldGenericD7Tilde.lean:41,230` cite
`FieldGenericD5Tilde.lean:980` for the D̃₅ indecomposability
precedent, but the declaration `d5tildeRep_kQ_isIndecomposable`
starts at line 974 (sorry at 981). Off by a few lines. Trivial.

## Notes on issue-body inaccuracies (non-blocking)

These are observations about the audit issue body itself, not the
PRs:
1. Issue body bullet 2 describes the C.short `x.deg = 1 ∧
   chain.length = 4` dispatches as "T(1, 2, 5) at w"; actual code is
   at v₀ (vertex map starts `0→v₀`). Code is correct.
2. Issue body D3.b lattice claim was for the Ẽ₇ T(1,3,3) distance
   distribution (`7+6+5+2+1`), not for D̃₇ (`8+4+4+4+1`). Code is
   correct for D̃₇.
3. D̃₅ precedent cross-reference at the issue body and in the D̃₇
   docstrings cites `FieldGenericD5Tilde.lean:980`; actual line is
   974 (sorry at 981). Minor.

None of these affect the verdict; they're worth a follow-up cleanup
pass.

## Recommendation

All three PRs are sound. The single CONCERN (stale docstring at
`FieldGenericNonAdjacentBranches.lean:28-33`) is non-blocking and
can be addressed in a one-line cleanup PR if not picked up by the
next sibling audit's findings. No code changes were pushed during
this audit.

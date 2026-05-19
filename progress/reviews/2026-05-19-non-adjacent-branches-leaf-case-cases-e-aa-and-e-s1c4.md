# Review: `non_adjacent_branches_leaf_case_per_kQ` — Case E.aa + E.s1c4 dispatches (PR #2979)

**Issue:** https://github.com/kim-em/Etingof-RepresentationTheory-draft1/issues/2980
**PR audited:** #2979 (merge commit `2a9398f`)
**Audited commit:** `ec4696f` (current `main`)
**Target file:** `EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean`

## Summary

| Dim | Verdict |
|-----|:-------:|
| D1 Sub-case E.aa correctness (Ẽ₆ at w via reversed chain edge) | **PASS** |
| D2 Sub-case E.s1c4 correctness (D̃₇ at (v₀, w))                | **PASS** |
| D3 Residual sorry documentation + sub-issue breadcrumbs       | **CONCERN** |
| D4 Build sanity at current `main`                             | **PASS** |
| D5 Cross-file consistency / progress alignment                | **CONCERN** |

No build-breaking issues. No code changes pushed.

## D1 — Sub-case E.aa correctness (Ẽ₆ at w): **PASS**

Block at `FieldGenericNonAdjacentBranches.lean:989-1048`. Entry condition
`chain.length = 3 ∧ arm₁.deg = 2 ∧ arm₂.deg = 2` (line 989) destructured
at line 992 into `_hlen3, harm₁_deg2, harm₂_deg2`. The leading `_` on
`_hlen3` is fine — the hypothesis `chain.length = 3` only feeds the
later `omega` discharges via the implicit lattice.

**(a) `y₁` / `y₂` extraction** (lines 994-1020). Pattern mirrors Case D
at `FieldGenericNonAdjacentBranches.lean:902-928` exactly:
`Sarm₁ := Finset.univ.filter (adj arm₁ · = 1)`, then
`card_eq_one` after `erase w` yields `y₁` plus
`hy₁_adj : adj arm₁ y₁ = 1` and `hy₁_ne_w : y₁ ≠ w` (via
`Finset.ne_of_mem_erase`). Phase 1 supplies `arm₁_adj_w : adj arm₁ w = 1`
(line 245) used as the membership witness, and `harm₁_deg2` is the
`card = 2` source. Same shape for `y₂` (lines 1007-1020). PASS.

**(b) Reversed chain edge** (lines 1023-1033):
```
hcL_2_3 : adj chain[chain.length-3] chain[chain.length-2] = 1
hcR_2_3 : adj chain[chain.length-2] chain[chain.length-3] = 1
```
For `chain.length = 3` these are `adj chain[0] chain[1]` and
`adj chain[1] chain[0]` respectively, i.e. `adj v₀ c` and `adj c v₀`
(using Phase 1's `hchain_first : chain.get ⟨0, _⟩ = v₀`). The
`hchain_edges (chain.length - 3) (by omega)` discharges because
`hchain_len : 3 ≤ chain.length` plus the local `chain.length = 3`
implies `chain.length - 3 + 1 = chain.length - 2 < chain.length`. The
`Fin.ext h_nat`-based rewrite handles the index re-association.
Construction is structurally identical to Case D's `hcL_2_3` / `hcR_2_3`
at lines 930-940 (which audited PASS in
`progress/reviews/2026-05-19-non-adjacent-branches-leaf-case-phase-1-and-cases-a-b-c-d.md`).
PASS.

**(c) `hc_3_ne_w`** (lines 1034-1036) — `chain[chain.length - 3] ≠ w`
via `hw_get` + `hchain_nodup.get_inj_iff`. For `chain.length = 3` this
is `chain[0] ≠ chain[2]`, discharged by `simp; omega` on the index
inequality. Same shape as Case D's `hc_3_ne_w` at lines 942-944. PASS.

**(d) Final `embed_etilde6_in_tree_per_kQ` call** (lines 1039-1048).
The embedder signature at `FieldGenericETilde6.lean:372-391` takes 7
vertex arguments (`v₀ c₁ d₁ c₂ d₂ c₃ d₃`) and 12 fact arguments
(`hc₁ hd₁ hc₂ hd₂ hc₃ hd₃` plus
`hc₁_ne_c₂ hc₁_ne_c₃ hc₂_ne_c₃ hd₁_ne_v₀ hd₂_ne_v₀ hd₃_ne_v₀`).

Position-by-position the call passes:

| Embedder position | Argument | Phase-1 source |
|---|---|---|
| `v₀` (centre) | `w` | — |
| `c₁` | `chain.get ⟨chain.length - 2, _⟩` | (chain) |
| `d₁` | `chain.get ⟨chain.length - 3, _⟩` | (chain) |
| `c₂` | `arm₁` | Phase 1 |
| `d₂` | `y₁` | extracted above |
| `c₃` | `arm₂` | Phase 1 |
| `d₃` | `y₂` | extracted above |
| `hc₁ : adj w chain[len-2] = 1` | `hw_chain_adj` | line 216 |
| `hd₁ : adj chain[len-2] chain[len-3] = 1` | `hcR_2_3` | just built |
| `hc₂ : adj w arm₁ = 1` | `harm₁_adj` | line 234 |
| `hd₂ : adj arm₁ y₁ = 1` | `hy₁_adj` | just built |
| `hc₃ : adj w arm₂ = 1` | `harm₂_adj` | line 236 |
| `hd₃ : adj arm₂ y₂ = 1` | `hy₂_adj` | just built |
| `hc₁_ne_c₂ : chain[len-2] ≠ arm₁` | `harm₁_ne_pre.symm` | line 238 |
| `hc₁_ne_c₃ : chain[len-2] ≠ arm₂` | `harm₂_ne_pre.symm` | line 240 |
| `hc₂_ne_c₃ : arm₁ ≠ arm₂` | `harm₁₂` | line 229 |
| `hd₁_ne_v₀ : chain[len-3] ≠ w` | `hc_3_ne_w` | just built |
| `hd₂_ne_v₀ : y₁ ≠ w` | `hy₁_ne_w` | extracted above |
| `hd₃_ne_v₀ : y₂ ≠ w` | `hy₂_ne_w` | extracted above |

All 19 positional arguments match. Spot-checked `harm₁_ne_pre.symm`
(line 238 builds `arm₁ ≠ chain[len-2]` via `Finset.ne_of_mem_erase
harm₁_mem`; `.symm` flips to `chain[len-2] ≠ arm₁`), `hcR_2_3` (just
built), `hc_3_ne_w` (just built). The Ẽ₆ = T(2,2,2) leg structure is:
leg 1 = `w-chain[len-2]-chain[len-3]` (= `w-c-v₀`); leg 2 =
`w-arm₁-y₁`; leg 3 = `w-arm₂-y₂`. PASS.

**Note on `chain.length = 3` specialisation:** for chain.length = 3,
`chain.length - 3 = 0` and `chain.length - 2 = 1`, so the first leg
collapses to the chain `w-c-v₀`. The arithmetic falls out of
`hchain_len` plus the destructured `chain.length = 3`. The dispatch
template generalises Case D's pattern with no signature divergence —
the same `embed_etilde6_in_tree_per_kQ` positional shape is used (Case
D at lines 949-958 uses the identical 19 arguments in the same
positions). The only structural difference is the source of the
chain-length bound; Case D's `chain.length ∈ {4, 5}` and E.aa's
`chain.length = 3` both produce the required `chain[len-3]` index via
`omega`. PASS.

## D2 — Sub-case E.s1c4 correctness (D̃₇ at (v₀, w)): **PASS**

Block at `FieldGenericNonAdjacentBranches.lean:1049-1082`. Entry condition
`chain.length = 4 ∧ vertexDegree adj side_arm = 1` (line 1049)
destructured at line 1052 into `hlen4, _hside_deg1`. The `_` prefix on
`_hside_deg1` is correct — the hypothesis is mathematically necessary
for the embedding (it forces the 8 vertices to be the entire induced
subgraph in the all-leaves case) but is not consumed by the dispatch:
`embed_d7tilde_in_tree_per_kQ` derives all internal non-edges from the
listed 7 edges + 1 non-edge + acyclicity hypothesis. PASS on the lint
guard.

**(a) `hc12`** (lines 1054-1056) — `adj chain[1] chain[2] = 1` from
`hchain_edges 1 (by omega)`. For `chain.length = 4`, the call needs
`2 < chain.length`, which follows from `hlen4` via `omega`. PASS.

**(b) `hc2_eq_pre`** (lines 1058-1061) —
`chain[2] = chain[chain.length - 2]`. For `chain.length = 4`, this is
trivially `chain[2] = chain[2]`. `omega` discharges `(2 : ℕ) =
chain.length - 2` from `hlen4`; `Fin.ext h_nat` then closes the
`Fin (chain.length)` equality. PASS.

**(c) `hc2_w`** (lines 1062-1063) — `adj chain[2] w = 1` via rewrite
chain `chain[2] → chain[len-2] → adj_comm` against
`hw_chain_adj : adj w chain[len-2] = 1`. Direction is correct: the
goal `adj chain[2] w = 1` is rewritten left-to-right with `hc2_eq_pre`
to `adj chain[len-2] w = 1`, then `adj_comm` rewrites to
`adj w chain[len-2] = 1`, which `hw_chain_adj` closes. PASS.

**(d) `hps_eq`** (lines 1065-1066) — `adj v₀ w = 0` via
`(h01 v₀ w).resolve_right h_v₀w_nonadj`. The strengthened
`h_v₀w_nonadj : adj v₀ w ≠ 1` is bound at line 107 in the signature
(introduced by PR #2941 — confirmed still on `main` at the same
location). `resolve_right` selects the left disjunct `adj v₀ w = 0`
when the right disjunct contradicts `h_v₀w_nonadj`. PASS.

**(e) `harm₁_ne_c2`, `harm₂_ne_c2`** (lines 1068-1071) — from
`arm{1,2}_ne_chain 2 (by omega)`. The `arm₁_ne_chain` and
`arm₂_ne_chain` lemmas are Phase 1 distinctness facts
(`FieldGenericNonAdjacentBranches.lean:322-356, 358-392`); each takes a
chain index and a bound proof. `omega` handles `2 < chain.length` from
`hlen4`. The `.symm` flips orientation to `chain[2] ≠ arm{1,2}`. PASS.

**(f) Final `embed_d7tilde_in_tree_per_kQ` call** (lines 1075-1082).
The embedder signature at `FieldGenericD7Tilde.lean:323-340` takes 8
vertex arguments (`a b p q r s u v`) and 15 fact arguments
(7 edges + 1 non-edge + 7 distinctness).

Position-by-position:

| Embedder position | Argument | Source |
|---|---|---|
| `a` | `leaf` | Phase 1 input |
| `b` | `side_arm` | Phase 1 |
| `p` (left branch point) | `v₀` | Phase 1 input |
| `q` | `chain.get ⟨1, _⟩` | (chain) |
| `r` | `chain.get ⟨2, _⟩` | (chain) |
| `s` (right branch point) | `w` | Phase 1 input |
| `u` | `arm₁` | Phase 1 |
| `v` | `arm₂` | Phase 1 |
| `hap : adj v₀ leaf = 1` | `h_leaf_adj` | line 108 |
| `hbp : adj v₀ side_arm = 1` | `hside_adj` | line 204 |
| `hpq : adj v₀ chain[1] = 1` | `hc1_adj` | line 167 |
| `hqr : adj chain[1] chain[2] = 1` | `hc12` | just built |
| `hrs : adj chain[2] w = 1` | `hc2_w` | just built |
| `hsu : adj w arm₁ = 1` | `harm₁_adj` | line 234 |
| `hsv : adj w arm₂ = 1` | `harm₂_adj` | line 236 |
| `hps : adj v₀ w = 0` | `hps_eq` | just built |
| `hab : leaf ≠ side_arm` | `hside_ne_leaf.symm` | line 206 |
| `haq : leaf ≠ chain[1]` | `hleaf_ne_c1` | line 170 |
| `hbq : side_arm ≠ chain[1]` | `hside_ne_c1` | line 208 |
| `huv : arm₁ ≠ arm₂` | `harm₁₂` | line 229 |
| `hru : chain[2] ≠ arm₁` | `harm₁_ne_c2` | just built |
| `hrv : chain[2] ≠ arm₂` | `harm₂_ne_c2` | just built |
| `hps_ne : v₀ ≠ w` | `hne.symm` | line 104 |

All 23 positional arguments match. The dispatch is structurally
identical to the Case C.short all-leaves residual at lines 888-895
(which audited PASS in
`progress/reviews/2026-05-19-case-c-short-and-d7tilde-helper.md`,
D3). Same fact names, same argument order — only the surrounding
`by_cases` path differs. PASS.

**Note on D̃₇ embedder dependency:** the embedder
`embed_d7tilde_in_tree_per_kQ` itself audited PASS under issue #2973
(PR #2981, merged); the dispatch correctness here therefore does not
inherit any open audit concern from the embedder.

## D3 — Residual sorry documentation + sub-issue breadcrumbs: **CONCERN**

Residual block at `FieldGenericNonAdjacentBranches.lean:1083-1093`.

**(a) Comment-block enumeration of remaining configurations**
(lines 1084-1087):
```
-- Remaining: chain.length = 3 mixed arm cases (E.ab, E.bb),
-- chain.length = 5 (any), chain.length ≥ 6 all-leaves.
-- Requires Ẽ₇ extension splits, D̃₆, or D̃₈+/parametric D̃_n
-- helpers — see follow-up sub-issues.
```
This is a 3-bullet enumeration. Cross-referenced with the upstream
comment block at lines 979-988:
```
-- * E.aa siblings at `chain.length = 3` with mixed arm degrees
--   (requires Ẽ₇ at `v₀` or `w` plus extension-degree splits, or
--   the unavailable D̃₆ helper for all-leaves at chain.length=3).
-- * `chain.length = 5` (any sub-case): needs D̃₈ helper, ...
-- * `chain.length ≥ 6` all-leaves: needs general D̃_n helper.
```

**Concern:** the comment block has **3 bullets** but there are
**4 sub-issues** (#2974, #2976, #2977, #2978). The chain.length=3
case is split across two sub-issues (#2974 for all-leaves, #2976 for
mixed) but the comment block at lines 979-981 lumps both under "E.aa
siblings ... with mixed arm degrees", with the D̃₆ all-leaves variant
mentioned only in a parenthetical aside ("or the unavailable D̃₆
helper for all-leaves at chain.length=3"). The lower comment block at
lines 1084-1086 entirely omits the chain.length=3 all-leaves case
(the bullet says "chain.length = 3 mixed arm cases (E.ab, E.bb)" —
all-leaves is neither mixed nor labelled E.ab/E.bb).

The sub-issue split is correct (D̃₆ is genuinely a different helper
from Ẽ₇ extensions, so #2974 ≠ #2976), but the comment-block
enumeration in the code does not reflect that split exactly.

**(b) `let _ := …` bindings** (lines 1088-1092). Eight bindings:
`hn, h_deg, h_no_adj_branch, h_no_adj_branch_w, hleaf_ne_arm₁,
hleaf_ne_arm₂, hside_ne_arm₁, hside_ne_arm₂, leaf_ne_chain,
arm₂_ne_chain`. Checked syntactic usage elsewhere in the file via grep:

- `hn`, `h_deg`, `h_no_adj_branch`, `h_no_adj_branch_w`,
  `hleaf_ne_arm₁`, `hleaf_ne_arm₂`, `hside_ne_arm₁`,
  `hside_ne_arm₂`, `leaf_ne_chain` — each appears only in its Phase 1
  binding site and in this `let _` block. The `let _` is genuinely
  silencing an unused-variable warning. PASS.
- `arm₂_ne_chain` — also appears at lines 862, 887, 1071 (Cases C
  arm₂-extends, C.short all-leaves residual, E.s1c4). It is already
  syntactically used; the `let _ := arm₂_ne_chain` at line 1092 is
  **redundant**. Minor slop. (`arm₁_ne_chain` — also used at 782,
  834, 885, 1069 — is correctly absent from the `let _` list.)

The asymmetric inclusion of `arm₂_ne_chain` but not `arm₁_ne_chain`
in the `let _` list is a small inconsistency, not a correctness
issue.

**(c) Sub-issue references in the comments.** The residual comment
block at lines 1084-1087 says "see follow-up sub-issues" but does
**not** cite the issue numbers `#2974`, `#2976`, `#2977`, `#2978`.
The earlier comment at line 988 says "Tracked by follow-up sub-issues
spawned from #2955" — same, no specific numbers. Searching by
sub-issue number in the file: zero matches for `#2974`, `#2976`,
`#2977`, `#2978`. A reader landing on the residual `sorry` has no
direct link to the four tracking issues.

**(d) Sub-issue coverage check.** Cross-read of issue bodies
#2974 (all-leaves chain.length=3 → D̃₆), #2976 (mixed chain.length=3
→ Ẽ₇ extension splits), #2977 (chain.length=5 → D̃₈), #2978
(chain.length≥6 all-leaves → parametric D̃_n) confirms each covers a
disjoint configuration band. Their union is exactly the residual
configuration space implied by `¬ hA ∧ ¬ hB ∧ ¬ hC ∧ ¬ hD ∧ ¬ hE_aa ∧
¬ hE_s1c4` (worked through case-by-case in the audit notes for D5
below). No orphan configuration, no double coverage. PASS on the
sub-issue side.

**Verdict CONCERN** — the sub-issue coverage is correct, but the
comment-block enumeration in the residual is sloppy:
- 3 bullets cover 4 sub-issues (chain.length=3 split is hidden);
- the residual block's `let _ := arm₂_ne_chain` is redundant;
- specific sub-issue numbers (#2974/#2976/#2977/#2978) are not cited.

None of these is build-breaking. Recommend a small follow-up doc
patch (or fold into the existing #2982 docstring refresh) to:
(i) make the 4-way decomposition explicit in the residual comment;
(ii) drop the redundant `let _ := arm₂_ne_chain`; (iii) cite the four
sub-issue numbers.

## D4 — Build sanity at current `main`: **PASS**

```
$ git rev-parse HEAD
ec4696f1a61243fbf5b89a6b794ba6da420c87ab
$ lake exe cache get
… Already decompressed 8010 file(s) …
$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches
… ⚠ [8047/8047] Built EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches (17s) …
Build completed successfully (8047 jobs).
```

Filtered warning list for the target file (verbatim from
`/tmp/build-nonadj.log`):
```
warning: EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean:88:8: declaration uses `sorry`
```

Exactly one warning at line 88 (the top-level
`non_adjacent_branches_leaf_case_per_kQ` theorem), as expected. **No
unused-variable warnings on the E.aa or E.s1c4 blocks themselves,
including no warning on `_hside_deg1` at line 1052 or `_hlen3` at line
992.** The `let _ := …` block at lines 1088-1092 suppresses the
warnings on the unused Phase 1 hypotheses correctly.

Downstream build:
```
$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericAssembly
… ✔ [8049/8049] Built EtingofRepresentationTheory.Chapter6.FieldGenericAssembly (37s) …
Build completed successfully (8049 jobs).
```
No warnings on `FieldGenericAssembly.lean` itself. PASS.

## D5 — Cross-file consistency / progress alignment: **CONCERN**

**(a) Comment-block enumeration vs sub-issue decomposition.** Already
audited under D3 — the residual comment block's 3 bullets do not
match the 4-way sub-issue decomposition (#2974 vs #2976 split at
chain.length=3). CONCERN (cross-referenced from D3).

**(b) Progress entry alignment.** `progress/20260519T113642Z_5cda04fc.md`
accurately summarises:
- E.aa as "chain.length = 3 ∧ arm₁.deg = 2 ∧ arm₂.deg = 2" → Ẽ₆ at w;
- E.s1c4 as "chain.length = 4 ∧ side.deg = 1" → D̃₇ at (v₀, w);
- 8-vertex induced subgraph for E.s1c4 listed correctly;
- Sub-issue numbers #2974/#2976/#2977/#2978 cited correctly with
  matching scope descriptions.

Build claim ("File sorry count unchanged (1, at the top-level
theorem)") confirmed by D4. PASS.

**(c) Case D dispatch pattern claim.** The E.aa comment at lines
970-971 claims "mirrors Case D's dispatch with `chain.length - 3 = 0`,
`chain.length - 2 = 1`". Verified by inspection: Case D at lines
949-958 uses the same `embed_etilde6_in_tree_per_kQ` with the same 19
positional argument shape (vertex tuple
`w chain[len-2] chain[len-3] arm₁ y₁ arm₂ y₂` plus the same 12 fact
arguments). E.aa at lines 1039-1048 is the literal-clone dispatch for
the same vertex map with chain.length specialised to 3. No
signature divergence; the `omega` discharges differ only in the
underlying `hchain_len`/`chain.length = 3` source. PASS.

**(d) Per-(F, Q) library inventory in file docstring** (lines 27-34).
**Confirmed stale**: the docstring lists only
- `d5tilde_not_finite_type_per_kQ`
- `etilde6_not_finite_type_per_kQ`
- `etilde7_not_finite_type_per_kQ`
- `t125_not_finite_type_per_kQ`
- `embed_t125_in_tree_per_kQ`

Missing from this enumeration (both landed before the audited
commit):
- `d7tilde_not_finite_type_per_kQ`
  (`FieldGenericD7Tilde.lean:272`, PR #2968)
- `embed_d7tilde_in_tree_per_kQ`
  (`FieldGenericD7Tilde.lean:323`, PR #2970)

The strategy paragraph (lines 36-38) lists "`Ẽ₆`, `Ẽ₇`, `T(1, 2, 5)`"
as the available fixed-shape forbidden subgraphs — does not mention
`D̃₇`. The "API stub" paragraph (lines 40-52) claims the body is
`sorry`; the body has substantially landed (Phases 1+2 with Cases
A/B/C-main/C.short/D plus E.aa/E.s1c4). The theorem docstring at
lines 84-87 contains the same "API stub" claim. **All stale.**

This is the staleness the prior audit
`progress/reviews/2026-05-19-non-adjacent-branches-leaf-case-api-stub.md`
flagged as "Minor concern (non-blocking)" — it persists on `main` as
of `ec4696f`. **Issue #2982 is the docstring-refresh follow-up
already in the queue** (label `feature`, unclaimed at the time of
this audit). CONCERN.

**(e) Configuration coverage cross-check.** The four sub-issues plus
the six landed cases must partition the input configuration space.
Walking the `by_cases` cascade:

- **hA** (chain.length≥6, side.deg=2) → Case A: T(1,2,5) at v₀.
- **¬hA ∧ hB** (chain.length≥6, arm₁.deg=2 ∨ arm₂.deg=2) → Case B.
- **¬hA ∧ ¬hB ∧ hC** (chain.length∈{4,5}, side.deg=2) → Case C (incl.
  C.main / C.short.{1,3} / all-leaves D̃₇).
- **… ∧ ¬hC ∧ hD** (chain.length∈{4,5}, arm₁=arm₂=2) → Case D.
- **… ∧ ¬hD ∧ hE_aa** (chain.length=3, arm₁=arm₂=2) → E.aa.
- **… ∧ ¬hE_aa ∧ hE_s1c4** (chain.length=4, side.deg=1) → E.s1c4.

Residual configurations:

| chain.length | side.deg | arm₁.deg | arm₂.deg | Sub-issue |
|---|---|---|---|---|
| 3 | 1 | 1 | 1 | #2974 (D̃₆ all-leaves) |
| 3 | * | mixed (not (2,2), not (1,1)) | mixed | #2976 (Ẽ₇ splits) |
| 3 | 2 | * | * | #2976 (Ẽ₇ splits) |
| 5 | 1 | not (2,2) | not (2,2) | #2977 (D̃₈) |
| ≥6 | 1 | 1 | 1 | #2978 (parametric D̃_n) |

(Note: at chain.length=3, the constraint `arm₁.deg, arm₂.deg < 3`
from `h_no_adj_branch_w` restricts to `∈ {1, 2}`; similarly
`side.deg ∈ {1, 2}` from `h_no_adj_branch`. The mixed sub-band at
chain.length=3 is exactly `(side, arm₁, arm₂) ∈ {1,2}^3 ∖ {(*, 2, 2),
(*, 1, 1) ∩ {side=1}}` — covered by #2976.)

Union of cases A/B/C/D/E.aa/E.s1c4 + sub-issues #2974/#2976/#2977/#2978
covers the full configuration space. PASS on coverage; CONCERN
elsewhere as above. Verdict for D5 = CONCERN driven by the
docstring staleness (d).

## Verdict

**Mathematical correctness of the two newly landed sub-cases is
clean.** Both dispatches use audited per-(F, Q) embedders
(`embed_etilde6_in_tree_per_kQ` audited PASS in #2949,
`embed_d7tilde_in_tree_per_kQ` audited PASS in #2973). The 19-arg
Ẽ₆ call and 23-arg D̃₇ call thread the right facts at the right
positions; the E.aa dispatch is structurally identical to Case D
(same embedder, same arg shape, only the `chain.length` specialisation
differs), and the E.s1c4 dispatch is structurally identical to the
Case C.short all-leaves residual (which audited PASS).

**Concerns are all in the surrounding paperwork**: the residual
comment block does not match the 4-way sub-issue decomposition, the
file docstring + theorem docstring still claim "API stub", and the
sub-issue numbers are not cited in the comments. Issue #2982 already
tracks the docstring refresh; the residual comment polish and the
redundant `let _ := arm₂_ne_chain` line can be folded into that PR or
left for a future cleanup.

**No code changes pushed** — none warranted.

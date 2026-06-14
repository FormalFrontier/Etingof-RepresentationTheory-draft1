# Review: `non_adjacent_branches_leaf_case_per_kQ` — Phase 1 setup + Phase 2 Cases A/B/C-main/D

**Issue:** https://github.com/kim-em/Etingof-RepresentationTheory-draft1/issues/2972
**PRs audited:**
- #2952 (Phase 1 setup, merge `0b62104`)
- #2956 (Case A, merge `5527cfd`)
- #2958 (Case B, merge `7dcc9f3`)
- #2961 (Cases C+D, merge `47acdc3`)
**Audited commit:** `b1f8b7f` (current `main`)
**Target file:** `EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean`

## Summary

| Dim | #2952 | #2956 | #2958 | #2961 |
|-----|:-----:|:-----:|:-----:|:-----:|
| D1 Phase 1 lattice fidelity | **PASS** | n/a | n/a | n/a |
| D2 vertex map + embedder args | n/a | **PASS** | **PASS** | **PASS** |
| D3 case coverage (combined) | **PASS** | | | |
| D4 build sanity (combined)   | **PASS** | | | |
| D5 docstring / dead-code     | **CONCERN** | **CONCERN** | **CONCERN** | **CONCERN** |

No build-breaking issues. No code changes pushed.

## D1 — Phase 1 lattice fidelity (PR #2952): **PASS**

The Phase 1 block in `FieldGenericNonAdjacentBranches.lean:121-444` is a
line-for-line port of the universal `leaf_case` Phase 1 at
`InfiniteTypeConstructions.lean:9772-10120`. Spot-checked against the
universal:

- **Chain extraction** (`FieldGenericNonAdjacentBranches.lean:129-156`)
  matches `InfiniteTypeConstructions.lean:9779-9809`. Same walk-trimming
  via `walk_to_nodup_path`, same `chain.length ≥ 3` derivation from
  non-adjacency. Note `walk_to_nodup_path` was de-privatised by #2952
  (`InfiniteTypeConstructions.lean:8857-8860`, +2/-2) so the port can
  reuse rather than re-prove — independently confirmed in this file's
  diff.
- **Side-arm extraction** (`FieldGenericNonAdjacentBranches.lean:198-209`)
  matches `InfiniteTypeConstructions.lean:9858-9869`.
- **Arm₁/arm₂ extraction** (`FieldGenericNonAdjacentBranches.lean:226-241`)
  matches `InfiniteTypeConstructions.lean:9888-9902`.
- **Distinctness lattice** — `leaf_ne_chain`
  (`FieldGenericNonAdjacentBranches.lean:264-280`),
  `side_ne_chain` (282-320), `arm₁_ne_chain` (322-356),
  `arm₂_ne_chain` (358-392) — all four use the same proof strategy as
  the universal (idx-zero / idx-one direct, idx≥2 via
  `acyclic_path_nonadj`), with prefix/suffix split for v₀-anchored vs
  w-anchored vertices. Sub-proofs are line-for-line equivalent to
  `InfiniteTypeConstructions.lean:9929-10062`.
- **Cross-region distinctness** — `hleaf_ne_arm₁`, `hleaf_ne_arm₂`
  (`FieldGenericNonAdjacentBranches.lean:394-397`), `side_arm_ne_arm`
  helper (399-442) — match `InfiniteTypeConstructions.lean:10063-10116`.

The per-(F, Q) port does **not** silently weaken hypotheses relative to
the universal. Every Nodup / non-adjacency fact consumed by Phase 2
cases is genuinely derived from inputs in Phase 1; none is assumed.

The signature differs from the universal only by (a) carrying
`h_v₀w_nonadj` as a direct hypothesis (vs the universal deriving it
from the broader `h_adj_exists`), and (b) splitting `h_no_adj_branch`
into separate v₀-side / w-side hypotheses — both differences are
inherited from the stub signature (#2941, audited PASS in #2948) and
neither weakens the lattice. No orientation-related Phase 1 hypothesis
is needed (the orientation enters only at the embedder dispatch).

## D2 — Per-case vertex map + embedder argument check

### Case A (PR #2956), `FieldGenericNonAdjacentBranches.lean:464-513`: **PASS**

Entry condition: `hA : 6 ≤ chain.length ∧ vertexDegree adj side_arm = 2`.
Dispatch: `embed_t125_in_tree_per_kQ` (signature at
`FieldGenericT125.lean:71-91`) with vertex tuple
`v₀ leaf side_arm x chain[1..5]`. Map matches the docstring at
`FieldGenericNonAdjacentBranches.lean:501-503`.

Verified parameter-for-parameter:
- Edges (`hu₁, hp₁, hp₂, hq₁..hq₅`) ↔ `h_leaf_adj, hside_adj, hx_adj,
  hc1_adj, hc12, hc23, hc34, hc45` — all derived in Phase 1 except
  `hx_adj` (extracted at line 478-479 from the
  `vertexDegree adj side_arm = 2` Finset analysis).
- Distinctness (`hu₁_ne_p₁ … hq₅_ne_q₃`) ↔
  `hside_ne_leaf.symm, hleaf_ne_c1, hside_ne_c1, hx_ne_v₀, hc2_ne_v₀,
   hc3_ne_c1, hc4_ne_c2, hc5_ne_c3` — all derivable in O(1) from
  Phase 1 + `hchain_nodup.get_inj_iff`. Spot-checked `hc3_ne_c1`,
  `hc5_ne_c3` at 494-499.
- `F`, `Q`, `hOrient` threaded unchanged.
- Conclusion `¬ Set.Finite {…}` matches outer goal parameter-for-parameter.

### Case B.1 / B.2 (PR #2958), `FieldGenericNonAdjacentBranches.lean:517-635`: **PASS**

Entry: `hB : 6 ≤ chain.length ∧ (arm₁.deg = 2 ∨ arm₂.deg = 2)`.
Inner `rcases` on `harm_deg2_or` gives sub-cases B.1 (arm₁ extends) and
B.2 (arm₂ extends).

**B.1** dispatch (599-610): `embed_t125_in_tree_per_kQ` with vertex
tuple `w arm₂ arm₁ y chain[len-2..len-6]`. Verified:
- `v₀ → w`, `u₁ → arm₂` (length-1 arm), `p₁ → arm₁` (length-2 arm
  root), `p₂ → y` (length-2 arm tip), `q₁..q₅ → chain[len-2..len-6]`
  (length-5 arm reversed back from w).
- Edges thread reversed chain facts `hcR_2_3, hcR_3_4, hcR_4_5,
  hcR_5_6` (defined 553-564 from forward `hcL_*` via `adj_comm`).
- Distinctness: `harm₁₂.symm` for `arm₂ ≠ arm₁`, `harm₂_ne_pre` for
  `arm₂ ≠ chain[len-2]`, `harm₁_ne_pre` for `arm₁ ≠ chain[len-2]`,
  `hy_ne_w`, `hc_3_ne_w`, `hc_4_ne_2`, `hc_5_ne_3`, `hc_6_ne_4` —
  spot-checked Nodup-pair derivations at 566-580.

**B.2** dispatch (624-635): symmetric; verified `harm₁_adj`,
`harm₂_adj` swap and `harm₁₂` (not `.symm`) is now the correct
`u₁ ≠ p₁` direction.

`hOrient` threaded unchanged. Goal matches.

### Case C.main (PR #2961), `FieldGenericNonAdjacentBranches.lean:637-698`: **PASS**

Entry: `hC : 4 ≤ chain.length ∧ chain.length < 6 ∧
vertexDegree adj side_arm = 2`. Inner `by_cases hxdeg : x.deg = 2`
gates the C.main vs C.short branches. The audit scope here is
C.main only (lines 654-698); the C.short branch (699-895) was
introduced later by PRs #2966 / #2970, not in this audit's scope.

C.main dispatch (688-698): `embed_etilde7_in_tree_per_kQ` (signature
at `FieldGenericETilde7.lean:356-376`) with vertex tuple
`v₀ leaf side_arm x x' chain[1] chain[2] chain[3]`. Map matches the
docstring at 685-687.

Verified parameter-for-parameter:
- 8 vertices, 7 edges: `h_leaf_adj` (v₀-leaf), `hside_adj` (v₀-side_arm),
  `hx_adj` (side_arm-x), `hx'_adj` (x-x', extracted 663-668 from the
  `vertexDegree adj x = 2` Finset analysis), `hc1_adj` (v₀-chain[1]),
  `hc12`, `hc23`.
- 7 distinctness: `hside_ne_leaf.symm` (leaf≠side_arm),
  `hleaf_ne_c1` (leaf≠chain[1]), `hside_ne_c1` (side_arm≠chain[1]),
  `hx_ne_v₀`, `hc2_ne_v₀`, `hx'_ne_side`, `hc3_ne_c1` — all derivable
  in O(1) from Phase 1 + Finset.ne_of_mem_erase.
- `hOrient` threaded unchanged.

Description nit: the issue body says "Case C (`side_arm.deg = 2 ∧
x.deg = 2`)" but the outer `by_cases hC` only checks
`side_arm.deg = 2`; the `x.deg = 2` filter is inside (line 654). Not
a correctness issue — just imprecise phrasing in the issue body.

### Case D (PR #2961), `FieldGenericNonAdjacentBranches.lean:899-958`: **PASS**

Entry: `hD : 4 ≤ chain.length ∧ chain.length < 6 ∧ arm₁.deg = 2 ∧
arm₂.deg = 2`. Dispatch: `embed_etilde6_in_tree_per_kQ` (signature
at `FieldGenericETilde6.lean:372-391`) with vertex tuple
`w chain[len-2] chain[len-3] arm₁ y₁ arm₂ y₂`. Map matches the
docstring at 946-948.

Verified parameter-for-parameter:
- 7 vertices for T(2, 2, 2), 6 edges: `hw_chain_adj` (w-chain[len-2]),
  `hcR_2_3` (chain[len-2]-chain[len-3]), `harm₁_adj`, `hy₁_adj`,
  `harm₂_adj`, `hy₂_adj`. `y₁`, `y₂` extracted at 902-928 from the
  arm₁.deg = 2 and arm₂.deg = 2 Finset analyses.
- 6 distinctness: `harm₁_ne_pre.symm` (chain[len-2]≠arm₁),
  `harm₂_ne_pre.symm` (chain[len-2]≠arm₂), `harm₁₂` (arm₁≠arm₂),
  `hc_3_ne_w`, `hy₁_ne_w`, `hy₂_ne_w` — all derivable in O(1) from
  Phase 1 + Finset.ne_of_mem_erase + Nodup-pair.
- `hOrient` threaded unchanged.

Note: the embedder takes only 6 distinctness facts (the C(7, 2) = 21
remaining are derived inside the embedder using `acyclic_no_triangle`
and the cycle-via-acyclicity tooling — verified by reading
`FieldGenericETilde6.lean:399-460`). Same pattern the prior audit
#2949 confirmed PASS.

## D3 — Case coverage exhaustiveness: **PASS**

The Phase 2 by_cases ladder in `FieldGenericNonAdjacentBranches.lean`:

| Line | Cond | True branch | False branch |
|------|------|-------------|--------------|
| 464  | `hA = 6 ≤ chain.length ∧ side.deg = 2` | Case A → embed T(1,2,5) | line 515 |
| 515  | `hB = 6 ≤ chain.length ∧ (arm₁.deg = 2 ∨ arm₂.deg = 2)` | Case B.1/B.2 → embed T(1,2,5) | line 637 |
| 637  | `hC = 4 ≤ chain.length ∧ chain.length < 6 ∧ side.deg = 2` | Case C (with internal C.main/C.short split) | line 897 |
| 897  | `hD = 4 ≤ chain.length ∧ chain.length < 6 ∧ arm₁.deg = 2 ∧ arm₂.deg = 2` | Case D → embed Ẽ₆ | line 959 (sorry) |

Lean's `by_cases` produces `P ∨ ¬P`, so no fifth case can be silently
dropped. With `chain.length ≥ 3` from Phase 1, the residual `sorry` at
line 969 covers exactly:
- `chain.length = 3` (D̃₅ embedding — tracked by #2955),
- `chain.length ∈ {4, 5}` with `side.deg ≠ 2` and not both
  `arm₁.deg = arm₂.deg = 2` (asymmetric short-chain cases — tracked
  by #2955),
- `chain.length ≥ 6` with `side.deg ≠ 2` and `arm₁.deg ≠ 2` and
  `arm₂.deg ≠ 2` (long-chain all-leaves — tracked by #2955).

These residual sub-cases align with the sub-issue breakdown documented
in `progress/20260519T025228Z_c8368183.md` ("Current frontier"
section).

PRs #2966 (Case C.short tractable sub-cases) and #2970 (Case C.short
all-leaves chain.length = 4) carved sub-cases out of the original
C.short `sorry` at line 699; these are in the audited file as of
`b1f8b7f` but were introduced after the four audited PRs and are out
of scope for this audit. They do not affect the Cases A/B/C-main/D
coverage analysis above.

The `let _ := …` bindings at 964-968 are idiomatic placeholders for
Phase 1 hypotheses that are not yet consumed by the Case E sorry but
remain in scope for the upcoming Case E proof; they are not dead code.

## D4 — Build sanity: **PASS**

```
$ git rev-parse HEAD
b1f8b7f447882414401d56bcf07c24edc7c48406

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches
…
⚠ [8047/8047] Built EtingofRepresentationTheory.Chapter6.FieldGenericNonAdjacentBranches (16s)
warning: EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean:88:8: declaration uses `sorry`
Build completed successfully (8047 jobs).

$ lake build EtingofRepresentationTheory.Chapter6.FieldGenericAssembly
…
✔ [8049/8049] Built EtingofRepresentationTheory.Chapter6.FieldGenericAssembly (33s)
Build completed successfully (8049 jobs).
```

Full sorry-warning list from the assembly build (`/tmp/build-assembly.log`):
```
EtingofRepresentationTheory/Chapter6/FieldGenericD5Tilde.lean:798:8       (pre-existing, indecomposability)
EtingofRepresentationTheory/Chapter6/FieldGenericD5Tilde.lean:974:8       (pre-existing)
EtingofRepresentationTheory/Chapter6/FieldGenericD7Tilde.lean:247:8       (introduced by #2968, tracked by #2967)
EtingofRepresentationTheory/Chapter6/FieldGenericETilde6.lean:291:8       (pre-existing, indecomposability)
EtingofRepresentationTheory/Chapter6/FieldGenericETilde7.lean:273:8       (pre-existing, indecomposability)
EtingofRepresentationTheory/Chapter6/FieldGenericNonAdjacentBranches.lean:88:8  (audited file — Case E residual line 969, tracked by #2955)
EtingofRepresentationTheory/Chapter6/FieldGenericStar.lean:543:8          (pre-existing)
EtingofRepresentationTheory/Chapter6/FieldGenericT125.lean:39:8           (pre-existing)
EtingofRepresentationTheory/Chapter6/FieldGenericTpqr.lean:1233:8         (pre-existing)
EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean:3331:8  (pre-existing)
EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean:3588:8  (pre-existing)
EtingofRepresentationTheory/Chapter6/InfiniteTypeConstructions.lean:3815:8  (pre-existing)
```

For the audited file, only the Case E residual (line 969 of
`FieldGenericNonAdjacentBranches.lean`, declaration on line 88)
remains. No additional sorries were introduced by the four audited
PRs.

Cosmetic linter warnings in `FieldGenericT125.lean` (long-line at
lines 345, 352, 363, 370, 377, 389) are pre-existing and unrelated.

## D5 — Stale docstring / dead-code spot-check: **CONCERN** (non-blocking)

The file-level docstring at `FieldGenericNonAdjacentBranches.lean:13-53`
has not been refreshed as Cases A-D and the D̃₇ helper landed.
Concretely:

1. **Lines 28-34** (available "fixed-`n` leaves" list): missing
   `d7tilde_not_finite_type_per_kQ` — introduced by #2968 alongside
   the new `FieldGenericD7Tilde.lean` module (imported at line 8).
   Previously flagged in
   `progress/20260519T044657Z_8cb2f5ad.md`; the four audited PRs did
   not refresh it (and none was responsible for adding D̃₇ — #2968
   was).
2. **Lines 36-38** (strategy summary "embed one of the available
   fixed-shape forbidden subgraphs (`Ẽ₆`, `Ẽ₇`, `T(1, 2, 5)`)"):
   missing `D̃₇`.
3. **Lines 40-52 ("## API stub" section)**: stale. The body is no
   longer a `sorry` API stub — Cases A/B/C-main/D have landed; only
   Case E remains. PR #2952 onwards did not refresh this section.
4. **Theorem docstring at lines 83-87** ("**API stub** (issue #2922):
   the body is `sorry` pending the proof tracked by issue #2932…"):
   stale by the same argument.

The Phase 2 dispatcher overview comment at lines 446-463 is also
slightly stale: Case E (line 462) is described as "`chain.length = 3`:
dispatch to a D̃₅-style embedding" — accurate for the chain.length = 3
sub-case, but Case E now also covers the all-leaves residual at
chain.length ≥ 6 and asymmetric short-chain residuals. Tracked by
#2955.

**Not introduced by the four audited PRs** — most of the staleness was
caused by subsequent PRs (#2966 carving up C.short, #2968 adding D̃₇,
#2970 closing chain.length = 4 all-leaves) failing to refresh the
docstring. Recording as CONCERN per the audit's non-blocking criterion;
suggest a docstring-refresh follow-up issue rather than fixing in this
review.

No dead `import` lines or orphaned helper lemmas found. The
`let _ := …` bindings in Case E (lines 964-968) are idiomatic
"these will be consumed when Case E is filled in" markers, not dead
code (see D3).

## Recommendation

All four PRs pass on D1-D4. The recurring concern from prior audits
(D3-style signature shadow-weakening in case branches) does **not**
apply: the Phase 1 lattice is consumed without strengthening or
weakening in any of Cases A, B, C-main, D — the per-case Finset
extractions (e.g. `x`, `y`, `y₁`, `y₂`) introduce genuinely new
distinctness facts only, never weaken inherited ones.

Suggest opening a docstring-refresh follow-up issue (file-level
docstring at lines 13-53 + theorem docstring at lines 83-87) once the
remaining Case E sub-cases land. No urgency.

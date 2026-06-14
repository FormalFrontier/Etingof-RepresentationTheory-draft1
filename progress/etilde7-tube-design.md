# Per-shape design: Ẽ₇ = T(1,3,3) homogeneous-tube indecomposable (#4558)

**Issue:** #4558 (sub-3 of #4548). Replaces the refuted single-nilpotent-twist
`etilde7Rep_kQ` with a homogeneous tube whose `_isIndecomposable` lemma is a
*true* statement.
**Parent design:** `progress/sporadic-tube-redesign-design.md`.
**Refutation:** `progress/indecomposability-framework-investigation.md` §1.
**Foundational mechanism (landed):** `Chapter6/FieldGenericTube.lean`
(`eigenvalue_jordan_invariant_compl_trivial_gen`, D̃₄ validation
`starTubeRepGen_isIndecomposable`).

This note scopes the T(1,3,3) work into sub-A/sub-B/sub-C. It records the one
non-obvious mathematical finding from this session (the naive swap fails) and
fixes the construction shape so the sub-issues are self-contained.

## 1. Data

`δ = etilde7Dim m`, with the dimension vector laid out by vertex
(`InfiniteTypeConstructions.lean:3382`):

| v | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| dim | 4(m+1) | 2(m+1) | 3(m+1) | 2(m+1) | (m+1) | 3(m+1) | 2(m+1) | (m+1) |

So `δ = (4; 2; 3,2,1; 3,2,1)` (center 4; short arm mark 2; two long arms
`3,2,1`). This is exactly the Ẽ₇ Coxeter labelling. Canonical sink orientation
`etilde7Quiver` points every arrow at the center:
`1→0`, `4→3→2→0`, `7→6→5→0`.

Any construction must keep the per-vertex object `Fin (etilde7Dim m v) → F`
unchanged so that `etilde7Rep_kQ_dimVec` (`FieldGenericETilde7.lean:223`,
proved by `LinearEquiv.refl`) and the two live downstream consumers
(`FieldGenericTpqr`, `FieldGenericNonAdjacentBranches`, via
`etilde7_not_finite_type_per_kQ`) keep their statements.

## 2. Finding: swapping `N ↦ λI+J` in arm 1 alone does **not** work

The current arm-1 map `etilde7Arm1Embed_F` is `(p,q) ↦ (p+q, p, q, Nq)`, with
`N` the rank-deficient nilpotent shift; the `e_m` direction of center block `D`
is never reached, and the §1 refutation peels it off via **arm 3**
(`embed3to4_ACD_F : (a,b,c) ↦ (a,0,b,c)` covers center blocks A,C,D).

Replacing `N` by the square `λI+J` makes block `D = (λI+J) q` full rank, but
this is **not sufficient**: arm 3 still reaches `(0,0,0,e_m)` independently of
arm 1 (it is `embed3to4_ACD_F (0,0,e_m)`), so the §1 complementary pair
`W'(0) = ⟨(0,0,0,e_m)⟩`, `W'(5) = ⟨(0,0,e_m)⟩` survives unless the arm-3 chain
is *also* reshaped to tie block D to the eigenvalue site. This matches the
parent design's §3 obstruction note: "δ is non-constant, so the eigenvalue λ is
encoded in the **rectangular** maps rather than in a square `λI+J`; deriving
those matrices is the real per-shape work." A one-arm swap is the trap to avoid.

## 3. Construction target (what sub-A must build)

A genuine regular-simple tube `R_λ^{(m+1)}` at `(m+1)·δ`, shaped so the
collapse machinery (`compl_le_forces_eq` / the `core` + `propagate` pattern of
`starTubeRepGen_isIndecomposable`) forces every vertex onto a single common
`F^{m+1}` carrying `λ•id + J`, where
`eigenvalue_jordan_invariant_compl_trivial_gen` finishes.

Recommended shape (tensor model). Write each vertex space as
`F^{δ_v} ⊗ F^{m+1}`. Take the regular simple `S_λ` of T(1,3,3) at dimension
`δ = (4;2;3,2,1;3,2,1)` — a tree quiver, so **any** choice of full-column-rank
arm maps is a valid representation (no relations to check); the only real
obligation is that the chosen maps put the three arm flags in general enough
position that the **only** complementary invariant pairs are the ones the
eigenvalue site controls. The tube is `S_λ ⊗ I_{m+1}` on every arm map *except*
the single λ-bearing map, which becomes `M_λ ⊗ I_{m+1} + (∂_λ M) ⊗ J_{m+1}`,
so that exactly one site sees `λ•id + J`. Concretely:

- Center `V0 = F^4 ⊗ F^{m+1}`, blocks `B1,B2,B3,B4`.
- The two long-arm flags and the short-arm 2-plane must be arranged so that the
  collapse forces `W(0)` block-diagonal with all four block-restrictions equal
  to one `U ⊆ F^{m+1}`, and the λ-bearing map deposits a `(λ•id+J)`-invariant
  pair on `U`. (This is the D̃₄ picture with four blocks instead of two and one
  extra hop per long arm.)

Acceptance for sub-A: `m = 1` must defeat the §1 peeling pair, i.e. there is no
free `e_1`-in-block-D direction because every center block is tied through the
square `λ•id+J` site. The deliverable is the new `def etilde7Rep_kQ` body (real
object, no sorry in the `def`) + the re-proved `etilde7Rep_kQ_dimVec` (still
`refl`). The explicit rectangular matrices of `S_λ` are the genuinely-open part
and are this sub-issue's core work.

## 4. Orientation-generic case tree (sub-B)

`etilde7Rep_kQ` is built for an **arbitrary** orientation `Q` of `etilde7Adj`
(seven edges, each can point either way → forward + reverse map per edge). The
indecomposability proof therefore needs the per-orientation **leaf-equality**
case tree exactly as the D̃₅/D̃₆/D̃₇ programs did (`d5tildeRep_kQ_leaf_equalities`
& friends): for each edge direction, show the corresponding `W₁(leaf)` equalities
that drive the collapse. Reuse the landed reductions in `FieldGenericStar.lean`
(`reversed_leaf_subspace_eq`, `forward_leaf_subspace_eq`) and the N-invariance
infrastructure from #4554. This is the bulk of the remaining proof volume and is
independent of sub-A's matrix choice up to the interface
(`leaf_equalities` statement).

## 5. Indecomposability assembly + re-point (sub-C)

Assemble `etilde7Rep_kQ_isIndecomposable` (no sorry) from sub-A's construction
and sub-B's leaf equalities via the `core`/`propagate` +
`eigenvalue_jordan_invariant_compl_trivial_gen` reduction
(`starTubeRepGen_isIndecomposable` is the template). `etilde7_not_finite_type_per_kQ`
keeps its statement (it already consumes `_isIndecomposable`); rebuild
`FieldGenericTpqr` and `FieldGenericNonAdjacentBranches`.

## 6. Decomposition

- **sub-A** (no dep): derive `S_λ` matrices + build tube `def etilde7Rep_kQ` +
  `etilde7Rep_kQ_dimVec`. Soundness win lands here even before the proof: the
  `_isIndecomposable` sorry becomes a sorry of a *true* statement.
- **sub-B** (no hard dep on sub-A; shares the `leaf_equalities` interface):
  orientation-generic leaf-equality case tree.
- **sub-C** (depends on sub-A and sub-B): indecomposability assembly + re-point
  consumer + rebuild downstream.

Do **not** re-file sub-sorries against the old refuted single-twist shape.

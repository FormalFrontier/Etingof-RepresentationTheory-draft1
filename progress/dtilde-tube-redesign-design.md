# Design: corrected indecomposable family for the D̃ affine base cases

**Issue:** #4647 (D̃₅ pattern-setter), parent #4597. Consumed by the
D̃₆/₇/₈/parametric sub-issues #4649 / #4650 / #4651 / #4652.
**Refutation context:** #4566, and the m=1 combo-C counterexample in the
closing comment of #2853.
**Mechanism:** `eigenvalue_jordan_invariant_compl_trivial_gen` (#4555,
`FieldGenericTube.lean:77`).
**Closest worked precedents:** the sporadic tube redesigns #4557 (Ẽ₆) /
#4558 (Ẽ₇) / #4559 (T(1,2,5)) and `progress/sporadic-tube-redesign-design.md`;
the actual Lean model `FieldGenericT125.lean` (eigenvalue tube + flag
collapse). **Author:** work session `925c806e`, 2026-06-15.

This is the D̃-family analogue of `progress/sporadic-tube-redesign-design.md`.
It is *not* a proof; it fixes the construction, the one reduction template the
existing machinery already supports, the **two-degree-3-vertex** coupling that
the sporadic single-center shapes do not exercise, and an honest statement of
what each implementing sub-issue must still derive.

## 0. The D̃ family shape (what makes it the pattern-setter)

The affine diagram D̃_n (`n+1` vertices) is a **central path** with a fork
(two leaves) at each **end**:

```
0           4              0       (chain of degree-2)      4
 \         /                \                              /
  2 ----- 3        D̃₅;       2 -- c₁ -- c₂ -- … -- c_k -- 3   D̃_{k+5}
 /         \                /                              \
1           5              1                                5
```

- **D̃₄** = the K_{1,4} star: a *single* degree-4 center, 4 leaves. Already
  done: `starTubeRepGen` / `starTubeRepGen_isIndecomposable`
  (`FieldGenericTube.lean`). One eigenvalue site, no central edge.
- **D̃₅** (this issue): **two** degree-3 centers `2, 3` joined by the single
  central edge `{2,3}`, leaves `{0,1}` at `2` and `{4,5}` at `3`. This is the
  smallest shape with the **two-fork / central-edge** coupling, absent from
  every sporadic single-center shape. Its corrected construction is therefore
  the pattern-setter for the whole D̃ family.
- **D̃₆ / D̃₇ / D̃₈ / D̃_{k+5}**: the same two end-forks, with a chain of
  `k ≥ 1` extra **degree-2 pass-through** centers inserted between them.

Adjacency / dimension vector for D̃₅ (`d5tildeAdj`,
`InfiniteTypeConstructions.lean:1369`; `d5tildeDim`,`:1527`):
edges `{0,2},{1,2},{2,3},{3,4},{3,5}`; `δ = d5tildeDim 0 = (1,1,2,2,1,1)`
over vertices `(0,1,2,3,4,5)`. The tube at level `m` has dim vector
`(m+1)·δ = d5tildeDim m`: leaves `m+1`, the two centers `2(m+1)`.

The whole δ-mass on the central path is `2`; the four leaf marks are `1`. So
the central path of every D̃ shape carries `F^{2(m+1)} = F^{m+1} ⊕ F^{m+1}`
at each vertex, the four leaves carry `F^{m+1}`, and the single eigenvalue
parameter `λ` lives in **one** central map. The degree-2 pass-through centers
of D̃₆₊ are joined to their neighbours by honest block isos that the
collapse step treats exactly as the cycle-pattern identity arrows.

## 1. What is broken, in one paragraph

`d5tildeRep_kQ` (`FieldGenericD5Tilde.lean:166`) joins its two centers by the
**iso bridge** `γ = d5tildeGamma_F = [[I, I], [I, N]]` (`:55`), where `N` is the
rank-deficient nilpotent shift `nilpotentShiftLinGen` (`N e_i = e_{i-1}`,
`N e_0 = 0`; image `⟨e_0,…,e_{m-1}⟩` **misses** the `e_m` direction). For the
**canonical** orientation this is fine — the ℂ-source `d5tildeRep_isIndecomposable`
(`InfiniteTypeConstructions.lean:1569`) is a *correct* proof: the iso `γ` ties
the two centers' decompositions together so all four leaves are forced equal,
then `nilpotent_invariant_compl_trivial_gen` finishes. But for **mixed /
reversed** orientations the central edge is reversed (`3→2` uses `γ⁻¹`, which
carries the twist `M = (I − N)⁻¹`, `gammaInv` `:109`), and the available edges
force only `M(W⟨5⟩) = W⟨0⟩` with **no edge supplying leaf `N`-invariance**. The
rank-deficient `N` leaves the `e_m` direction unconstrained, so a 1-dimensional
complementary summand peels off: `d5tildeRep_kQ_leaf_equalities` (`:793`) is
**false** in the mixed branches (explicit m=1 combo-C counterexample, #2853),
and `d5tildeRep_kQ_isIndecomposable` (`:1086`) is a `sorry` of a false-on-the-
current-rep statement. The infinite-type conclusion
`d5tilde_not_finite_type_per_kQ` (`:1111`) is **true** (D̃₅ is affine = infinite
type for every orientation) but currently routes through that false lemma.

## 2. The fix, in one line

Replace the rank-deficient nilpotent `N` in the central map with the **full-rank
eigenvalue site** `Λ = λ·id + J` (`jordanShiftLinGen F lam m`,
`FieldGenericTube.lean:115`), `λ` generic. Nothing else about the construction
changes: the four leaf maps stay `starEmbed1_F` / `starEmbed2_F` (canonical) and
`starFirst_F` / `starSecond_F` (reversed).

```
d5tildeGamma_F      = [[I, I], [I, N]]        (refuted: N rank-deficient)
d5tildeGammaTube_F  = [[I, I], [I, Λ]]        (corrected: Λ = λ·id + J, full rank)
```

Two independent things go wrong with `N` and are both repaired by `Λ`:

1. **Rank.** `Λ = λ·id + J` is invertible for `λ ≠ 0` (eigenvalue `λ ≠ 0`),
   so its image is all of `F^{m+1}` — there is no missed `e_m` direction for a
   complementary summand to peel off. `N` (image misses `e_m`) is exactly the
   under-coupling of #4566 / §1.
2. **Splitting.** `Λ` and `J` have the **same invariant subspaces** (`λ·id`
   maps every subspace to itself), so the eigenvalue `λ` drops out of the
   final splitting argument: `eigenvalue_jordan_invariant_compl_trivial_gen`
   reduces a `(λ·id + J)`-invariant complementary pair to a `J`-invariant one,
   which `nilpotent_invariant_compl_trivial_gen` (1-dim kernel) kills. So `λ`
   makes the simple simple; `J` drives the indecomposability of the tube.

This is precisely the sporadic-doc §3 dichotomy, now applied at a central edge
rather than a leaf arm.

## 3. Why the corrected central map is a regular simple (m = 0 sanity check)

At `m = 0` (`δ` itself) every space is a line/plane: leaves `F`, centers `F²`,
`Λ = (λ)`. Leaf maps: `starEmbed1 = e_0`, `starEmbed2 = e_1` at both centers.
The corrected central iso `γ_λ : (x,y) ↦ (x + y, x + λy)` is invertible for
`λ ≠ 1` (`det = λ − 1`). The four lines visible in `V₃ = F²` are

```
γ_λ⟨e_0⟩ = ⟨(1,1)⟩,  γ_λ⟨e_1⟩ = ⟨(1,λ)⟩    (transported from center 2)
⟨e_0⟩ = ⟨(1,0)⟩,      ⟨e_1⟩ = ⟨(0,1)⟩         (center-3 leaves)
```

These are four **distinct** points of `P¹(F²)` iff `λ ∉ {0, 1, ∞}`; in general
position they admit no proper nonzero subrepresentation, i.e. the dim-`δ` rep
is the **regular simple** `R_λ` (homogeneous point of the D̃₅ tubular `P¹`
family, cross-ratio `λ`). The level-`m` tube `R_λ^{(m+1)}` thickens each line
to an `(m+1)`-block and replaces the scalar `λ` at the single eigenvalue site
by the Jordan block `Λ = λ·id + J`. The choice of generic `λ` over an
algebraically closed `F` is the `t125TubeLam`-style "distinct powers" pick
(`FieldGenericT125.lean:107`); any `λ ∉ {0,1}` works for D̃₅.

## 4. The reduction template (already supported by the machinery)

The proof shape is the **two-center** version of the D̃₄ star proof
`starTubeRepGen_isIndecomposable` (`FieldGenericTube.lean:174`), which is the
cleanest model to mirror. For a complementary invariant pair `(W₁, W₂)`:

1. **Leaf collapse at each center** (the `core` / `compl_le_forces_eq`
   move, reused from the star and cycle proofs). The leaf embeddings are
   injective half-block maps; complementarity + the center decomposition
   `center_decomp_F` force the two leaf subspaces around center 2 equal to a
   common `U₂ ⊆ F^{m+1}`, and likewise `U₃` around center 3.
2. **Central transport.** The central edge (forward `γ_λ`, or reverse
   `γ_λ⁻¹` in a reversed orientation) is an **isomorphism that is a polynomial
   in `J` blockwise**: `γ_λ`, `γ_λ⁻¹`, `Λ`, `Λ⁻¹`, `(Λ−I)⁻¹` all share the
   `J`-invariant-subspace lattice. Transporting the center-2 decomposition
   across it pins `U₂` and `U₃` to a **single** `F^{m+1}` carrying a
   `(λ·id + J)`-invariant complementary pair — in *every* orientation, because
   the twist is always invertible and `J`-polynomial (this is the step the
   rank-deficient `N` could not perform in the reversed orientation).
3. **Workhorse.** `eigenvalue_jordan_invariant_compl_trivial_gen Λ … λ` drops
   `λ` and applies `nilpotent_invariant_compl_trivial_gen` (`J` nilpotent,
   `dim ker J = 1`) to force one component `⊥`; `propagate` pushes `⊥` back out
   to every vertex through the (now invertible) maps.

The reverse central map is the closed-form inverse of `[[I,I],[I,Λ]]`:

```
γ_λ⁻¹ = [[ I + (Λ−I)⁻¹,  −(Λ−I)⁻¹ ],
         [    −(Λ−I)⁻¹,   (Λ−I)⁻¹ ]]          (Λ − I) invertible for λ ≠ 1
```

`(Λ − I)⁻¹ = ((λ−1)·id + J)⁻¹` is the eigenvalue-`(λ−1)` geometric series, the
`Λ`-analogue of the nilpotent `cumTailSumLin = (I − N)⁻¹` already in
`FieldGenericStar.lean`. It is again a polynomial in `J`, so step 2 goes
through identically in the reversed-central orientation — the combo-C branch
that refuted the old construction.

## 5. Framework decision: submodule route, not `End`-local

As in the sporadic doc §4: **do not** build `End`-is-local infrastructure. The
invariant-submodule-splitting route is the established technology, every D̃
shape reduces to it through §4, and the workhorse + reduction lemma already
exist. Shape every construction so that any complementary invariant pair is
forced down to a complementary `J`-invariant pair of a single `F^{m+1}` at the
eigenvalue site.

## 6. Per-shape work that remains (honest open part)

For D̃₅ (this issue's deliverables 2–4), and as the template for D̃₆₊:

1. **Corrected maps** (sub-A): `d5tildeGammaTube_F F lam m = [[I,I],[I,Λ]]`
   and its inverse `d5tildeGammaTubeInv_F F lam m` (closed form §4, built from
   `starEmbed1_F`/`starEmbed2_F`/`starFirst_F`/`starSecond_F` and a
   `Λ`-geometric-series `(Λ−I)⁻¹` primitive — the eigenvalue analogue of
   `cumTailSumLin`). Real `def`s, no sorry'd bodies. Swap them into
   `d5tildeRepMap_kQ` for the `{2,3}` edge; thread the `lam` parameter through
   `d5tildeRep_kQ` (pick `lam := d5tildeTubeLam F` generic, mirroring
   `t125TubeLam`). Keep the dim vector exactly `d5tildeDim m` so
   `d5tildeRep_kQ_dimVec` keeps its statement. **Open:** the closed-form
   `γ_λ ∘ γ_λ⁻¹ = id` (the ℂ-source skipped its `N`-analogue; the eigenvalue
   version is genuinely needed for the reversed-central branch) and the
   `Λ`-geometric-series retraction lemmas.
2. **Orientation-generic leaf equalities** (sub-B): re-prove
   `d5tildeRep_kQ_leaf_equalities` (now **true in all branches**) on the
   corrected rep. The all-canonical and all-leaves-reversed (combo-D) branches
   of the *old* proof are reusable for the leaf arms; the central-edge
   transport (steps 2 of §4) is rewritten around `Λ`/`γ_λ⁻¹`. Acceptance: the
   m=1 combo-C orientation (#2853) now satisfies the equalities. Replaces the
   three remaining `sorry`s at `:1042/:1044/:1046` and removes the false-branch
   problem entirely.
3. **isIndecomposable assembly** (sub-C): close `d5tildeRep_kQ_isIndecomposable`
   for all `m ≥ 1` and all orientations via the §4 reduction (leaf collapse →
   single `Λ`-invariant splitting → `eigenvalue_jordan_invariant_compl_trivial_gen`).
   Mirror `starTubeRepGen_isIndecomposable`'s `core` / leaf-`sub` / `propagate`
   skeleton, generalised to two centers joined by `γ_λ`. Then **re-point**
   `d5tilde_not_finite_type_per_kQ` (statement unchanged) and verify the
   downstream consumers `FieldGenericTpqr`, `FieldGenericNonAdjacentBranches`,
   `FieldGenericAssembly`, `adjacent_branches_infinite_type_per_kQ`, and any
   `d5tilde_subgraph_*` still build against the new `lam`-threaded signature.

Do **not** re-file "fill the old `d5tildeRep_kQ_isIndecomposable`/`leaf_equalities`
sorry" against the refuted `[[I,I],[I,N]]` rep — that statement is false there.

## 7. Recommended decomposition (this issue)

Mirrors the D̃₆/₇/₈ sub-A/B/C program:

- **sub-A**: corrected `d5tildeGammaTube_F` / `d5tildeGammaTubeInv_F` +
  `Λ`-geometric-series primitive + `γ_λ ∘ γ_λ⁻¹ = id`; re-point `d5tildeRep_kQ`
  (thread `lam`), keep `d5tildeRep_kQ_dimVec`. Leaf-equality / isIndecomposable
  lemmas may remain `sorry` (they are restated, not yet proven) but the file
  must build.
- **sub-B**: orientation-generic `d5tildeRep_kQ_leaf_equalities` on the
  corrected rep (true in all branches; combo-C acceptance test).
- **sub-C**: `d5tildeRep_kQ_isIndecomposable` assembly + re-point
  `d5tilde_not_finite_type_per_kQ` and rebuild downstream consumers.

For D̃₆₊ (#4649–#4652): same three-part split per shape, with the extra
degree-2 pass-through centers joined by block isos that collapse exactly like
the cycle-pattern identity arrows; the single eigenvalue site `γ_λ` lives on
one central edge, the rest of the central path is honest isos.

**sub-A for D̃₆₊ needs no new gamma defs** (verified on D̃₇, #4650): these
shapes differ from D̃₅ only by the internal identity chain plus the one central
edge, so sub-A is a mechanical swap — point the central `{2,3}` edge at the
already-merged D̃₅ `d5tildeGammaTube_F` / `d5tildeGammaTubeInv_F` (whose
retraction lemmas are also merged), thread `lam := d5tildeTubeLam F`, add
`[IsAlgClosed F]` to the rep `def` and every helper that mentions it, and
`sorry` the restated `leaf_equalities` (sub-B). The bottom theorems
(`isIndecomposable`, `not_finite_type_per_kQ`, the embed lemma) may already
carry `[IsAlgClosed F]`; check before editing. Confirm with a full
`lake build EtingofRepresentationTheory` — the ripple stays inside the shape's
own file in practice.

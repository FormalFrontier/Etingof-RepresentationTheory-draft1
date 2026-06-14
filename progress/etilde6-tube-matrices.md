# Ẽ₆ = T(2,2,2) homogeneous-tube: explicit regular-simple matrices

**Issue:** #4574 (sub-A of #4557). Supplies the rectangular-matrix derivation
that `sporadic-tube-redesign-design.md` §5 deferred ("the part **not** worked
out in this doc").

This note derives an explicit regular simple `R_λ` for the affine quiver
Ẽ₆ = T(2,2,2) at `δ = (3; 2,1; 2,1; 2,1)`, gives a paper proof it is a brick
for generic `λ`, and lifts it to the length-`(m+1)` homogeneous tube around the
eigenvalue site `λI + J`, matching `etilde6Dim (m+1)`.

## 1. The quiver

`etilde6Adj` edges: `{0,1},{1,2},{0,3},{3,4},{0,5},{5,6}`. Center vertex `0`
(dim `3` at `δ`); three arms, each `center 0 — mid — leaf`:

- arm A: mid `1` (dim 2), leaf `2` (dim 1)
- arm B: mid `3` (dim 2), leaf `4` (dim 1)
- arm C: mid `5` (dim 2), leaf `6` (dim 1)

Canonical reference orientation: all arrows point toward the center
(`2→1→0`, `4→3→0`, `6→5→0`). A representation is, per arm `i`, a leaf→mid map
`β_i : F¹ → F²` and a mid→center map `α_i : F² → F³`.

## 2. The regular simple `R_λ` at `m = 0`

Write the center `F³ = ⟨e₀, e₁, e₂⟩`. Each `α_i` is injective; its image is a
plane `π_i ⊂ F³`, and the leaf line `ℓ_i := im(α_i ∘ β_i) ⊂ π_i`. Take the
three **coordinate planes** and three lines positioned with modulus `λ`:

| arm | plane `π_i`           | line `ℓ_i`          | `α_i(p,q)`   | `β_i(x)`     |
|-----|------------------------|---------------------|--------------|--------------|
| A   | `⟨e₁,e₂⟩` (`x₀=0`)     | `⟨e₁+e₂⟩`           | `(0,p,q)`    | `(x,x)`      |
| B   | `⟨e₀,e₂⟩` (`x₁=0`)     | `⟨e₀+e₂⟩`           | `(p,0,q)`    | `(x,x)`      |
| C   | `⟨e₀,e₁⟩` (`x₂=0`)     | `⟨e₀+λe₁⟩`          | `(p,q,0)`    | `(x,λx)`     |

(Check: `α_A(1,1) = (0,1,1) ∈ ℓ_A`, `α_B(1,1) = (1,0,1) ∈ ℓ_B`,
`α_C(1,λ) = (1,λ,0) ∈ ℓ_C`.)

### Modulus

The subgroup of `GL₃` fixing the three coordinate planes is the diagonal torus
`diag(a,b,c)`. It moves the line slopes `s_A` (`ℓ_A = ⟨e₁+s_A e₂⟩`), `s_B`,
`s_C` by `s_A ↦ s_A·c/b`, `s_B ↦ s_B·a/c`, `s_C ↦ s_C·b/a`. The product
`s_A s_B s_C` is the **invariant**; with `s_A = s_B = 1`, `s_C = λ` it equals
`λ`. The three exceptional points (rank-3 tubes) are `λ ∈ {0, 1, ∞}`; every
other `λ` gives a homogeneous regular simple.

## 3. Brick proof (indecomposability at `m = 0`)

Suppose `F³ = S ⊕ S'` as subrepresentations, both nonzero. A subrep restricts
on the center to a subspace; complementarity forces, for **every** arm,

- `π_i = (π_i ∩ S) ⊕ (π_i ∩ S')` (the plane splits), and
- `ℓ_i ⊆ S` or `ℓ_i ⊆ S'` (the line, dim 1, lands wholly in one side).

WLOG `dim S = 1` (the `dim S = 2` case is dual). Write `S = ⟨v⟩`. For each `i`,
the plane condition forces either `S ⊆ π_i` or `π_i ⊆ S'`. Since `S'` is a
single 2-dim space it can equal at most one `π_i`, so at least two arms need
`S ⊆ π_i`, i.e. `v` lies on a coordinate axis `⟨e_k⟩`. Say `S = ⟨e₂⟩`
(`⊆ π_A, π_B`); the third arm then needs `S' = π_C = ⟨e₀,e₁⟩`. But then the
line `ℓ_A = ⟨e₁+e₂⟩` must lie in `S = ⟨e₂⟩` or `S' = ⟨e₀,e₁⟩` — it lies in
**neither** (it has both an `e₂` and an `e₁` component). Contradiction. Every
axis choice for `S` hits the same obstruction by symmetry. Hence `R_λ` is
indecomposable; being a regular simple it is a brick (`End R_λ = F`).

The key point versus the **refuted** single-twist construction: there the leaf
images degenerated onto axes, so a free direction peeled off. Here the lines
avoid every axis, obstructing all candidate splittings — independent of `m`.

## 4. The length-`(m+1)` tube `R_λ^{(m+1)}`

Tensor each `F¹ ↦ F^{m+1}`, `F² ↦ F^{2(m+1)}`, `F³ ↦ F^{3(m+1)}` (block
form, each block `F^{m+1}`), replace every scalar by the corresponding operator
(`1 ↦ id`), and **deform the modulus**: the single scalar `λ` (appearing only
in `β_C`) becomes `λ•id + J = jordanShiftLinGen F lam m`. Concretely, with the
existing primitives:

| arm map (canonical) | tube operator (`Fin _ → F` linear map)                                  |
|---------------------|--------------------------------------------------------------------------|
| `β_A` (`2→1`)       | `starEmbedDiag_F F m`  (`x ↦ (x,x)`)                                      |
| `α_A` (`1→0`)       | `(p,q) ↦ (0,p,q)`  (blocks 1,2)                                           |
| `β_B` (`4→3`)       | `starEmbedDiag_F F m`                                                     |
| `α_B` (`3→0`)       | `(p,q) ↦ (p,0,q)`  (blocks 0,2)                                           |
| `β_C` (`6→5`)       | `starEmbedTube_F F lam m`  (`x ↦ (x, (λ•id + J)x)`)                       |
| `α_C` (`5→0`)       | `prefixBlockEmbed_F F 2 3 m`  (`(p,q) ↦ (p,q,0)`, blocks 0,1)             |

The eigenvalue site is the leaf space of arm C (`F^{m+1}` at vertex 6); after
the collapse, `λ•id + J` governs the splitting there, and
`eigenvalue_jordan_invariant_compl_trivial_gen` (`FieldGenericTube.lean:77`)
finishes — exactly the §3 Kronecker template, now two-level.

### Dimension vector

Center `3(m+1)`, mids `2(m+1)`, leaves `m+1` — i.e. `etilde6Dim (m+1)`
verbatim, so `etilde6Rep_kQ_dimVec` keeps its statement.

### Reduction sketch for sub-B/sub-C

`α_A, α_B, α_C` have images = the three "coordinate-block planes"
`⟨blocks 1,2⟩`, `⟨blocks 0,2⟩`, `⟨blocks 0,1⟩` of the center; their pairwise
intersections are the single blocks. `β_A = β_B = diag`, `β_C = tube`. The
two-level collapse: complementary invariance pushes each leaf `W`-subspace up
through its mid to the center, the three planes force the three leaf subspaces
equal (the brick argument of §3, now at the `W`-pair level, via
`compl_le_forces_eq` / `forward_leaf_subspace_eq`), and arm C deposits a
`(λ•id + J)`-invariant pair at the common leaf space. Then propagate `⊥` back
down each arm (`center_decomp_F` + mid/leaf containment), as in
`starTubeRepGen_isIndecomposable`.

## 5. Orientation-genericity

Only the canonical (toward-center) maps are listed above. The full
`etilde6Rep_kQ` is orientation-generic: each of the six edges may reverse, and
the reverse maps are honest left inverses / sections (mirroring the existing
`prefixBlockProj_F`, `etilde6GammaInv_F`, `embed2to3_CA_reverse_F`,
`etilde6LeafProj_F` family). Reverse-direction leaf equalities are sub-B's job
(precedent: D̃₅ #2853, D̃₆ #4551). The construction itself is direction-aware
but the dimension vector is direction-independent.

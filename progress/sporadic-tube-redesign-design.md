# Design: corrected indecomposable family for the sporadic affine base cases

**Issue:** #4548 (replaces the refuted single-twist family for Ẽ₆ / Ẽ₇ / T(1,2,5)).
**Audit context:** #4542 (verdict: UNSOUND), and
`progress/indecomposability-framework-investigation.md` (explicit decompositions).
**Author:** work session `af582350`, 2026-06-14.

This document is the shared mathematical design for the redesign. It is
*not* a proof; it nails down the method, the framework constraint, the one
reduction template that the existing machinery already supports, and an
honest statement of what each implementing sub-issue must still derive.

## 1. What is broken, in one paragraph

`etilde6Rep_kQ`, `etilde7Rep_kQ` and the (not-yet-existent) `t125Rep_kQ`
are built from a **single nilpotent twist** `N` on one arm of an affine
Dynkin tree. The twist image only covers the `⟨e₀,…,e_{m-1}⟩` sub-block of
its target and misses the `e_m` direction; that one free direction peels off
a 1-dimensional summand at the center, so `*_kQ_isIndecomposable` is **false
for every `m ≥ 1`** (explicit complementary splittings in the investigation
doc, §1 Ẽ₇ and §2 T(1,2,5)). The reps are real objects with the right
dimension vector `(m+1)·δ`, but they are decomposable. The theorem
statements they feed (`*_not_finite_type_per_kQ`) are *true*; only the
indecomposability lemma is false.

## 2. Why neither existing shortcut applies

The project has exactly two proven indecomposability patterns, both via the
**invariant-submodule-splitting route** (there is no `End`-ring / local-ring
/ idempotent infrastructure anywhere — confirmed by survey):

- **Cycle pattern** (`cycleRepGen_isIndecomposable`, `FieldGenericCycle.lean`):
  every arrow is the identity except one nilpotent shift. The identity
  arrows + complementarity force `W₁(v)` equal at *every* vertex
  (`compl_le_forces_eq`), collapsing the whole rep to a single space with a
  nilpotent operator whose kernel is 1-dimensional; then
  `nilpotent_invariant_compl_trivial_gen` kills one side.
- **Iso-bridge pattern** (`d5tildeRep_isIndecomposable`,
  `InfiniteTypeConstructions.lean:1569`; `dTildeRep'_isIndecomposable:2431`):
  two centers of equal dimension joined by an **iso** `γ = [[I,I],[I,N]]`
  (`det = det(I−N) = ±1`, unipotent). The iso ties the two centers'
  decompositions together so all four leaves are forced equal, then the same
  workhorse finishes.

Ẽ₆ = T(2,2,2), Ẽ₇ = T(1,3,3) and T(1,2,5) are **simple trees with a single
trivalent vertex**. There is no graph cycle (so the cycle pattern's
"all-identity isos" is impossible — the dimension vector `δ` is non-constant,
so arms *must* be non-iso embeddings), and there is no second center to host
an iso bridge. The investigation doc reaches the same conclusion (§3): the
γ-iso is exactly what these shapes lack, and a single nilpotent twist cannot
replace it.

The mathematically forced answer (issue deliverable 1, preferred route) is
the **homogeneous-tube** indecomposable: introduce a genuine eigenvalue
parameter `λ` and build the length-`(m+1)` self-extension of a regular
simple. This is the canonical indecomposable at dimension `(m+1)·δ` for an
affine quiver.

## 3. The reduction template the machinery already supports (Kronecker)

The homogeneous tube reduces, via the *existing* workhorse, to a single
nilpotent-invariant splitting — provided the construction is shaped so the
identity arrows can collapse everything onto the eigenvalue site. The
Kronecker quiver `•⇉•` (vertices 0,1; two arrows `a,b : 0→1`) is the clean,
fully-worked template:

- `R_λ^{(n)}` : `V_0 = V_1 = F^n`, arrow `a = I_n`, arrow `b = λ·I_n + J_n`,
  where `J_n` is the nilpotent Jordan block (`J e_i = e_{i-1}`, `J e_0 = 0`).
- **Reduction:** let `(W₁,W₂)` be a complementary invariant pair. Arrow `a`
  is the identity, so `a(W_i(0)) = W_i(0) ⊆ W_i(1)`; by complementarity and
  dimensions `W_i(1) = W_i(0) =: U_i` (this is the `compl_le_forces_eq` move
  reused from the cycle proof). Invariance under `b` then gives
  `(λI + J_n)(U_i) ⊆ U_i`, i.e. `U_i` is `J_n`-invariant (same invariant
  subspaces as `J_n`, since `λI` is central). So `U₁,U₂` are complementary
  `J_n`-invariant subspaces of `F^n`; `J_n` is nilpotent with
  `dim ker = 1`, and `nilpotent_invariant_compl_trivial_gen` forces one to
  `⊥`. ∎

The two crucial facts this template proves portable:

1. `λI + J` and `J` have the **same invariant subspaces** — so the eigenvalue
   `λ` never needs to be tracked in the splitting argument; it only matters
   that the construction is built around `λI + J` rather than a rank-deficient
   `N`. (`λ` makes the *simple* simple; `J` drives the indecomposability of
   the *tube*.)
2. The reduction is exactly cycle-pattern collapse (identity arrows force
   equality) **followed by** the workhorse — both already in the codebase.

The obstruction for Ẽ₆/Ẽ₇/T(1,2,5): they are *not* Kronecker. `δ` is
non-constant, so the regular simple `R_λ` has genuinely different dimensions
at different vertices joined by **rectangular** maps, and the eigenvalue `λ`
is encoded in those rectangular maps rather than in a square `λI + J`.
Deriving those matrices is the real per-shape work (§5).

## 4. Framework decision: submodule route, not `End`-local

Issue deliverable 1 suggests proving indecomposability via "`End` is local
(`F[t]/(t^{m+1})`)". **Do not build `End`-local infrastructure for this** —
it is a large independent project and nothing else in the repo uses it. The
submodule route is the established technology and the Kronecker template
above shows the tube reduces to it cleanly. Concretely, every correct
construction here should be shaped so that:

> any complementary invariant pair `(W₁,W₂)` is forced (by the identity/iso
> arrows of the construction) down to a complementary `J`-invariant pair of a
> single `F^{m+1}` at the eigenvalue site, where
> `nilpotent_invariant_compl_trivial_gen` applies.

This is the D̃₅ proof shape (`core` / `gamma_containment` / `propagate`
helpers) re-targeted at a `J`-bearing center instead of an iso bridge.

## 5. Per-shape work that remains (honest open part)

For each shape the implementing sub-issue must:

1. **Derive the regular simple `R_λ`** at dimension `δ` (one parameter
   `λ ∈ F`, generic). `δ`:
   - Ẽ₆ = T(2,2,2): `δ = (3; 2,1; 2,1; 2,1)` (center 3, three arms `2,1`).
   - Ẽ₇ = T(1,3,3): center 4; arms of marks `(2)`, `(3,2,1)`, `(3,2,1)`
     — confirm against `etilde7Dim` before trusting.
   - T(1,2,5): null root quoted in `FieldGenericT125` comment as
     `δ = (6,3,4,2,5,4,3,2,1)`; confirm vertex order against the file.
   The regular simples of a 3-arm star are the homogeneous points of the
   tubular/canonical-algebra `P¹` family (`λ ≠ 0,1,∞`); explicit rectangular
   matrices exist but must be written and checked simple. This is the part
   **not** worked out in this doc.
2. **Tube `R_λ^{(m+1)}`:** tensor `R_λ` with `F^{m+1}` and inject `J_{m+1}`
   at the eigenvalue site so the construction is built around `λI + J`, with
   every other arrow an honest iso/identity that the collapse step can use.
   The dimension vector must come out `(m+1)·δ` (matching the *existing*
   `etilde6Dim` / `etilde7Dim` / `t125`-`Dim`, so the downstream
   `*_dimVec` and `*_not_finite_type_per_kQ` lemmas keep their statements).
3. **Indecomposability** via the §3/§4 reduction: collapse arrows → single
   `J`-invariant splitting → workhorse. Expect a D̃₅-sized proof
   (`core`-style containment lemmas + `propagate`); decompose sub-A/sub-B/
   sub-C exactly as the D̃₆/₇/₈ program does if it overflows a session.
4. **Re-point** `*_not_finite_type_per_kQ` at the new lemma (statements
   unchanged) and rebuild the four downstream consumers
   (`FieldGenericInfiniteType`, `FieldGenericTpqr`,
   `FieldGenericNonAdjacentBranches`, `FieldGenericAssembly`).

Acceptance (from the issue): the `m = 1` case must defeat the exact peeling
splitting of the investigation doc — i.e. there is no free `e_m` direction,
because the eigenvalue site is a *square* `λI + J` whose invariant subspaces
are all `J`-invariant (no rank-deficient leftover).

## 6. Recommended decomposition

- **Foundational (no graph dependency):** build/validate the reusable tube
  machinery on the smallest affine *tree* tube — D̃₄ (4-subspace,
  `δ = (2;1,1,1,1)`, dim 6) is the cleanest validation target — producing
  (i) a reusable "identity-arrow collapse" helper if not already factored out
  of the cycle proof, and (ii) a reusable statement of the §3 reduction
  ("center bearing `λI+J`, arms forcing collapse ⇒ indecomposable"). This
  de-risks the eigenvalue/`J` pattern before committing to the awkward
  rectangular matrices of the real shapes.
- **Per shape (depend on foundational):** Ẽ₆, then Ẽ₇, then T(1,2,5)
  (T(1,2,5) also constructs `t125Rep_kQ` from scratch). Each may further
  split sub-A/sub-B/sub-C.

Do **not** re-file "mirror etilde6" sub-sorries against the old refuted
shape — the old shape is decomposable and cannot carry the proof.

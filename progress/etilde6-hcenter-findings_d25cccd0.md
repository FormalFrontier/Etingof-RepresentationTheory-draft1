# Ẽ₆ `hcenter` center crux — findings and route correction (#4750)

Session `d25cccd0`. Issue #4750 asked to either **(A)** prove the standalone
`hcenter` obligation inside the all-canonical branch of
`etilde6Rep_kQ_leaf_equalities`, or **(B)** re-scope the Ẽ₆ indecomposability
route. This note records the mathematical analysis and concludes **(B)**, with a
precise redirect.

## Setup recap

Center `V₀ = c₀ ⊕ c₁ ⊕ c₂` (three blocks `F^{m+1}`). Three coordinate planes:
`π_A = ⟨c₁,c₂⟩ = range blockEmbed12`, `π_B = ⟨c₀,c₂⟩ = range blockEmbed02`,
`π_C = ⟨c₀,c₁⟩ = range (prefixBlockEmbed 2 3)`. Pairwise overlaps are single
blocks: `π_A ∩ π_B = c₂`, `π_B ∩ π_C = c₀`, `π_A ∩ π_C = c₁`.

The three leaf→center composites:
`compA u = (0,u,u)`, `compB u = (u,0,u)`, `compC u = (u, Ju, 0)` with
`J = λ•id + N` (the Jordan eigenvalue site of arm C).

`hcenter` claims, for an arbitrary complementary invariant pair `(W₁,W₂)`:
`compA u ∈ W₁⟨0⟩ ↔ compB u ∈ W₁⟨0⟩` and `compA u ∈ W₁⟨0⟩ ↔ compC u ∈ W₁⟨0⟩`.

## Finding 1 — `hcenter` is equivalent to the full leaf-equality goal

Via the already-landed arm criteria `hcritA/B/C` (in context at the `sorry`),
`u ∈ W₁⟨2⟩ ↔ compA u ∈ W₁⟨0⟩`, `u ∈ W₁⟨4⟩ ↔ compB u ∈ W₁⟨0⟩`,
`u ∈ W₁⟨6⟩ ↔ compC u ∈ W₁⟨0⟩`. So `hcenter` is logically **identical** to the
theorem's own conclusion `W₁⟨2⟩ = W₁⟨4⟩ = W₁⟨6⟩`. The "center-collapse" framing
adds no leverage: it is the goal in disguise.

## Finding 2 — plane-splits alone do NOT imply `hcenter` (explicit counterexample)

The naive route ("3-block analogue of `core`") would feed `hcenter` only the
three plane-splits `etilde6_armX_plane_split`
(`W₁⟨0⟩ ⊓ π = embed(W₁⟨mid⟩)`, complementary within each plane). That is
**insufficient**:

> Take `W₁⟨0⟩ = π_C = ⟨c₀,c₁⟩` and `W₂⟨0⟩ = c₂`. This is `IsCompl`, and it
> splits all three planes:
> `π_A: (W₁∩π_A, W₂∩π_A) = (c₁, c₂)`; `π_B: (c₀, c₂)`; `π_C: (π_C, 0)`.
> Yet `compC u = (u,Ju,0) ∈ π_C = W₁⟨0⟩` (always) while
> `compA u = (0,u,u) ∉ W₁⟨0⟩` for `u ≠ 0`. So `hcenter` **fails** for this
> plane-splitting pair.

(This `W₁⟨0⟩` does not extend to a genuine *invariant* pair — arm-A leaf
invariance of `W₂` fails — so it is not a counterexample to `hcenter` itself.
It *is* a proof that the plane-splits are not enough: any correct proof must
also consume the **leaf-level criteria** `hcritA/B/C`, i.e. the leaf
complementarity in both `W₁` and `W₂` directions.)

This is the formal version of the design-doc §3 observation that the brick
argument needs both "the plane splits" **and** "the leaf line lands wholly in
one side." `center3_sum_zero_F` only encodes the former.

## Finding 3 — arms A,B cannot be decoupled from arm C (eigenvalue site)

`compA u ∈ W₁⟨0⟩ ⟹ compB u ∈ W₁⟨0⟩` is equivalent (submodule arithmetic,
`compB = compA - (compA - compB)`) to `(compA u - compB u) = (-u,u,0) ∈ W₁⟨0⟩`.
But `(-u,u,0) ∈ π_C`, and its `W₁/W₂` membership is governed by the
**arm-C mid-5 data** `prefixBlockEmbed(W₁⟨5⟩)` — i.e. the Jordan eigenvalue
site. So the A↔B leaf coincidence **necessarily routes through arm C**. There is
no arm-A/arm-B-only derivation. This confirms the planner's route-(B) intuition:
the collapse and the eigenvalue-site argument must run in **one pass**.

## Finding 4 — λ-genericity caveat

`etilde6Rep_kQ_leaf_equalities` is stated for **all** `λ` and **all** `m`
(no `1 ≤ m`, no genericity). The design doc (`etilde6-tube-matrices.md` §2,
"Modulus") notes `λ ∈ {0,1,∞}` are exceptional rank-3 tube points where the
homogeneous construction degenerates. At those `λ` the rep may genuinely
decompose with **unequal** leaf subspaces, making the lemma *false as stated*.
The successor must either restrict `λ` (genericity hypothesis) or confirm the
Jordan-block site `λ•id + N` keeps the tube indecomposable at exceptional `λ`
for `m ≥ 1` (and handle `m = 0` separately — `m = 0` is exactly the §2 regular
simple `R_λ`).

## Recommended route (B): mirror the just-landed star `#4752`

`starRep_kQ_isIndecomposable` (merged in `#4752`,
`FieldGenericStar.lean:998–1245`) closes the analogous **D̃₄ star** center crux.
Its shape:

1. `starRep_kQ_leaf_equalities` (single-block embeds — provable standalone there
   via `compl_le_forces_eq`, because the D̃₄ arms hit *disjoint single blocks*,
   not overlapping planes) yields the leaf equalities **plus** the
   eigenvalue-coupled pair `hN₁` at the arm-1 leaf;
2. `eigenvalue_jordan_invariant_compl_trivial_gen` on `hN₁` ⟹
   `W₁⟨leaf⟩ = ⊥ ∨ W₂⟨leaf⟩ = ⊥`;
3. `center_collapse` lifts leaf-⊥ to `W⟨0⟩ = ⊥`;
4. `star_leaf_bot_of_center_bot` propagates `⊥` to every leaf.

The Ẽ₆ obstruction is **only at step 1**: the overlapping planes make the
standalone leaf-equality unprovable from the local pair data (Findings 2–3).
So the successor should **not** factor through a standalone arbitrary-pair
`hcenter`. Instead, fold steps 1–3 into one pass that directly produces
`W₁⟨0⟩ = ⊥ ∨ W₂⟨0⟩ = ⊥`:

- run `eigenvalue_jordan_invariant_compl_trivial_gen` at the arm-C leaf (via
  `etilde6_armC_criterion`/the arm-C mid pair) to get `W_i⟨6⟩ = ⊥`;
- build a **3-plane `center_collapse`** (the genuinely new infrastructure) that,
  from one arm's leaf/mid being `⊥`, drives `W_i⟨0⟩ = ⊥` using all three
  plane-splits + the two remaining arms' leaf criteria — the overlapping-plane
  analogue of the star's two-arm `center_collapse`;
- propagate `⊥` back down all three arms (forward injective embeds / reversed
  surjective projections, as `etilde6CompX_F_injective` + the reverse maps).

Then `etilde6Rep_kQ_leaf_equalities` is either narrowed to the
`⊥`-or-`⊤`-per-arm form actually consumed by sub-C `#4577`, or replaced
outright by the indecomposability pass.

## Status

- No proof of standalone `hcenter` exists or is expected (route A abandoned with
  the counterexample above as justification).
- `etilde6Rep_kQ_leaf_equalities` all-canonical branch retains its `sorry`; the
  in-file comment is updated to record the counterexample and point here.
- Successor issue created for the route-(B) eigenvalue-fold pass.

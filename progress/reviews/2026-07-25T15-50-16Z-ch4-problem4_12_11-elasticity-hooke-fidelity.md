# Stage 3.7 audit — Chapter 4, Problem 4.12.11 (elasticity / Hooke's law)

- **Issue:** #7302 (report-only statement-fidelity & non-vacuity audit)
- **Blob:** `blobs/Chapter4/Problem4.12.11.md`
- **Lean:** `EtingofRepresentationTheory/Chapter4/Problem4_12_11.lean` (1504 lines)
- **Build:** `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_11` exits 0
- **Sorries:** none (`grep -n sorry … | grep -v sorry-free` is empty)
- **Date:** 2026-07-25

## Verdict

**fidelity: `partial`** (downgraded from the previously recorded `verified`) —
**coverage: `covered_partial`**.

Every headline theorem that exists is faithfully stated, non-vacuous and axiom-clean.
Two of the book's named claims are *not* delivered by any theorem in the file, and in
both cases the missing content is currently asserted only in a docstring:

- **Gap A (pre-existing, re-confirmed):** `hooke_law` takes `f : End(V) →ₗ[ℝ] End(V)`,
  while the book supplies `f : S²V → End(V)`. See below.
- **Gap B (new, found by this audit):** the 3-dimensional summand is never identified
  with *the standard representation* `V = ℝ³`. See below.

The previously recorded `fidelity: verified` is not supportable alongside Gap B, and the
old note pointed `followup_issue` at #7302 itself (an audit issue, not a fix issue).
Both are corrected in `progress/items.json`.

## Axiom check

`#print axioms` appended to the source file and run with
`lake env lean EtingofRepresentationTheory/Chapter4/Problem4_12_11.lean` (file restored
afterwards). All twelve report

```
[propext, Classical.choice, Quot.sound]
```

with **no `sorryAx`**, and the run produced **no `error:`** (so no false-`sorryAx`
elaboration artifact of the kind recorded for `Chapter3/Problem3_9_2.lean`):

`conjRep`, `endV_isInternal`, `symSub_eq_scalar_sup_tracelessSym`, `scalarSub_finrank`,
`skewSub_finrank`, `tracelessSymSub_finrank`, `conjRep_invariant`, `skewSub_irreducible`,
`tracelessSymSub_irreducible`, `skewSub_irreducible_complexified`,
`tracelessSymSub_irreducible_complexified`, `hooke_law`.

## Hypothesis faithfulness

- **`SO3` is the genuine special orthogonal group.** `SO3 := specialOrthogonalGroup (Fin 3) ℝ`
  (Mathlib), i.e. orthogonal **and** `det = 1`. The determinant condition is not decorative:
  for `O(3)` the skew summand is `V ⊗ det`, not `V`, so restricting to `SO(3)` is what makes
  the book's identification of the 3-dimensional summand available at all.
- **`conjRep` is a real `Representation`, not a placeholder.** `conjRep : Representation ℝ SO3 EndV`
  with `conjRep A M = A * M * star A`, `map_one'`/`map_mul'` both discharged; `star A = Aᵀ = A⁻¹`
  on `SO3` (`star_coe_eq_transpose`, `coe_mul_star`, `star_mul_coe`), so this is honest
  conjugation, and it is axiom-clean as a definition.
- **The three submodules are the intended `ℝ`/`V`/`W`.** `scalarSub = span ℝ {1}`,
  `skewSub = {M | Mᵀ = -M}`, `tracelessSymSub = {M | Mᵀ = M ∧ trace M = 0}`, all built as genuine
  `Submodule` data (no sorry'd fields), and all `conjRep`-invariant by `conjRep_invariant`.
  `symSub = {M | Mᵀ = M}` is the book's `S²V`; the book itself makes that identification
  ("a small symmetric matrix, i.e. an element of `S²V`"), so reading `S²V` as symmetric
  matrices is faithful and **not** a gap.
- **`scalarSub` really carries the trivial action.** Immediate from the axiom-checked
  `conjRep_one : conjRep A 1 = 1` plus `map_smul`. Not stated as a standalone lemma — a
  presentational nit, not a gap.
- **The intertwiner hypothesis encodes Galileo invariance.** `hf : ∀ A : SO3, f.comp (conjRep A) = (conjRep A).comp f`
  is exactly "`f` is a homomorphism of `SO(3)`-representations". It is a real equation between
  linear maps, not a `True`-typed or trivially-dischargeable stub.

## Conclusion faithfulness

### Part (a) — the decomposition

- `endV_isInternal : DirectSum.IsInternal ![scalarSub, skewSub, tracelessSymSub]` is a genuine
  internal direct sum (independence + `iSup = ⊤`, both proved), and with
  `scalarSub_finrank = 1`, `skewSub_finrank = 3`, `tracelessSymSub_finrank = 5` plus
  `conjRep_invariant` this delivers `End(V) = ℝ ⊕ (3-dim) ⊕ (5-dim)` **as representations**.
- `symSub_eq_scalar_sup_tracelessSym : scalarSub ⊔ tracelessSymSub = symSub ∧ scalarSub ⊓ tracelessSymSub = ⊥`
  faithfully delivers `S²V = ℝ ⊕ W` (sup + trivial intersection is a direct-sum decomposition
  of `symSub`). **Faithful.**

**Gap B.** The book asks for `ℝ ⊕ V ⊕ W` where "`V` is the standard 3-dimensional
representation". The Lean proves only that the middle summand is a 3-dimensional invariant
subspace. There is no `Representation ℝ SO3 (Fin 3 → ℝ)` anywhere in the file, and no
equivariant `skewSub ≃ₗ[ℝ] (Fin 3 → ℝ)`. A repo-wide grep for `specialOrthogonalGroup`
confirms the standard `SO(3)`-action on `ℝ³` is not formalized elsewhere in the project
either (`Problem4_12_7.lean`, `Problem4_12_8.lean` use `SO(3)` but build no such
representation). Meanwhile the file's module docstring and the docstrings on `skewSub` and
`skewSub_irreducible` all assert "isomorphic to the standard representation `V`" — a reader
trusting the docstrings would believe more is proved than is. The statement is true (the hat
map `v ↦ [[0,-v₂,v₁],[v₂,0,-v₀],[-v₁,v₀,0]]` satisfies `hat (A v) = A · hat v · Aᵀ` for
`det A = 1`) and cheap to formalize, but it is currently unproved.

Follow-up: **#7796**.

### Part (b) — irreducibility

All four theorems have the correct shape — an invariant submodule of the ambient one is `⊥`
or everything:

```lean
skewSub_irreducible (U : Submodule ℝ EndV) (hUle : U ≤ skewSub)
    (hUinv : ∀ A : SO3, ∀ M ∈ U, conjRep A M ∈ U) : U = ⊥ ∨ U = skewSub
```

and likewise `tracelessSymSub_irreducible`, plus the two complexified versions over
`EndVc = Matrix (Fin 3) (Fin 3) ℂ` with `conjRepc` and `skewSubc`/`tracelessSymSubc`.
**Faithful, and phrased over the correct object.** The complexification is genuine, not a
relabelling: `skew_decompc` / `traceless_sym_decompc` prove every *complex* skew (resp.
traceless-symmetric) matrix is a `ℂ`-combination of `cx` of the *real* basis matrices, so
`skewSubc` really is `skewSub ⊗_ℝ ℂ`, and `cx_conjRep` proves `cx` intertwines `conjRep`
with `conjRepc`. This covers the book's "even after complexification".

### Part (b) — Hooke's law

```lean
hooke_law (f : EndV →ₗ[ℝ] EndV) (hf : ∀ A : SO3, f.comp (conjRep A) = (conjRep A).comp f) :
    ∃ K μ : ℝ, (∀ x ∈ scalarSub, f x = K • x) ∧ (∀ y ∈ tracelessSymSub, f y = μ • y) ∧
      (∀ x ∈ symSub, f x ∈ symSub)
```

- The book's **`f(x + y) = Kx + μy`** is reachable in one line. Verified by elaborating,
  against the real file, the witness

  ```lean
  example (f : EndV →ₗ[ℝ] EndV) (hf : ∀ A : SO3, f.comp (conjRep A) = (conjRep A).comp f) :
      ∃ K μ : ℝ, ∀ x ∈ scalarSub, ∀ y ∈ tracelessSymSub, f (x + y) = K • x + μ • y := by
    obtain ⟨K, μ, hK, hμ, _⟩ := hooke_law f hf
    exact ⟨K, μ, fun x hx y hy => by rw [map_add, hK x hx, hμ y hy]⟩
  ```

  which compiles clean. Not stating the combined form as a headline is a presentational nit,
  **not** a gap.
- The book's **"`S_P` is always symmetric"** is the third conjunct: `d_P ∈ S²V = symSub` and
  `S_P = f(d_P) ∈ symSub`. **Faithful.**

**Gap A (re-confirmed).** The book's `f` has domain `S²V`; the Lean `f` has domain `End(V)`.
This is a *strengthened hypothesis*, so `hooke_law` does not apply to the book's data: given
an equivariant `f : symSub →ₗ[ℝ] EndV` you cannot instantiate `hooke_law` without first
extending `f` to `End(V)`. The extension does exist and is equivariant — `End(V) = symSub ⊕ skewSub`
as representations, so extend by `0` on `skewSub` — but that step is not formalized, so the
book's exact-domain statement is not currently a consequence of anything in the file.
This matches the note already on record from the prior pass; the only correction is that the
note pointed `followup_issue` at #7302, which is this audit, not a fix.

Follow-up: **#7795**.

## Non-vacuity

Each of the following was appended to the real source file and elaborated with
`lake env lean` (whole run reported no `error:`); the file was restored afterwards.

- **`SO3` is nontrivial:** `example : (Dz : EndV) ≠ 1` compiles. `Dz`, `Dy`, `Dx`, `Pc`,
  `Rz45`, `Ry45` are all constructed with real membership proofs, so the group has genuine
  content beyond the identity.
- **The `hooke_law` hypothesis is satisfiable by non-trivial equivariant maps:**

  ```lean
  example : ∀ A : SO3, scalarProj.comp (conjRep A) = (conjRep A).comp scalarProj :=
    fun A => LinearMap.ext fun M => scalarProj_equivariant A M
  ```

  and the same for `skewProj`. Both compile. `scalarProj M = (trace M / 3) • 1` and
  `skewProj M = (1/2) • (M - Mᵀ)` are honest non-zero, non-identity maps.
- **`hooke_law` instantiates and yields real moduli:** applying it to `scalarProj` compiles,
  so the conclusion is inhabited rather than vacuously quantified.
- **The irreducibility theorems have nonzero ambients:** `example : skewSub ≠ ⊥` and
  `example : tracelessSymSub ≠ ⊥` compile (via the `finrank = 3` / `= 5` lemmas).
- **No `True`-typed or trivially-dischargeable hypothesis** appears in any headline statement;
  every hypothesis is either a submodule membership/containment or a genuine equation of
  linear maps.

## Coverage summary

| Book claim | Status |
|---|---|
| (a) `End(V) = ℝ ⊕ (3-dim) ⊕ (5-dim)`, invariant, dims `1,3,5` | covered_full |
| (a) the 3-dim summand **is the standard rep `V`** | **not covered** → #7796 |
| (a) `S²V = ℝ ⊕ W` | covered_full |
| (b) `V`, `W` irreducible over `ℝ` | covered_full |
| (b) `V`, `W` irreducible after complexification | covered_full |
| (b) `f(x + y) = Kx + μy` | covered_full (one-line corollary of `hooke_law`) |
| (b) `S_P` symmetric | covered_full (third conjunct) |
| (b) the hypothesis is the book's `f : S²V → End(V)` | **not covered** → #7795 |

## No Lean edits

Per the report-only scope of #7302, no statement in
`EtingofRepresentationTheory/Chapter4/Problem4_12_11.lean` was changed; the file is
byte-identical to `main`. Both gaps are split out as feature issues.

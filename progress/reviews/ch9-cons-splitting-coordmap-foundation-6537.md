# Review #6537 — Ch9 cons-splitting coordinate-map foundation: **PASS**

Audit of the two sorry-free foundational files that the pending bundled iso
`A_n ⊗_S V ≅ A_{n+1}` (#6535) and the combinatorial core (#6533) rest on:

- `EtingofRepresentationTheory/Chapter9/PathAlgebraLengthGrading.lean` (PR #6517)
- `EtingofRepresentationTheory/Chapter9/PathAlgebraInducedGrading.lean` (PR #6527)

**Verdict: clean PASS.** No defect found. Every `def`/`abbrev` constructs genuine
data; every lemma statement faithfully encodes the cons-splitting decomposition;
the `S`-linearity claims are correct for the right action `s • a = a * f s`.

## Verification performed

- `lake exe cache get` then `lake build …PathAlgebraLengthGrading …PathAlgebraInducedGrading`
  succeeds on the current tree (1822 jobs, both files rebuilt clean).
- `grep -n sorry` on both files returns nothing — the sorry-free claim holds.

## Deliverable 1 — definitions construct genuine data

All checked; none is a `sorry`ed body, a `True`-placeholder, or an accidentally-trivial map:

- `pathLen p = p.2.2.length` — the real arrow count.
- `lengthGrading = Finsupp.lsum k (p ↦ id.smulRight (single (pathLen p) (ofPath p)))`.
  `lengthGrading_single` confirms `single p c ↦ single (pathLen p) (single p c)` — the genuine
  homogeneous decomposition, recovered by `lengthTotalize` (so demonstrably non-collapsing).
- `lengthTotalize = Finsupp.lsum k (_ ↦ id)` — sum of graded components; `lengthTotalize_lengthGrading`
  proves it is a left inverse (hence `lengthGrading_injective`).
- `lengthProj n = (lapply n).comp lengthGrading` — genuine `n`-th coordinate; `lengthProj_single`,
  `lengthProj_single_self`, `lengthProj_lengthProj` (idempotence) all hold.
- `lengthGradingS` / `lengthTotalizeS` — the `Q → k`-linear upgrades. Their `map_add'` = `map_add _`
  and `map_smul'` fields are proven substantively (via `vertex_smul_def` +
  `lengthGrading_mul_vertexEmbedding`, and by `Finsupp.induction_linear` respectively), **not**
  discharged vacuously. `lengthTotalizeS_comp_lengthGradingS` is the `S`-linear left inverse.
- `inducedCarrier M = TensorProduct (Q → k) (PathAlgebra k Q) (restrictObj M)` — the real `A ⊗_S M`.
- `inducedCoordMap = finsuppLeft ∘ TensorProduct.map lengthGradingS id`. `inducedCoordMap_tmul`
  confirms `a ⊗ m ↦ (n ↦ lengthProj n a ⊗ m)` — non-trivial (top degree returns the path unchanged).

## Deliverable 2 — statements faithfully encode cons-splitting

- `pathLen_mk`, `pathLen_comp` (`len (p·q) = len p + len q`), `pathLen_comp_arrow`
  (`len (p · e.toPath) = len p + 1`) count arrows correctly.
- `ofPath_mul_arrowElt`: `ofPath ⟨a,b,p⟩ * arrowElt ⟨b,c,e⟩ = ofPath ⟨a,c, p.comp e.toPath⟩` — the
  correct seed: a length-`n` basis path times one arrow `e : b ⟶ c` is the length-`(n+1)` basis path
  with source `a`, target `c`. Endpoints correct. **Independently corroborated** by
  `Chapter2/Problem2_8_6.lean:44` (`ofPath ⟨a,c, q.cons e⟩ = ofPath ⟨a,b,q⟩ * arrowGen k Q e`).
- `lengthProj_ofPath_mul_arrowElt`: projecting `p·e` onto degree `len p + 1` returns it unchanged.
- Injectivity claims are stated over the intended full domains and are not weaker than advertised:
  `lengthGrading_injective` over all of `A = QuiverPathIndex Q →₀ k`;
  `inducedCoordMap_injective` over all of `inducedCarrier M = A ⊗_S M`.

## Deliverable 3 — `S`-linearity for the right action `s • a = a * f s`

- Action convention confirmed at source: `PathAlgebraInduction.vertex_smul_def` gives
  `s • a = a * vertexEmbedding k Q s`, and `inducedCarrier` tensors over exactly this
  `instModuleVertex`. `restrictObj M = (restrictScalars (vertexEmbedding k Q)).obj M`.
- `ofPath_mul_vertexEmbedding`: `p · f s = s(tgt p) • p` (`x.2.1` is the target vertex).
  Consistent with the target-action convention `arrowElt_mul_vertexEmbedding`
  (`arrowElt x * f s = s x.tgt • arrowElt x`) in `PathAlgebraArrowBimodule.lean` — the coordinate
  map matches what the bundled iso will consume.
- `lengthProj_mul_vertexEmbedding` (degree-`n` component of `a · f s` is `(deg-n of a) · f s`) and
  `lengthGrading_mul_vertexEmbedding` (`lengthGrading (a · f s) = s • lengthGrading a`, pointwise
  right mult on `ℕ →₀ A`) are the substance behind `lengthGradingS`'s `map_smul'`. Correct: right
  multiplication by `f s` scales each basis path by its target coordinate and so preserves length
  degree. `inducedCoordMap` is `S`-linear as declared (it is a composite of `S`-linear maps).

## Notes for downstream (#6535, #6533)

The foundation is sound to build the bundled `≃ₗ` on top of. No follow-up issue is required.
The `S`-scaling in this file is by the **target** coordinate (right action); the source-scaling
analogue the bundled iso will also need is `vertexEmbedding_mul_arrowElt` /
`arrowInclusion_wSMul_src` in `PathAlgebraArrowBimodule.lean` / `PathAlgebraStandardComplex.lean`,
already present.

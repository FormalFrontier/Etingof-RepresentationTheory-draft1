# Stage 3.7 audit: Chapter4/Problem4.12.5 (icosahedral A₅ decompositions)

Issue: #7276. Session `2caa5111-b747-407a-812c-b5d99cf63ab7`, branch `agent/2caa5111`.

**Verdict: PASS**, after closing the non-vacuity gap the 2026-07-22 reopen identified.

## Scope

The issue was originally filed as a report-only statement-fidelity and non-vacuity audit of
`EtingofRepresentationTheory/Chapter4/Problem4_12_5.lean`. It was reopened on 2026-07-22 with
expanded acceptance criteria:

> construct concrete A5 actions for vertices, faces, and edges (or precise coset models), prove
> the required transitivity/stabilizer facts and equivariant identifications with the
> regular-icosahedron representations, then expose unconditional decomposition corollaries on
> those source models.

Per `agent-worker-flow` Step 1, the reopening comment is authoritative over the issue body, so
this session treated the work as construction rather than reporting. The audit findings are
recorded below; the construction is in
`EtingofRepresentationTheory/Chapter4/Problem4_12_5_CosetModels.lean`.

## Book statement (`blobs/Chapter4/Problem4.12.5.md`)

`I` = vertices of a regular icosahedron, `|I| = 12`; `G = A₅` acts on the icosahedron, giving a
12-dimensional representation on `F(I)`.

* (a) Decompose it into irreducibles (find the multiplicities of all irreducibles).
* (b) Same for functions on the set of faces and the set of edges.

## 1. Statement fidelity

The three theorems `vertices_decomposition`, `faces_decomposition`, `edges_decomposition` each
assert the existence of a family `S : Fin k → Submodule ℂ (Fin N → ℂ)` of `A₅`-invariant
subspaces with

* `DirectSum.IsInternal S` — Mathlib's genuine internal direct sum (the canonical map from the
  direct sum is bijective), not a dimension count or a spanning claim;
* `∀ k, IsIrredSub (permRep act) (S k)` — `S k ≠ ⊥` and no `A₅`-invariant submodule strictly
  between `⊥` and `S k`, i.e. genuine irreducibility of the subrepresentation, not merely of the
  underlying `ℂ`-module;
* explicit `Module.finrank` values for each summand;
* a witness `g : A₅` at which the two 3-dimensional summands' subrepresentation characters
  differ, so those summands are non-isomorphic.

The dimension multisets are `(1,3,3,5)` summing to 12, `(1,3,3,4,4,5)` summing to 20, and
`(1,3,3,4,4,5,5,5)` summing to 30. Against the known character table of `A₅` (irreducible
dimensions `1, 3, 3', 4, 5`) these are the correct multiplicities: `1+3+3'+5`, `1+3+3'+4²+5`,
`1+3+3'+4²+5³`. Listing dimensions plus the `3`/`3'` separation pins the isomorphism type
uniquely, since `3` and `3'` are the only pair of distinct irreducibles of equal dimension. This
is a faithful rendering of "find the multiplicities of occurrence of all irreducible
representations" for parts (a) and (b).

Supporting definitions check out: `permRep act g f = f ∘ act g⁻¹` is the permutation
representation on functions (a left action, with the inverse in the right place);
`subChar ρ S hS g` is the trace of `ρ g` restricted to `S`; `fixCount_vertices/faces/edges` derive
the permutation characters `(12,0,0,2,2)`, `(20,0,2,0,0)`, `(30,2,0,0,0)` on the class
representatives from transitivity and the stabilizer order alone, via the orbit-stabilizer
identity `fix_mul_stab_card` and `decide`-checked twisted counts over `A₅`.

## 2. Non-vacuity — the gap, and its closure

**The gap.** The three theorems quantified over an arbitrary `act : A₅ →* Equiv.Perm (Fin N)`
with transitivity and stabilizer-order hypotheses. Nothing in the repository exhibited such an
`act`. Formally the theorems were not vacuous in the logical sense (the hypotheses are
satisfiable), but nothing *in the formalization* witnessed that, and nothing connected `Fin 12`,
`Fin 20`, `Fin 30` to the icosahedron. The file's own module docstring conceded this, asserting
uniqueness up to isomorphism in prose and then taking the action as a hypothesis. That is exactly
what the reopen objected to.

**The closure.** `Problem4_12_5_CosetModels.lean` supplies:

1. **Constructed actions.** The vertex, face and edge stabilizers of the icosahedron are cyclic of
   orders 5, 3, 2, so the three actions are left translation on `A₅ ⧸ H` for `H` cyclic of those
   orders. `vertexStab`, `faceStab`, `edgeStab` are `⟨classRepA5 3⟩`, `⟨classRepA5 1⟩`,
   `⟨classRepA5 2⟩` (orders 5, 3, 2 by the existing `ord_cr3`, `ord_cr1`, `ord_cr2`).
   `card_quotient_vertexStab/faceStab/edgeStab` give `60/5 = 12`, `60/3 = 20`, `60/2 = 30`, and
   `cosetAct` transports the translation action along a labelling by `Fin N`, yielding
   `verticesAct`, `facesAct`, `edgesAct`. These are real `def`s with no sorry in their bodies.
2. **The hypotheses, discharged.** `verticesAct_transitive` etc. come from pretransitivity of the
   coset action. The stabilizer orders are *not* assumed: `card_mul_card_stab` (the `g = 1` case
   of the existing `fix_mul_stab_card`) shows `N * |stabilizer| = |A₅| = 60` for any transitive
   action, so `verticesAct_stab`, `facesAct_stab`, `edgesAct_stab` follow by arithmetic.
3. **Equivariant identification.** `quotStabEquivFin` shows the orbit map descends to an
   equivariant bijection `A₅ ⧸ stabSub act i₀ ≃ Fin N` for any transitive `act`, so every
   transitive action *is* a coset action. `quotientEquivOfConjSubgroup` gives an equivariant
   bijection `A₅ ⧸ H₁ ≃ A₅ ⧸ H₂` when `H₂ = c H₁ c⁻¹`. Combining these with the conjugacy results
   already in `Problem4_12_5.lean` (`exists_conj_stab_sylow` for orders 5 and 3, where the
   stabilizer is a full Sylow subgroup of `A₅`; `exists_conj_stab_invol` for order 2) yields
   `verticesAct_unique`, `facesAct_unique`, `edgesAct_unique`: any transitive `A₅`-action of the
   right degree and stabilizer order is equivariantly isomorphic to the constructed model. So
   whichever concrete realization of the regular icosahedron one starts from, its vertex/face/edge
   action is the model built here, up to equivariant isomorphism.
4. **Unconditional corollaries.** `vertices_decomposition_icosahedral`,
   `faces_decomposition_icosahedral`, `edges_decomposition_icosahedral` are the three
   decompositions with no hypotheses.

The remaining unformalized step is the identification of the abstract rotation group of the
regular icosahedron with `A₅` together with its vertex/face/edge stabilizers — Euclidean geometry
the book itself only asserts ("Recall that the group `G = A₅` ... acts on the icosahedron"). The
reopen explicitly allowed "precise coset models" in place of that, and the uniqueness theorems
mean nothing about the representation-theoretic content depends on which model is used.

## 3. `#print axioms`

Via a scratch file importing the built module (`lake env lean`, after
`lake build EtingofRepresentationTheory.Chapter4.Problem4_12_5_CosetModels` succeeded), all of

`vertices_decomposition`, `faces_decomposition`, `edges_decomposition`,
`vertices_decomposition_icosahedral`, `faces_decomposition_icosahedral`,
`edges_decomposition_icosahedral`, `verticesAct_unique`, `facesAct_unique`, `edgesAct_unique`,
`verticesAct_transitive`, `verticesAct_stab`, `facesAct_stab`, `edgesAct_stab`,
`exists_equivariant_equiv_cosetAct`

report `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

`Problem4_12_5.lean` contains no `sorry` (the only occurrence of the token is inside a docstring);
`Problem4_12_5_CosetModels.lean` contains none at all. The `coverage_issue: 7537` recorded on the
`items.json` entry (an unsolved goal in `Problem4_12_5.lean`) is stale — that issue is closed and
the file builds clean; the field has been removed.

## 4. `progress/items.json`

`Chapter4/Problem4.12.5` updated: `status` `partially_proved` → `sorry_free`, `coverage`
`covered_partial` → `covered_full`, `fidelity` `partial` → `verified`, `fidelity_decl` repointed to
the six unconditional endpoints, `lean_file` extended with the new file, `coverage_note` and
`fidelity_note` rewritten, `followup_issue` (#7276) and stale `coverage_issue` (#7537) removed,
`last_updated` 2026-07-26.

## Verification

* `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_5_CosetModels` — exit 0, no
  warnings from the new file.
* `python3 scripts/validate_items.py` — `VALIDATION PASSED`.

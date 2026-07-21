# Statement-fidelity & non-vacuity audit — Theorem 5.18.1 (Double Centralizer Theorem)

**Issue:** #7173
**Date:** 2026-07-21 (UTC)
**Reviewer:** review agent (session 038324b8)
**Scope:** report-only fidelity + non-vacuity audit of the five headline declarations in
`EtingofRepresentationTheory/Chapter5/Theorem5_18_1.lean` (parts (i), (ii), (iii) and the
two bimodule forms), plus the supporting `noncomputable def`s.
**Verdict: FAITHFUL — axiom-clean, no defect requiring a fix. Nothing filed.**

## Sources compared

- **Book statement** (`blobs/Chapter5/Theorem5.18.1.md`):
  > **Theorem 5.18.1.** Let `A`, `B` be two subalgebras of `End E` of a finite dimensional
  > vector space `E`, such that `A` is semisimple and `B = End_A E`. Then:
  > (i) `A = End_B E` (the centralizer of the centralizer of `A` is `A`).
  > (ii) `B` is semisimple.
  > (iii) As a representation of `A ⊗ B`, `E = ⊕_{i∈I} V_i ⊗ W_i`, where the `V_i` are all
  > the irreducible representations of `A` and `W_i` all the irreducible representations of
  > `B`. In particular there is a natural bijection between irreducible reps of `A` and `B`.
- **Book proof.** Since `A` is semisimple, `E = ⊕_i V_i ⊗ W_i` with `W_i := Hom_A(V_i, E)`
  and `A = ⊕_i End V_i`. `W_i ≠ 0` because `A` acts faithfully. By Schur's lemma
  `B = End_A E ≅ ⊕_i End(W_i)`. This gives all statements.
- **Lean file:** `EtingofRepresentationTheory/Chapter5/Theorem5_18_1.lean` (1051 lines,
  `grep -cE '\bsorry\b|\badmit\b'` = 0).

Throughout, the Lean model realizes the book's `B = End_A E` as
`B = Subalgebra.centralizer k A` inside `Module.End k E`. This is the correct translation:
for `A ⊆ End_k E`, the `A`-linear endomorphisms of `E` are exactly the elements of
`End_k E` that commute with every element of `A`, i.e. the centralizer of `A`. The ring
isomorphism `centralizer(A) ≅ Module.End A E` is built and used explicitly in part (ii)
(`toEnd`/`fromEnd`, `:317`–`:341`), confirming the two descriptions coincide.

## Fidelity checks, per headline declaration

### (i) `Theorem5_18_1_double_centralizer` (`:226`) — FAITHFUL

```lean
theorem Theorem5_18_1_double_centralizer
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E] :
    Subalgebra.centralizer k
      (Subalgebra.centralizer k (A : Set (Module.End k E)) : Set (Module.End k E)) = A
```

- LHS is genuinely `centralizer(centralizer(A))` and RHS is `A` (Subalgebra equality),
  which is exactly book part (i) `A = End_B E` under `B = End_A E = centralizer(A)`. ✓
- Hypotheses are load-bearing and match the book: `A` semisimple (`[IsSemisimpleRing A]`),
  `E` finite over `k` (`[Module.Finite k E]`, from the section `variable`). The hard
  inclusion `centralizer(centralizer(A)) ≤ A` is proved by genuine Jacobson density
  (`jacobson_density f' s` on a finite spanning set), not assumed; the easy inclusion is
  `Subalgebra.le_centralizer_centralizer`. No `True`/vacuous placeholder. ✓
- `[FaithfulSMul A E]` note: for a subalgebra `A ⊆ End_k E` the action on `E` is *always*
  faithful (an endomorphism acting as `0` on all of `E` is `0`), so this instance is
  automatically satisfiable and does not weaken the statement or exclude any book case. It
  is a redundant-but-harmless hypothesis needed to drive Mathlib's `A`-module machinery.
  Not a defect.

### (ii) `Theorem5_18_1_commutant_semisimple` (`:301`) — FAITHFUL

```lean
theorem Theorem5_18_1_commutant_semisimple
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E] :
    IsSemisimpleRing (Subalgebra.centralizer k (A : Set (Module.End k E)))
```

- Directly asserts book part (ii): `B = centralizer(A)` is a semisimple ring. ✓
- Proof is honest: `E` is a semisimple, finite `A`-module, so `Module.End A E` is
  semisimple by Wedderburn–Artin (`IsSemisimpleRing.moduleEnd A E`); the explicit ring
  iso `centralizer(A) ≃+* Module.End A E` (`e`, `:340`) transports semisimplicity back.
  No hidden assumption; `[IsAlgClosed k]` is (correctly) **not** required here. ✓

### (iii) `Theorem5_18_1_decomposition` (`:359`) — TRUE but WEAK (see note)

```lean
theorem Theorem5_18_1_decomposition ... :
    ∃ (ι) (Fintype ι) (DecidableEq ι) (V : ι → Type v) (W : ι → Type u) ...
      (∀ i, IsSimpleModule A (V i)) ...,
      Nonempty (E ≃ₗ[k] DirectSum ι (fun i => V i ⊗[k] W i))
```

This is a *true, non-vacuous, but strictly weaker* rendering of part (iii). It is proved
by `V i =` the `i`-th simple `A`-submodule from the semisimple decomposition of `E` and
`W i = k`, so the tensor factorization degenerates to `E ≅ ⊕_i S_i ⊗ k ≅ ⊕_i S_i` — just
the semisimple decomposition of `E` as an `A`-module. Relative to the book it drops the
two pieces of double-centralizer content:

- the `V_i` are **not** required pairwise non-isomorphic (they repeat with multiplicity);
- the `W_i` carry **no** `B`-module structure (they are `k`, not the irreducible
  `B`-modules `Hom_A(V_i, E)`), so `B` does not appear in the statement at all.

This is **not** a defect masquerading as content: the equivalence is genuine (real
`e.restrictScalars` + `TensorProduct.rid`), it is honestly documented in the file as the
weak precursor, and the full book claim is captured faithfully by the two bimodule forms
below. I therefore record it as a deliberate weak lemma, not a statement error. No fix
filed (the strong faithful statement already exists in the same file — see next).

### (iii, strong) `Theorem5_18_1_bimodule_decomposition` (`:704`) — FAITHFUL

```lean
theorem Theorem5_18_1_bimodule_decomposition [IsAlgClosed k]
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E] :
    ∃ (ι) ... (V : ι → Type v) ... (∀ i, IsSimpleModule A (V i))
      (∀ i j, Nonempty (V i ≃ₗ[A] V j) → i = j)          -- distinctness
      ... (L : ι → Type v) ...
      (∀ i, Module (centralizer k A) (L i))               -- L_i is a B-module
      (∀ i, SMulCommClass (centralizer k A) k (L i)) (∀ i, Module.Finite k (L i)),
      Nonempty (E ≃ₗ[k] DirectSum ι (fun i => V i ⊗[k] L i))
```

Faithful to the book's part (iii):

- **Distinct irreducibles.** `∀ i j, Nonempty (V i ≃ₗ[A] V j) → i = j` (`:713`) genuinely
  encodes "the `V_i` are pairwise non-isomorphic," matching "`V_i` are *all the*
  irreducible reps" (indexed once each). The proof derives it from equality of isotypic
  components (`isotypicComponent_eq`), so it is real, not a vacuous `→`. ✓
- **`W_i = Hom_A(V_i, E)` as a `B`-module.** `L i = V i →ₗ[A] E` carries a genuine
  `Module (centralizer k A)` structure (`centralizerModuleHom`, post-composition) with
  `SMulCommClass B k` — this is exactly the book's `W_i` with its `B`-action, not a bare
  `k`-space. ✓
- **The decomposition.** `E ≃ₗ[k] ⊕_i V_i ⊗[k] L_i` is built via the isotypic
  decomposition (`isotypicDirectSumEquiv`), per-component Schur evaluation
  (`schurEvaluationEquiv`) and the isotypic bridge (`homIsotypicBridge`). The index set is
  `isotypicComponents A E`, i.e. one factor per *distinct* isotype in `E`. ✓
- `[IsAlgClosed k]` is present and genuinely needed (Schur's lemma `End_A(V) ≅ k`), matching
  the book's standing algebraically-closed base field for the tensor factorization. ✓

### (iii, explicit) `Theorem5_18_1_bimodule_decomposition_explicit` (`:854`) — FAITHFUL (strongest)

Strengthens the previous by concretizing `V : ι → Submodule A E`, `L_i = V_i →ₗ[A] E`, and
adds the two decisive clauses:

- **`W_i` are irreducible `B`-modules.**
  `∀ i, IsSimpleModule (centralizer k A) (V i →ₗ[A] E)` (`:863`) — the multiplicity spaces
  are *simple* over `B`, proved by `isSimpleModule_homA_centralizer` (`B`-side Schur via
  `IsSemisimpleModule.extension_property`). Together with `V_i` simple + distinct and the
  index `i ↦ (V_i, L_i)`, this realizes the book's "natural bijection between irreducible
  reps of `A` and `B`." ✓
- **The iso is the natural evaluation map.**
  `∀ i v l, e.symm (of i (v ⊗ₜ l)) = l v` (`:868`) pins the equivalence to the canonical
  evaluation `v ⊗ f ↦ f v`, certifying it is `A ⊗ B`-equivariant (as the docstring derives:
  `e.symm (of i (v ⊗ (b • l))) = b.val (l v)`), not an ad hoc bijection. This is the book's
  "as a representation of `A ⊗ B`" content made explicit. ✓

**Completeness caveat (non-defect).** The bimodule statements assert the `V_i` are the
distinct simples *appearing in `E`* and the `L_i` the corresponding simple `B`-modules; they
do not *separately* assert "these exhaust *all* irreps of `A` (resp. `B`)." Mathematically the
exhaustion follows from `[FaithfulSMul A E]` (every simple `A`-module embeds in a faithful
semisimple `E`) and from `B ≅ ⊕_i End(L_i)`, so no book case is lost; the statements simply
leave the exhaustion implicit rather than as an extra conjunct. Recorded as a mild
under-statement, not an error.

## Non-vacuity of the supporting `noncomputable def`s

All supporting defs have genuine, non-trivial bodies (checked by reading each construction):

- `isotypicDirectSumEquiv` (`:39`) — real `iSupIndep.linearEquiv` from independence
  (`sSupIndep_isotypicComponents`) + `iSup = ⊤` (`sSup_isotypicComponents`). Genuine.
- `endOfSimpleEquivAlgClosed` (`:64`) — `LinearEquiv.ofBijective` of the algebra map
  `k → End_A V`, bijective by `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`
  (Schur + alg-closed). Genuine; `endOfSimpleEquivAlgClosed_symm_smul_apply` pins its inverse.
- `homCongrRightOverSubring`, `homPiCurryEquiv` (`:99`, `:120`) — explicit compose/curry
  equivalences with proved inverse laws. Genuine.
- `schurEvaluationEquiv` (`:140`) — genuine 5-step chain; crucially
  `schurEvaluationEquiv_apply_tmul` (`:179`) proves it acts as evaluation `v ⊗ f ↦ f v`, so
  it is the canonical map, not a choice-dependent artifact.
- `homIsotypicBridge` (`:581`) — forward = compose with `c.subtype`, inverse = `codRestrict`
  justified by `range_le_isotypicComponent_of_simple`. Genuine.
- `centralizerToEndA`, `centralizerModuleHom`, `postCompCentralizerMonoidHom` (`:400`,
  `:427`, `:504`) — genuine ring-hom / module / monoid-hom via post-composition, all module
  axioms discharged. Genuine.

None are trivial (`0`, `id`-on-a-point, `True`-valued) constructions; each equivalence is real.

## Axiom check (deliverable 2)

`#print axioms` on all five headline declarations (via a scratch importer, `lake env lean`):

```
Etingof.Theorem5_18_1_double_centralizer            : [propext, Classical.choice, Quot.sound]
Etingof.Theorem5_18_1_commutant_semisimple          : [propext, Classical.choice, Quot.sound]
Etingof.Theorem5_18_1_decomposition                 : [propext, Classical.choice, Quot.sound]
Etingof.Theorem5_18_1_bimodule_decomposition        : [propext, Classical.choice, Quot.sound]
Etingof.Theorem5_18_1_bimodule_decomposition_explicit : [propext, Classical.choice, Quot.sound]
```

All axiom-clean: no `sorryAx`, no custom/non-standard axioms.

## Verification performed

- `lake exe cache get` (oleans downloaded), then
  `lake build EtingofRepresentationTheory.Chapter5.Theorem5_18_1` → exit 0 (only style
  linter warnings: `maxHeartbeats`-comment and `unusedSectionVars`; no errors).
- `grep -cE '\bsorry\b|\badmit\b'` on the file = 0.
- `#print axioms` on every headline decl = clean (above). Scratch importer removed after use.

## Verdict summary

| Declaration | Verdict |
|---|---|
| (i) `Theorem5_18_1_double_centralizer` | **FAITHFUL** |
| (ii) `Theorem5_18_1_commutant_semisimple` | **FAITHFUL** |
| (iii) `Theorem5_18_1_decomposition` | **TRUE but WEAK** — deliberate weak precursor; full content in the bimodule forms; no defect |
| (iii) `Theorem5_18_1_bimodule_decomposition` | **FAITHFUL** |
| (iii) `Theorem5_18_1_bimodule_decomposition_explicit` | **FAITHFUL** (strongest, canonical evaluation) |

**Overall: FAITHFUL, axiom-clean.** Book parts (i), (ii), (iii) are each faithfully
formalized; part (iii)'s full double-centralizer content (distinct simple `V_i`, simple
`B`-modules `W_i = Hom_A(V_i,E)`, `A ⊗ B`-equivariant evaluation iso) lives in
`Theorem5_18_1_bimodule_decomposition_explicit`. The weak `Theorem5_18_1_decomposition` is a
true, honestly-documented precursor, not a masked defect. Report-only; no Lean changes, no
follow-up `feature` issue filed.

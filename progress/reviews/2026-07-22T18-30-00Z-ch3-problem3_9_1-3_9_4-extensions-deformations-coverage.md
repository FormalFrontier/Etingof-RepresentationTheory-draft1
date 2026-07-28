# Coverage-arm audit — §3.9 extensions & deformations (#7361)

Stage 3.7 coverage-arm audit of the two multi-part §3.9 problems:

- **Problem 3.9.1** — Extensions of representations and `Ext¹` (parts a–d)
- **Problem 3.9.4** — Formal deformations of representations (parts a–b)

Both files build sorry-free and are axiom-clean; this audit adds the missing
`coverage` field at sub-part granularity via a `derived` array on each item and
reconciles the (previously absent) coverage notes.

## Build & axioms

```
lake build EtingofRepresentationTheory.Chapter3.Problem3_9_1
           EtingofRepresentationTheory.Chapter3.Problem3_9_4
→ Build completed successfully (1959 jobs)
  (only two unusedVariables linter warnings on Problem3_9_1.lean:204 — the
   documented `_hf`/`_hf'` placeholder hypotheses of iso_of_sub_mem_coboundaries;
   no errors, no sorries)
```

`#print axioms` on the headline decls — all clean, no `sorryAx`:

| decl | axioms |
|------|--------|
| `blockOp_mul_iff_isCocycle` | propext, Quot.sound |
| `coboundaryOf_isCocycle` | propext, Classical.choice, Quot.sound |
| `coboundaryOf_eq_zero_iff` | propext, Quot.sound |
| `coboundaries_le_cocycles` | propext, Classical.choice, Quot.sound |
| `iso_of_sub_mem_coboundaries` | propext, Classical.choice, Quot.sound |
| `ext_iso_of_sub_smul_mem_coboundaries` | propext, Classical.choice, Quot.sound |
| `irreducible_ext_iso_iff_proportional` | propext, Classical.choice, Quot.sound |
| `isTrivial_of_ext1_subsingleton` | propext, Classical.choice, Quot.sound |

## Problem 3.9.1 — `covered_full`

| Part | Coverage | Headline decl | Notes |
|------|----------|---------------|-------|
| (a) 1-cocycle condition | covered_full | `blockOp_mul_iff_isCocycle` | genuine iff (block assignment is a rep) ↔ (f ∈ Z¹); `blockOp`, `cocycles`, `IsCocycle` all honest |
| (b) coboundaries, B¹⊆Z¹, Ext¹ | covered_full | `coboundaryOf_isCocycle`, `coboundaryOf_eq_zero_iff`, `coboundaries_le_cocycles`, `Ext1` | dX∈Z¹, dX=0 ↔ X A-linear, B¹⊆Z¹, Ext¹=Z¹/B¹. The named iso B¹≅Hom_k/Hom_A is an immediate corollary (range=coboundaries, kernel=Hom_A), not separately bundled |
| (c) B¹-equivalence classifies extensions | covered_full | `iso_of_sub_mem_coboundaries`, `converse_sub_mem_coboundaries_of_unitriangular_intertwines`, `ExtMod.nonempty_equiv_iff_intertwines`, `ExtMod.sub_mem_coboundaries_of_unitriangular_equiv` | Both directions are formalized for the intertwiner and for the genuine extension modules |
| (d) iso classes ↔ ℙ Ext¹ | covered_full | `irreducible_ext_iso_iff_proportional` | genuine iff over `[IsAlgClosed k]` for f.d. irreducible V,W; the faithful ℙ-form (nonzero ratio = line in ℙ Ext¹; f∈B¹ = split class). `[IsAlgClosed k]` is the correct hypothesis (Schur needs End_A=k), documented in the file |

### The (c) closure

The gap found by the original audit was closed by #7362.
`converse_sub_mem_coboundaries_of_unitriangular_intertwines` proves over a
general algebra that a unitriangular intertwiner forces `f − f' ∈ B¹`; it is
the exact converse to `iso_of_sub_mem_coboundaries` and remains distinct from
the irreducible part-(d) proportionality theorem. #7418 subsequently packages
the construction as actual modules `ExtMod f hf`, proves their short exact
sequence and quotient description, and restates both directions using genuine
module equivalences. Problem 3.9.1 is therefore `covered_full`; #7362 is
historically closed, not an outstanding follow-up.

## Problem 3.9.4 — `covered_full`

| Part | Coverage | Headline decl | Notes |
|------|----------|---------------|-------|
| (a) Ext¹(V,V)=0 ⇒ deformations trivial | covered_full | `isTrivial_of_ext1_subsingleton` | genuine; `FormalDeformation`, `constDeformation`, `IsIsomorphic`, `IsTrivial` all honestly constructed; `Ext1` = the in-book Z¹/B¹, not Mathlib `Ext` |
| (b) converse (open question; negative answer) | covered_full | `ConverseHolds`, `Problem3_9_4b`, `dualNumber_all_deformations_trivial`, `dualNumber_ext1_not_subsingleton`, `not_problem3_9_4b_dualNumber` | The source question is faithfully stated and the integrated provider proves the suggested dual-number case is a counterexample |

### The (b) classification (deliverable-1 honesty check)

`ConverseHolds` / `Problem3_9_4b` are `def … : Prop` statements recording the
converse. The book itself poses (b) as a question, so the interrogative source
unit remains `non_formalizable` in the Stage 3.2 claim inventory. The current
provider additionally answers it: every formal deformation of the
dual-number augmentation representation is constant, while an explicit
epsilon cocycle gives a nonzero self-`Ext¹` class;
`not_problem3_9_4b_dualNumber` combines these facts into the negative answer.
That provider-authored theorem is correctly recorded as derived
`covered_full` coverage without reclassifying the source question as an
assertion.

## Outcome

- `progress/items.json` now records both items as `covered_full`, with
  reconciled derived coverage for every book sub-part.
- The original follow-up #7362 is closed by the general unitriangular
  converse; #7418 supplies the actual extension-module packaging.
- #8101 supplies the dual-number negative answer to Problem 3.9.4(b), while
  preserving the source-question/derived-answer distinction.
- Prior `fidelity: verified` reviews stand and are reused; no full fidelity
  sweep redone.

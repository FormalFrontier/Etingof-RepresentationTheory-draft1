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
→ Build completed successfully (1962 jobs)
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
| `dualNumber_deformation_eq_const` | propext, Classical.choice, Quot.sound |
| `dualNumber_ext1_not_subsingleton` | propext, Classical.choice, Quot.sound |
| `not_problem3_9_4b_dualNumber` | propext, Classical.choice, Quot.sound |

## Problem 3.9.1 — `covered_partial`

| Part | Coverage | Headline decl | Notes |
|------|----------|---------------|-------|
| (a) 1-cocycle condition | covered_full | `blockOp_mul_iff_isCocycle` | genuine iff (block assignment is a rep) ↔ (f ∈ Z¹); `blockOp`, `cocycles`, `IsCocycle` all honest |
| (b) coboundaries, B¹⊆Z¹, Ext¹ | covered_full | `coboundaryOf_isCocycle`, `coboundaryOf_eq_zero_iff`, `coboundaries_le_cocycles`, `Ext1` | dX∈Z¹, dX=0 ↔ X A-linear, B¹⊆Z¹, Ext¹=Z¹/B¹. The named iso B¹≅Hom_k/Hom_A is an immediate corollary (range=coboundaries, kernel=Hom_A), not separately bundled |
| (c) B¹-equivalence classifies extensions | **covered_partial** | `iso_of_sub_mem_coboundaries` | **forward only** (f−f'∈B¹ ⇒ iso); the book's converse (unitriangular iso ⇒ f−f'∈B¹) is **not formalized** → gap **#7362** |
| (d) iso classes ↔ ℙ Ext¹ | covered_full | `irreducible_ext_iso_iff_proportional` | genuine iff over `[IsAlgClosed k]` for f.d. irreducible V,W; the faithful ℙ-form (nonzero ratio = line in ℙ Ext¹; f∈B¹ = split class). `[IsAlgClosed k]` is the correct hypothesis (Schur needs End_A=k), documented in the file |

### The (c) gap (deliverable-2 spot check)

Book part (c) asserts **both** directions. The Lean file proves only the
forward direction. The converse — *if `φ : U_f → U_{f'}` is an iso of the
special unitriangular form `[[1,∗],[0,1]]`, then `f − f' ∈ B¹`* — has no
standalone theorem. The part-(d) theorem `irreducible_ext_iso_iff_proportional`
handles an arbitrary `φ`, but only under `[IsAlgClosed k]` + finite-dimensional
+ irreducible, and concludes a possibly-nonunit ratio; it does **not** subsume
the elementary general-`A` unitriangular converse. This is a genuine strictly-
weaker-than-book sub-part → `covered_partial`, follow-up **#7362** opened.

## Problem 3.9.4 — `covered_full`

| Part | Coverage | Headline decl | Notes |
|------|----------|---------------|-------|
| (a) Ext¹(V,V)=0 ⇒ deformations trivial | covered_full | `isTrivial_of_ext1_subsingleton` | genuine; `FormalDeformation`, `constDeformation`, `IsIsomorphic`, `IsTrivial` all honestly constructed; `Ext1` = the in-book Z¹/B¹, not Mathlib `Ext` |
| (b) converse (open question) | **covered_full** | `not_problem3_9_4b_dualNumber` | answered negatively in the suggested dual-number case: the augmentation representation has only trivial formal deformations but nonzero self-`Ext¹` |

### The (b) classification (deliverable-1 honesty check)

`ConverseHolds` / `Problem3_9_4b` remain the interface for the converse
proposition. Issue #8097 resolves its truth value at the book's suggested
example. The dual numbers act on `k` through the augmentation, so `eps` acts by
zero. Mapping a deformation into `k⟦X⟧` shows that the image of `eps` is a
square-zero series and hence zero, while the image of `1` is the unique
idempotent series with constant coefficient `1`; consequently every deformation
is literally constant. The second-coordinate map is then exhibited as a nonzero
self-extension cocycle, and every coboundary is proved zero. Thus
`not_problem3_9_4b_dualNumber` refutes the converse and the sub-part is
`covered_full`.

## Outcome

- `progress/items.json`: Problem 3.9.1 remains `covered_partial`, while Problem
  3.9.4 is now `covered_full`;
  `coverage_arm: audited`, a reconciled `coverage_note`, `last_updated`,
  `lean_file` (list form), and a `derived` array covering every book sub-part
  ((a)–(d) for 3.9.1, (a)–(b) for 3.9.4). File parses.
- One follow-up `feature` issue opened: **#7362** (3.9.1(c) converse). No
  further follow-up for 3.9.4(b): issue #8097 resolves it negatively.
- Prior `fidelity: verified` reviews stand and are reused; no full fidelity
  sweep redone.

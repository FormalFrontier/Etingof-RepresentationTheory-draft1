# Mathlib Coverage for Book Definitions (Stage 2.4 Part 2)

## Overview

Analyzed all 83 `definition`-type items from `progress/items.json` against Mathlib v4.28.0.

| Match Quality | Count | Percentage |
|--------------|-------|------------|
| Exact        | 46    | 55%        |
| Partial      | 21    | 25%        |
| Gap          | 16    | 19%        |

**55% of definitions have exact Mathlib coverage.** An additional 25% have partial coverage (building blocks exist but assembly or adaptation is needed). Only 19% require definition from scratch.

## Per-Chapter Breakdown

| Chapter | Total | Exact | Partial | Gap |
|---------|-------|-------|---------|-----|
| Ch 2 (Basic notions of representation theory) | 25 | 19 | 6 | 0 |
| Ch 3 (General results of representation theory) | 5 | 4 | 1 | 0 |
| Ch 4 (Representations of finite groups: basic results) | 2 | 0 | 1 | 1 |
| Ch 5 (Representations of finite groups: further results) | 10 | 4 | 1 | 5 |
| Ch 6 (Quiver representations) | 12 | 2 | 5 | 5 |
| Ch 7 (Introduction to categories) | 13 | 12 | 1 | 0 |
| Ch 8 (Homological algebra) | 6 | 5 | 1 | 0 |
| Ch 9 (Structure of finite dimensional algebras) | 10 | 0 | 5 | 5 |

**Best coverage:** Chapters 7 (categories, 92% exact) and 2 (basic rep theory, 76% exact). These are foundational topics where Mathlib is strongest.

**Weakest coverage:** Chapters 6 (quiver representations), 5 (advanced finite group reps), and 9 (finite dimensional algebra structure) have the most gaps.

## Definitions NOT in Mathlib (Gap — Need From Scratch)

1. **Chapter4/Definition4.10.1**: Frobenius determinant (group determinant) — det of matrix X_G with entries x_{g_i g_j}
2. **Chapter5/Definition5.1.1**: Complex, real, and quaternionic type of irreducible representations
3. **Chapter5/Definition5.1.4**: Frobenius-Schur indicator (0/1/-1 based on type)
4. **Chapter5/Definition5.7.1**: Virtual representation and its character (representation ring/Grothendieck group)
5. **Chapter5/Definition5.14.2**: Kostka numbers K_{μ,λ}
6. **Chapter5/Definition5.23.1**: Algebraic (polynomial) representation of GL(V)
7. **Chapter6/Definition6.5.1**: Dimension vector of a quiver representation
8. **Chapter6/Definition6.6.1**: Sink and source vertices in a quiver
9. **Chapter6/Definition6.6.2**: Reversed quiver at a vertex
10. **Chapter6/Definition6.6.3**: Reflection functor F_i^+ (BGP reflection functors)
11. **Chapter6/Definition6.6.4**: Reflection functor F_i^-
12. **Chapter9/Definition9.3.1**: Cartan matrix of a finite dimensional algebra (multiplicities of simples in projective indecomposables)
13. **Chapter9/Definition9.4.1**: Projective dimension
14. **Chapter9/Definition9.4.3**: Homological dimension of a ring
15. **Chapter9/Definition9.5.1**: Linked simple modules and blocks
16. **Chapter9/Definition9.7.2**: Basic algebra

## Definitions with Different Mathlib Formulation (Partial — Need Adaptation)

Key items where Mathlib has a different formulation or only building blocks:

- **Indecomposable representation** (2.3.8): `Indecomposable` exists for order theory; module-specific version needs work
- **Quiver representation infrastructure** (2.8.3–2.8.10): `Quiver` exists but representation/subrepresentation/morphism API for quivers is limited; functorial approach via `CategoryTheory.Functor` from free category is available
- **Path algebra** (2.8.4): `Quiver.Path` exists but the full k-algebra structure needs assembly
- **Filtration** (3.4.1): `CompositionSeries` exists but general filtrations need `ℕ →o Submodule R M`
- **Unitary representation** (4.6.1): `InnerProductSpace` and `Representation` exist separately; compatibility condition needs stating
- **Dynkin diagram** (6.1.4): `CoxeterMatrix`/`CoxeterSystem` cover related concepts; explicit Dynkin diagram classification needs work
- **Root system concepts** (6.4.3/5/7): `RootPairing` is more abstract than the book's elementary quiver-based definitions
- **Tor functors** (8.2.3): Mathlib has `Tor` but API may be limited
- **Orthogonal idempotents** (9.1.2): `OrthogonalIdempotents` and `CompleteOrthogonalIdempotents` exist
- **Projective cover** (9.2.2): No dedicated type; needs construction from projective + essential epimorphism
- **Morita equivalence** (9.7.1): Expressible as `CategoryTheory.Equivalence (ModuleCat R) (ModuleCat S)` but no dedicated predicate

## Formalization Strategy Recommendations

1. **Chapters 2, 3, 7, 8 are ready** — most definitions have exact Mathlib matches. These chapters can begin formalization with minimal custom definitions.

2. **Chapter 5 gaps cluster around representation ring theory** — Frobenius-Schur indicators, virtual representations, Kostka numbers. These form a coherent block that could be formalized together.

3. **Chapter 6 gaps are quiver-specific** — BGP reflection functors, dimension vectors, sink/source. These are self-contained and could form an independent formalization module.

4. **Chapter 9 gaps are homological algebra extensions** — projective dimension, homological dimension, blocks, basic algebras. These build on Mathlib's existing homological algebra.

5. **No Chapter 2 or 3 gaps** — the foundational definitions are fully covered, meaning later chapters can reliably import from Mathlib.

## Verification

The following declarations were verified via `lake env lean` with `#check`:
- `Algebra`, `AlgHom`, `IsSimpleModule`, `FaithfulSMul`, `Quiver`
- `LieAlgebra`, `UniversalEnvelopingAlgebra`, `TensorProduct`
- `IsSemisimpleModule`, `IsSemisimpleRing`, `IsSolvable`
- `Nat.Partition`, `YoungDiagram`
- `CategoryTheory.Category`, `CategoryTheory.Adjunction`, `CategoryTheory.Abelian`
- `Module.Projective`, `Module.Injective`, `CategoryTheory.Projective`
- `CategoryTheory.projectiveResolution`, `Ext`
- `HomologicalComplex`, `CategoryTheory.ShortComplex`
- `LieModule`, `LieHom`, `Module.Dual`
- `CategoryTheory.Functor.Additive`, `CategoryTheory.Functor.Linear`
- `ExteriorAlgebra`, `Ideal.jacobson`, `CompositionSeries`
- `OrthogonalIdempotents`, `CompleteOrthogonalIdempotents`
- `RootPairing`, `CoxeterSystem`, `CoxeterMatrix`
- `Representation`, `Representation.dual`, `Representation.tprod`
- `MonoidAlgebra`, `CategoryTheory.Equivalence`

# Sorry Feasibility Audit: Ch5/Ch6/Ch9

**Date:** 2026-03-19
**Issue:** #1141
**Scope:** 10 files with uncovered sorries across Ch5 (7 files), Ch6 (2 files), Ch9 (1 file)

## Summary

| File | Sorries | Classification | Key Finding |
|------|---------|---------------|-------------|
| **Ch5/Corollary5_19_2** | 1 | Blocked | Requires Theorem5_18_4 (Schur-Weyl) |
| **Ch5/Proposition5_19_1** | 1 | Blocked | Zariski density argument, needs algebraic geometry |
| **Ch5/Theorem5_26_1** | 1 | Blocked | Forward Artin only; backward direction fully proved |
| **Ch5/Theorem5_27_1** | 1 | Blocked | Orbit method — 4 sub-theorems combined |
| **Ch5/Lemma5_25_3** | 2 | Needs infrastructure | Character inner product + identity evaluation |
| **Ch5/Theorem5_18_4** | 3 | Blocked | Core Schur-Weyl duality (3 parts) |
| **Ch5/Theorem5_22_1** | 1+2 def | Blocked | SchurModule + formalCharacter are opaque `sorry` |
| **Ch6/Theorem6_5_2** | 1 | Needs infrastructure | Parts (a)+(b) proved; part (c) needs reflection functor chain |
| **Ch6/Problem6_9_1** | 3 | Partially tractable | Part (c) proved; E_{n,λ} indecomposability nearly done |
| **Ch9/Example9_4_4** | 1 | Blocked | Hilbert syzygy theorem, not in Mathlib |

**Total:** 14 proof sorries + 2 definition sorries across 10 files.

## Detailed Findings

### Ch5/Corollary5_19_2 (1 sorry) — Blocked

Schur-Weyl decomposition of V⊗ⁿ as Sₙ × GL(V) representation. Imports Theorem5_18_4, which has 3 sorries. Even if 5.18.4 were proved, the partition-indexed decomposition requires additional infrastructure. Statement looks correct.

### Ch5/Proposition5_19_1 (1 sorry) — Blocked

GL(V) image spans centralizer. Requires a Zariski density argument (polynomial identity testing for invertible operators). No Mathlib support for this argument. Uses `diagonalActionImage` from the Theorem5_18_4 infrastructure (which is defined). Statement looks correct.

### Ch5/Theorem5_26_1 (1 sorry) — Blocked (partially proved)

**Notable:** The backward direction (span → covering) is **fully proved** (~40 lines). This is high-quality work: trivial representation constructed, proved simple, and a contrapositive argument shows all induced characters vanish at an uncovered element while the trivial character doesn't.

Only the forward direction (covering → span) is sorry'd. This requires Brauer's theorem on characterization of characters, which is deep character theory not in Mathlib.

### Ch5/Theorem5_27_1 (1 sorry) — Blocked

Orbit method classification for semidirect products. Four sub-statements (irreducibility, injectivity, surjectivity, character formula) in one sorry. Requires Mackey's criterion, induced representation theory. Statement looks well-formed.

### Ch5/Lemma5_25_3 (2 sorries) — Needs infrastructure

Field extension infrastructure (GaloisField p n → GaloisField p (2*n)) is **fully proved**: degree-2 extension, splitting, finrank = 2, algebra instances, scalar tower. GL₂ embedding, charW₁, charVα₁, and complementarySeriesChar are all defined.

Two remaining sorries:
1. `Lemma5_25_3_innerProduct`: ⟨χ,χ⟩ = 1 — requires evaluating a sum over all GL₂(𝔽_q) elements. Hard.
2. `Lemma5_25_3_dimension`: χ(1) = q-1 — requires evaluating character functions at the identity. Potentially tractable but involves multiple character function definitions with conditional sums.

### Ch5/Theorem5_18_4 (3 sorries) — Blocked

Core Schur-Weyl duality. All three parts (mutual centralizers, semisimplicity, decomposition) are sorry'd. Deep theorem requiring double commutant theory. Statement looks correct.

### Ch5/Theorem5_22_1 (1 proof sorry + 2 definition sorries) — Blocked

SchurModule and formalCharacter are **opaque `sorry` definitions** — not just unproved but undefined. The Weyl character formula theorem is also sorry'd. Nothing can be done until SchurModule is properly constructed (highest weight theory for GL_N). This blocks Proposition5_22_2 and Theorem5_23_2 downstream.

### Ch6/Theorem6_5_2 (1 sorry) — Needs infrastructure

**Notable:** Parts (a) and (b) of Gabriel's theorem are **fully proved**:
- Part (a) `Theorem_6_5_2a_finiteness`: Positive roots are finite. Complete proof via Cauchy-Schwarz bound + injection into bounded box.
- Part (b) `Theorem_6_5_2b_dimvec_is_positive_root`: Essentially definitional (wraps the hypotheses).

Part (c) `Theorem_6_5_2c_bijection` (each positive root ↔ unique indecomposable) is sorry'd. It delegates to:
- **Corollary6_8_3** (uniqueness): Structurally complete but depends on 2 sorry'd lemmas:
  - `reflectionFunctors_reduce_and_recover`: Reflection functor chain argument
  - `indecomposable_titsForm_le_two`: Requires Ringel's Ext formula
- **Corollary6_8_4** (existence): Base case fully proved via `simpleRepresentation`. Inductive step (applying F⁻ᵢ) is sorry'd.

The blocker is the reflection functor chain machinery — connecting integer-level simple reflections to representation-level functors.

### Ch6/Problem6_9_1 (3 sorries) — Partially tractable

**Notable:** Part (c) `Problem6_9_1c` (nilpotent case) is **fully proved** (~40 lines showing BA nilpotent from AB nilpotent and prodMap nilpotent).

Data structures Q₂Rep and Q₂Rep.Indecomposable are well-defined. The E_{n,λ} family construction (`Q₂Rep_E`) and H_n family (`Q₂Rep_H`) are defined.

Three remaining sorries:
1. **`Q₂Rep_E_indecomposable`** (line 104): The proof reduces to showing a single Jordan block has no nontrivial invariant direct summands. All the compatible-decomposition logic (B=Id forces pW=pV via dimension counting) is **complete**. Only the final step remains. **This is the most tractable sorry in the entire audit.** Difficulty 2/3.
2. `Problem6_9_1` (line 136): Main classification theorem. Needs Jordan normal form.
3. `Problem6_9_1b` (line 150): Non-nilpotent decomposition. Needs eigenvalue extraction.

### Ch9/Example9_4_4 (1 sorry) — Blocked

Hilbert syzygy theorem. `homologicalDimension` is properly defined via `CategoryTheory.HasProjectiveDimensionLE` on ModuleCat. Statement is `homologicalDimension (MvPolynomial (Fin n) k) = n` (coercion ℕ → ℕ∞ is implicit). This is a deep result in commutative algebra, not in Mathlib.

## Statement Correctness

All 10 files have **correct-looking statements**. No type mismatches, missing hypotheses, or placeholder `True` propositions found. The only concern is Theorem5_22_1's opaque definitions (SchurModule, formalCharacter), but these are explicitly marked as placeholders.

## Tractability Summary

### Tractable now (1 item)
- **Q₂Rep_E_indecomposable** (Problem6_9_1, line 104): Jordan block has no nontrivial invariant direct sum decomposition. All surrounding proof is complete. Difficulty 2/3.

### Needs infrastructure (3 items)
- **Lemma5_25_3** (2 sorries): Field extension infrastructure done; character calculations remain
- **Theorem6_5_2c** (1 sorry): Parts (a)+(b) done; reflection functor chain needed
- **Corollary6_8_4** inductive step: Simple representation base case done; functor application needed

### Blocked (6 items)
- **Corollary5_19_2**: Schur-Weyl (Theorem5_18_4)
- **Proposition5_19_1**: Zariski density
- **Theorem5_26_1 forward**: Brauer character theory
- **Theorem5_27_1**: Orbit method
- **Theorem5_18_4**: Double commutant theory
- **Theorem5_22_1**: SchurModule undefined
- **Example9_4_4**: Hilbert syzygy theorem

## Recommendations

1. **Create feature issue** for Q₂Rep_E_indecomposable — most tractable sorry found
2. The Ch5 Schur-Weyl cluster (Theorem5_18_4 → Corollary5_19_2, Proposition5_19_1) is the single biggest blocker — 5 sorries across 3 files, all gated on one deep theorem
3. Theorem5_26_1's backward direction and Problem6_9_1c are examples of excellent partial proofs that should be preserved

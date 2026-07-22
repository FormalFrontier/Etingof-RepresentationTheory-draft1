# Fidelity + coverage-arm audit — Problem 5.11.1 (induced reps of A₅)

- **Issue:** #7350 (Stage 3.7 coverage-arm audit + stale-note reconciliation)
- **Date (UTC):** 2026-07-22
- **Item:** `Chapter5/Problem5.11.1`
- **Lean:** `EtingofRepresentationTheory/Chapter5/Problem5_11_1.lean` (2788 lines, **0 sorries**)
- **Blob:** `blobs/Chapter5/Problem5.11.1.md` (p.112)
- **Verdict:** **covered_full** across all five parts / 11 headline theorems; **fidelity verified**. No gap → no follow-up issue.

## Book statement

Compute the decomposition into A₅-irreducibles of every representation of A₅
induced from an irreducible of the subgroups (a) ℤ₂, (b) ℤ₃, (c) ℤ₅, (d) A₄,
(e) ℤ₂×ℤ₂.

## What the Lean actually proves

`ind σ := FDRep.of (Etingof.Definition5_8_1 H σ.ρ)` is the honest induced
representation. Each headline theorem asserts `Nonempty (ind σ ≅ …)` — a genuine
FDRep ℂ A₅ isomorphism — obtained via the sorry-free `Etingof.charEq_iso`
(equal characters over ℂ for a finite group ⇒ isomorphic; `CharEqIso.lean:263`,
axiom-clean). These are **not** bare character or dimension equalities.

The five summands are the honest distinct A₅ irreducibles from
`Chapter4/Example4_8_1` (`repTriv`, `repC3plus`, `repC3minus`, `repC4`,
`repC5`), each with a `Simple` lemma and finrank 1, 3, 3, 4, 5 respectively.
A₅ has exactly these five irreducibles, so the target catalogue is complete and
the biproducts are explicit nonempty `⊞`-chains (never an empty index).

Every theorem quantifies over an **arbitrary** subgroup `H : Subgroup A5` of the
stated order; the reduction to a concrete representative uses genuine conjugacy
lemmas `exists_conj_H` (order 2), `exists_conj_H3` (3), `exists_conj_H5`
(5, Sylow), `exists_conj_H12` (12). The order-4 case reduces to the concrete V₄.
So no part is silently restricted to one hand-picked subgroup. The inducing
irrep is distinguished by dimension/triviality, covering every irreducible of
each subgroup.

| Part | Theorem | Inducing irrep | Decomposition | dim |
|------|---------|----------------|---------------|-----|
| (a) ℤ₂ | `indZ2_triv` | trivial | 1 + 3 + 3′ + 4² + 5³ | 30 |
| (a) ℤ₂ | `indZ2_sign` | sign | 3² + 3′² + 4² + 5² | 30 |
| (b) ℤ₃ | `indZ3_triv` | trivial | 1 + 3 + 3′ + 4² + 5 | 20 |
| (b) ℤ₃ | `indZ3_nontriv` | ω, ω² | 3 + 3′ + 4 + 5² | 20 |
| (c) ℤ₅ | `indZ5_triv` | trivial | 1 + 3 + 3′ + 5 | 12 |
| (c) ℤ₅ | `indZ5_nontriv` | nontrivial | (3 + 4 + 5) ∨ (3′ + 4 + 5) | 12 |
| (d) A₄ | `indA4_triv` | trivial | 1 + 4 | 5 |
| (d) A₄ | `indA4_nontriv_linear` | ω, ω² | 5 | 5 |
| (d) A₄ | `indA4_threeDim` | 3-dim | 3 + 3′ + 4 + 5 | 15 |
| (e) V₄ | `indV4_triv` | trivial | 1 + 4 + 5² | 15 |
| (e) V₄ | `indV4_nontriv` | nontrivial | 3 + 3′ + 4 + 5 | 15 |

The ℤ₅-nontrivial case is an honest disjunction: the two nontrivial-character
orbits induce into one of the two 5-cycle-class orderings, and both 3-dim irreps
(3 and 3′) appear across the two disjuncts. This faithfully renders the book's
"in one order or the other" and is not a weakening.

## Multiplicity spot-check (parts (a) and (d), the richest)

A₅ character table (classes 1, 2a, 3a, 5a, 5b):

- triv: 1, 1, 1, 1, 1
- 3: 3, −1, 0, (1+√5)/2, (1−√5)/2
- 3′: 3, −1, 0, (1−√5)/2, (1+√5)/2
- 4: 4, 0, 1, −1, −1
- 5: 5, 1, −1, 0, 0

Frobenius reciprocity mult(ψ) = ⟨ψ|_H, σ⟩_H:

- `indZ2_triv` = (χ(1)+χ(2a))/2 → (1,1,1,2,3). ✓
- `indZ2_sign` = (χ(1)−χ(2a))/2 → (0,2,2,2,2). ✓
- `indA4_triv` (coset perm rep on A₅/A₄) → (1,0,0,1,0) = triv⊕4. ✓
- `indA4_nontriv_linear` (ω factors through A₄/V₄≅ℤ₃): 8−4(ζ+ζ²)=12 for ψ=5, 0
  elsewhere → (0,0,0,0,1). ✓
- `indA4_threeDim` (χ_W = (3,−1,0,0) on A₄) → (0,1,1,1,1). ✓

All dimensions satisfy dim(Ind) = (60/|H|)·dim σ. Matches the Lean statements.

## Axioms

`#print axioms` on all 11 headline theorems: `[propext, Classical.choice,
Quot.sound]` only — no `sorryAx`.

## Build

`lake build EtingofRepresentationTheory.Chapter5.Problem5_11_1` succeeds (8602
jobs); only benign `unusedDecidableInType` linter warnings on
`indV4_nontriv_value` / `indV4_nontriv_char_all`. `sorry count: 0` reconfirmed.

## Stale-note reconciliation

The prior `coverage_note` claimed only part (a) was proved and parts (b)-(e)
were "still sorry" — directly contradicted by the 0-sorry file on `origin/main`
(all 11 headline theorems present and axiom-clean). Replaced with a note
matching the actual state, and added `coverage = covered_full`, a `derived`
array (11 sub-parts), `fidelity = verified`, `lean_file`, and `last_updated`.

## Outcome

No fidelity gap. No follow-up `feature` issue required.

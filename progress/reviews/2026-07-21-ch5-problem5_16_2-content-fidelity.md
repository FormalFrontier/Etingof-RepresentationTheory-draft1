# Stage 3.7 fidelity audit — Chapter 5 Problem 5.16.2 (#7220)

**Item:** `Chapter5/Problem5.16.2` — "C = ∑(ij) acts on the Specht module V_λ by the content c(λ)"
**Lean file:** `EtingofRepresentationTheory/Chapter5/Problem5_16_2.lean` (sorry-free)
**Headline:** `Etingof.sumTranspositions_mul_eq_content_smul`
**Verdict: VERIFIED**

## Book claim (blob `blobs/Chapter5/Problem5.16.2.md`)

The content of a Young diagram λ is `c(λ) = ∑_j ∑_{i=1}^{λ_j} (i − j)`. With
`C = ∑_{i<j} (ij) ∈ ℂ[S_n]` the sum of all transpositions, show `C` acts on the
Specht module `V_λ` by multiplication by `c(λ)`.

## Deliverable 1 — sign/indexing convention (the flagged risk)

The critical failure mode is a sign flip in the eigenvalue scalar. Checked explicitly:

- **Mathlib `YoungDiagram.cells` convention.** Cells are pairs `(row, col)` with
  `.1` = row, `.2` = col. Confirmed in-file via `YoungDiagram.mem_ofRowLens`: membership
  unfolds to `cell.1 < w.length ∧ cell.2 < w.getElem cell.1`, i.e. `.1` indexes which
  part (row) and `.2` indexes the position within that row (column). `Nat.Partition.toYoungDiagram`
  is built by `ofRowLens` from the parts, so parts are rows.
- **Lean `content`.** `content la = ∑ c ∈ cells, ((c.2 : ℤ) − (c.1 : ℤ))` = ∑ (col − row).
- **Book `c(λ) = ∑_j ∑_{i=1}^{λ_j} (i − j)`.** The outer index `j` ranges over parts
  (`λ_j` is the j-th part), so `j` = row; the inner `i` runs `1..λ_j`, i.e. over the cells
  of row `j`, so `i` = column. Thus `(i − j)` = col − row. Both indices are 1-based, but a
  difference of indices is invariant under a common shift, so the 1-based `(i − j)` equals
  the 0-based `(col − row)`.

**Conclusion:** Lean `content` = book `c(λ)` exactly. No sign flip. (This also matches the
standard content convention col − row.)

### Numerical cross-check (independent of the Lean proof)

Content computed as ∑(col − row) vs. the sum-of-transpositions eigenvalue on each S₃ irrep,
computed independently as `|class| · χ(transposition) / dim` (class of transpositions has size 3):

| λ         | irrep    | content | `3·χ(τ)/dim` |
|-----------|----------|---------|--------------|
| (3)       | trivial  | 3       | 3·1/1 = 3    |
| (2,1)     | standard | 0       | 3·0/2 = 0    |
| (1,1,1)   | sign     | −3      | 3·(−1)/1 = −3|

All three agree, confirming the scalar's sign is correct.

## Deliverable 2 — non-vacuity

- `SpechtModule n la = Submodule.span (SymGroupAlgebra n) {YoungSymmetrizer n la}` — the
  genuine left ideal `ℂ[S_n]·c_λ`, not `⊤` or `⊥`. It contains `c_λ ≠ 0` and is proved a
  simple module by `Theorem5_12_2_irreducible` (used in the proof via Schur's lemma).
- `sumTranspositions n = ∑_{p.1 < p.2} of(swap p.1 p.2)` is genuinely `∑_{i<j}(ij)`, not a
  rewritten trivial element.
- The headline quantifies over **all** `x ∈ SpechtModule n la`, asserting
  `sumTranspositions n * x = (content la : ℂ) • x`. This is exactly "C acts on V_λ by
  multiplication by c(λ)", with no weakening.

## Actions

- `progress/items.json` `Chapter5/Problem5.16.2`: `fidelity → verified`, `sorry_free: true`,
  `fidelity_note` recording the convention check and cross-check.
- No Lean files modified; item remains `sorry_free`. `lake build` unaffected.

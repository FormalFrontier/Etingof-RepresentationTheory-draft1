Stage 3.7 **coverage-arm audit** of the coupled pair **Problem 5.16.2** (the
sum-of-transpositions central element `C` acts on `V_λ` by the content
`c(λ)`) and **Problem 5.16.3** (the element `E = (12)+…+(1n)` is diagonalizable
with integer eigenvalues, and acts by a scalar on `V_λ` iff `λ` is rectangular).
Audited together because 5.16.3 is built directly on 5.16.2's `C` (via
`E = C_n − C_{n-1}`). Continues the §5.16/§5.24 symmetric-group sweep.

## Current state

- Blobs: `blobs/Chapter5/Problem5.16.2.md`, `blobs/Chapter5/Problem5.16.3.md`.
  - 5.16.2 (single part): `C = ∑_{i<j}(ij)` acts on `V_λ` by `c(λ) = ∑_j ∑_{i=1}^{λ_j}(i−j)`.
  - 5.16.3(a): `E := (12)+…+(1n)` is diagonalizable with integer eigenvalues in
    `[1−n, n−1]` on any f.d. rep (hint: `E = C_n − C_{n−1}`).
  - 5.16.3(b): `E` acts by a scalar on `V_λ` **iff** `λ` is rectangular; compute
    that scalar.
- Lean (both sorry-free):
  - `Chapter5/Problem5_16_2.lean` (481 lines): `sumTranspositions`, `content`,
    headline `sumTranspositions_mul_eq_content_smul` (`C · c_λ = c(λ) • c_λ`).
  - `Chapter5/Problem5_16_3.lean` (968 lines): `sumTranspositionsWith1` (=E),
    `IsRectangular`, `sumTranspositionsWith1_eq_sub` (E = C_n − C_{n−1}),
    `sumTranspositionsWith1_hasEigenvalue_integer`, headline
    `sumTranspositionsWith1_diagonalizable_integer_eigenvalues` for (a); check
    the file for the (b) rectangular-iff-scalar statement and its scalar value.
- `progress/items.json` items `Chapter5/Problem5.16.2` and
  `Chapter5/Problem5.16.3` have **no `coverage` field** yet.

## Deliverables

1. Assign `coverage` to `Chapter5/Problem5.16.2` (single claim) and to each
   sub-part of `Chapter5/Problem5.16.3` — (a) diagonalizable + integer
   eigenvalue bound, (b) rectangular-iff-scalar **and** the computed scalar
   value — recording per-sub-part `derived` entries (claim, source_span,
   lean_decl, coverage), mirroring the §5.24 / §4.12.2 audit structure.
2. Fidelity check (Stage 3.2 steps 6–7, different judge model): confirm
   non-vacuity — `content` is the genuine `∑(i−j)` over cells; the eigenvalue
   bound `[1−n, n−1]` is actually asserted (not just "integer"); part (b)'s
   `iff` is a real biconditional and the scalar is **computed**, not left
   abstract. If 5.16.3(b)'s scalar is not actually pinned down in Lean, or the
   `[1−n,n−1]` bound is missing, mark that sub-part `covered_partial` and open a
   follow-up `feature` issue with the precise gap. Do not pass a weaker
   statement off as `covered_full`.
3. Set each parent roll-up `coverage` to the min over its sub-parts.

## Context

- Read-only audit + items.json bookkeeping (plus follow-up issues for any gap).
  No new Lean proofs; do not touch the sorry-free Lean unless fixing a genuine
  fidelity gap.
- 5.16.3 explicitly reuses 5.16.2, so verifying the `E = C_n − C_{n−1}` bridge
  (`sumTranspositionsWith1_eq_sub`) faithfully connects the two is part of the
  audit.
- Sibling audits for format: merged §4.12 (PR #7324), in-flight §5.24 (#7328,
  #7334).

## Verification

- `progress/items.json`: both items have `coverage` fields with per-sub-part
  `derived` arrays; every accepted gap has a follow-up issue.
- `lake build EtingofRepresentationTheory.Chapter5.Problem5_16_2` and
  `…Problem5_16_3` still succeed.
- A progress file records the decisions and any follow-up issue numbers.

# Stage 3.2 fidelity review — Chapter 3 §3.6

## Scope

Reading order gives exactly three §3.6 catalog items, the contiguous `progress/items.json`
range 156–158:

1. `Chapter3/Introduction_to_3.6`;
2. `Chapter3/Exercise3.6.1`;
3. `Chapter3/Theorem3.6.2`.

The preceding item is `Chapter3/Proposition3.5.8`; the next item, and strict stopping boundary,
is `Chapter3/Introduction_to_3.7`. The source is pages 52–53. No §3.5 or §3.7 content is in
scope.

## Claim audit

The source pages, all three exact blobs, and all four §3.6 Lean providers were read in full.
The durable inventory has 19 claim units:

- 12 `formalized` by exact scoped declarations;
- 6 `covered_elsewhere` by the density theorem, Wedderburn–Artin, Theorem 3.3.1, and Mathlib's
  matrix-unit infrastructure;
- 1 `non_formalizable` organizational heading;
- no accidental gap, intentional omission, or unclassified hard mathematical claim.

The introduction's complete definition chain is present: `Etingof.character` is the genuine
trace-of-action functional; `commutatorSubmodule` is the span of `xy - yx`;
`commutatorSubmodule_le_ker_character` proves vanishing; and `characterQuotient` with
`characterQuotient_mk` gives the claimed quotient functional and factorization equation.

Exercise 3.6.1 is exact and non-vacuous. Its theorem quantifies an arbitrary
`W : Submodule A V`, uses the honest quotient representation `V ⨸ W`, and proves equality in
`Dual k A`; it is not restricted to a selected or split subrepresentation.

Both parts of Theorem 3.6.2 are faithful. Part (i) has no finite-dimensional hypothesis on the
algebra itself and uses the density theorem to isolate each trace coefficient. Part (ii) models
`(A/[A,A])*` by the canonically equivalent space of tracial functionals: part (i) supplies linear
independence, and `characters_basis_semisimple` supplies spanning for a complete pairwise
nonisomorphic family of irreducibles. This is the book's basis statement split into its two
standard obligations rather than weakened.

The proof's matrix identity is also public:
`commutatorSubmodule_matrix_eq_ker_trace` and its exact `Fin d` specialization prove
`[Mat_d(k),Mat_d(k)] = sl_d(k)`, including the empty and one-dimensional edge cases. The proof
contains the matrix-unit commutator and diagonal-correction construction; standard matrix-unit
basis facts, Wedderburn–Artin decomposition, and the earlier irreducible classification are
honestly recorded as `covered_elsewhere` rather than duplicated.

No Lean repair was necessary. The earlier fidelity defect that unnecessarily assumed the
algebra finite-dimensional in part (i) is already fixed, and the formerly missing public matrix
commutator endpoint is already present.

## Durable tracker result

All three scoped items now have complete Stage 3.2 `claim_coverage` records with verified
definition integrity, statement fidelity, and nonvacuity. Every item is `covered_full` and
`fidelity = verified`; only the organizational heading itself has a claim-level
`non_formalizable` verdict. The normalized non-§3.6 tracker projection and both dependency maps
are unchanged from `origin/main` at `b2d26b8c`.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared package cache;
- all four scoped providers build successfully together (1,957 jobs);
- `lake build EtingofRepresentationTheory.Chapter3` succeeds (8,692 jobs; reported warnings are
  pre-existing and outside this Stage 3.2 metadata-only change);
- the scoped scan finds no `sorry`, `admit`, `axiom`, `proof_wanted`, `opaque`, or
  `native_decide` declaration;
- `#check` resolves all 17 distinct declarations cited by the inventory, and `#print axioms`
  reports only `propext`, `Classical.choice`, and `Quot.sound` for every checked declaration;
- `jq` parsing, the exact three-item/19-claim aggregation, and the strict boundary check pass;
- all four repository validators pass;
- normalized non-scope tracker comparison, unchanged dependency-map checks, and
  `git diff --check` pass.

This PR is limited to Chapter 3 §3.6 and Stage 3.2.

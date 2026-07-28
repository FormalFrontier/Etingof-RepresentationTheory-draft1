# Stage 3.2 fidelity review — Chapter 3 §3.5

## Scope

Reading order gives exactly nine §3.5 catalog items, the contiguous `progress/items.json` range
147–155:

1. `Chapter3/Introduction_to_3.5`;
2. `Chapter3/Definition3.5.1`;
3. `Chapter3/Proposition3.5.2`;
4. `Chapter3/Proposition3.5.3`;
5. `Chapter3/Theorem3.5.4`;
6. `Chapter3/Corollary3.5.5`;
7. `Chapter3/Example3.5.6`;
8. `Chapter3/Definition3.5.7`;
9. `Chapter3/Proposition3.5.8`.

The preceding item is `Chapter3/Lemma3.4.2`; the next item, and strict stopping boundary, is
`Chapter3/Introduction_to_3.6`. The source is pages 49–52, including the zero-algebra footnote.
No §3.6 content is in scope.

## Claim audit

Pages 49–52 and all ten §3.5 providers were read in full. The durable inventory has 26 claim
units:

- 22 `formalized` by exact scoped declarations;
- 2 `covered_elsewhere` by the density theorem and standard finite-dimensional dimension lemmas;
- 2 `non_formalizable` organizational or underspecified prose units;
- no accidental gap, intentional omission, or unclassified hard mathematical claim.

The audit covers the Jacobson-radical encoding and its two-sidedness; both halves and the
largest-ideal conclusion of Proposition 3.5.3; cyclicity, finite dimensionality, finiteness,
exhaustiveness, the cardinal bound, the aggregate density map, its kernel, and the quotient
algebra isomorphism in Theorem 3.5.4; the full dimension argument of Corollary 3.5.5; both
radical computations and both irreducible-representation classifications in Example 3.5.6;
the definition of semisimplicity; all five conditions of Proposition 3.5.8; and every assertion
in its zero-algebra footnote.

No Lean repair was necessary. Current `main` already contains the recently completed family
construction for Theorem 3.5.4 and all six public zero-algebra endpoints from closed issue #7468
and PR #7610. The tracker was stale only for Proposition 3.5.8: its old `covered_partial` /
`fidelity: partial` record still described the now-closed footnote gap. It is reconciled to
`covered_full` / `verified`.

The sentence “a similar result holds for block-triangular matrices” is recorded as
`non_formalizable`: the source specifies no block decomposition, diagonal-block hypotheses,
representation family, or radical formula, so it does not determine a unique theorem. This is
not counted as a missing formal claim. The scalar upper-triangular classification and radical
identity immediately preceding it are fully formalized.

Definition integrity is verified: `Etingof.Radical` is the Jacobson radical, equivalent to the
common annihilator of simple modules, and `Etingof.IsSemisimpleAlgebra` uses Mathlib's
`IsSemisimpleRing`, equivalent to vanishing Jacobson radical for the finite-dimensional
(Artinian) algebras in scope. Statement fidelity and nonvacuity are verified for every theorem:
the family is actually constructed and exhaustive, the structure results return genuine algebra
or module equivalences, and the zero-algebra results use explicit subsingleton hypotheses rather
than impossible assumptions.

## Durable tracker result

All nine scoped items now have complete Stage 3.2 `claim_coverage` records with verified
definition integrity, statement fidelity, and nonvacuity. Every item is `covered_full`; the two
prose-only units retain claim-level `non_formalizable` verdicts. The normalized non-§3.5
projection of `progress/items.json` and both dependency maps are unchanged from `origin/main`.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared package cache;
- all ten scoped providers build successfully together (1977 jobs);
- `lake build EtingofRepresentationTheory.Chapter3` succeeds (8692 jobs); replayed warnings are
  pre-existing and Stage 3.5 proof-polish concerns, not Stage 3.2 claim gaps;
- the scoped scan finds no `sorry`, `admit`, `axiom`, `proof_wanted`, `opaque`, or
  `native_decide` declaration;
- representative `#print axioms` checks for the central endpoints report only `propext`,
  `Classical.choice`, and `Quot.sound`;
- all 40 distinct declarations cited by the claim inventory resolve under the Chapter 3 umbrella;
- `jq empty progress/items.json`, the exact nine-item/26-claim aggregation, and the strict
  boundary check pass;
- `python3 scripts/validate_items.py` passes with complete source-line coverage;
- `python3 scripts/validate_dependencies.py`, `validate_external_deps.py`, and
  `validate_mathlib_coverage.py` all pass;
- normalized non-scope tracker comparison, unchanged dependency-map checks, and
  `git diff --check` pass.

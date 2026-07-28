# Stage 3.2 fidelity review — Chapter 3 §3.1

## Scope

Reading order gives exactly ten §3.1 catalog items, the contiguous `progress/items.json` range
124–133:

1. `Chapter3/Introduction`;
2. `Chapter3/Definition3.1.1`;
3. `Chapter3/Example3.1.2`;
4. `Chapter3/Remark3.1.3`;
5. `Chapter3/Discussion_before_Proposition3.1.4`;
6. `Chapter3/Proposition3.1.4`;
7. `Chapter3/Remark3.1.5`;
8. `Chapter3/Discussion_alternative_proof_of_Proposition3.1.4`;
9. `Chapter3/Lemma3.1.6`;
10. `Chapter3/Discussion_after_Lemma3.1.6`.

The preceding item is `Chapter2/Problem2.16.5`; the next item, and strict stopping boundary, is
`Chapter3/Introduction_to_3.2`. The source is pages 43–45, including both footnotes; no §3.2
content is in scope.

## Claim audit and repairs

Pages 43–45 and all seven §3.1 Lean providers were read in full. The durable inventory has 28
claim units:

- 19 `formalized` directly by their scoped providers;
- 6 `covered_elsewhere` by precise project or Mathlib declarations;
- 3 `non_formalizable` organizational/setup/attribution units;
- no accidental gap, intentional omission, or unclassified hard mathematical claim.

The audit explicitly includes the evaluation formulas, the irreducible-base-case reduction,
both conclusions and the matrix qualifier of Proposition 3.1.4, the finite-dimensionality-free
footnote, every qualifier in Remark 3.1.5 (including the endomorphism division ring and “check
it!”), the naturality and all three componentwise criteria in the alternative proof, the B.
Poonen attribution, the maximal-subfamily proof content of Lemma 3.1.6, and every step in the
closing quotient/kernel calculation.

Stage 3.2 made three necessary scoped repairs:

1. `Discussion_alternative_proof_of_Proposition3_1_4.lean`, despite already containing the exact
   Hom-space equivalence and componentwise criteria, was absent from the Chapter 3 umbrella. It
   is now imported by `Chapter3.lean`.
2. `Etingof.mem_ker_iff_components` now exposes the exact componentwise kernel calculation used
   in the display after Lemma 3.1.6, under the canonical multiplicity-space equivalences.
3. The closing discussion's stale `covered_partial` / `fidelity: partial` marker and open-issue
   narrative were reconciled. Closed issue #7409 already supplied the exact given-subfamily form
   of Lemma 3.1.6, and the new kernel theorem plus the existing block classification finish the
   advertised alternative proof.

Definition integrity is verified: `Etingof.IsSemisimpleRepresentation` abbreviates semisimplicity
over the algebra `A`, and Mathlib's semisimple-module API identifies this with a direct sum of
simple modules, not the vacuous semisimplicity of the underlying vector space. Statement fidelity
and nonvacuity are verified for all theorem-bearing records: the key outputs are genuine linear
equivalences, arbitrary submodule classifications, injectivity/surjectivity equivalences, and a
concrete selected sub-sum, rather than implications with impossible hypotheses or proposition-only
wrappers.

## Durable tracker result

All ten scoped items now have complete Stage 3.2 `claim_coverage` records with verified definition
integrity, statement fidelity, and nonvacuity. Every item is `covered_full`; the two organizational
records retain claim-level `non_formalizable` verdicts, and the attribution is recorded separately.
The normalized non-§3.1 projection of `progress/items.json` is unchanged from `origin/main`.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared package cache;
- all seven scoped providers build successfully together (1977 jobs);
- `lake build EtingofRepresentationTheory.Chapter3` succeeds (8693 jobs); replayed warnings are
  pre-existing linter/style warnings;
- the scoped scan finds no `sorry`, `admit`, `axiom`, `proof_wanted`, `opaque`, or
  `native_decide` declaration;
- representative `#print axioms` checks for eight central declarations report only `propext`,
  `Classical.choice`, and `Quot.sound`;
- `jq empty progress/items.json`, the exact ten-item/28-claim aggregation, and the strict boundary
  check pass;
- `python3 scripts/validate_items.py` passes with 5721/5721 source-line coverage (plus its 593
  pre-existing extra-field warnings);
- `python3 scripts/validate_dependencies.py`, `validate_external_deps.py`, and
  `validate_mathlib_coverage.py` all pass;
- normalized non-scope tracker comparison and `git diff --check` pass.

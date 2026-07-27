# Stage 3.2 faithful formalization — Chapter 3 §3.3

## Exact scope

The audited interval is the seven consecutive catalog items at indices 137–143:

1. `Chapter3/Introduction_to_3.3`
2. `Chapter3/Theorem3.3.1`
3. `Chapter3/Discussion_before_Definition3.3.2`
4. `Chapter3/Definition3.3.2`
5. `Chapter3/Discussion_proof_of_Theorem3.3.1`
6. `Chapter3/Problem3.3.3`
7. `Chapter3/Remark3.3.4`

The immediate predecessor is `Chapter3/Theorem3.2.2`; the strict successor is
`Chapter3/Introduction_to_3.4`. This pass changes no item outside that interval.

## Source-to-Lean result

The seven source blobs contain 48 independently audited claim units: 34 are formalized directly,
10 are covered by named declarations elsewhere, and four are genuinely organizational or
methodological prose. There are no omissions, placeholders, or fidelity gaps.

The complete advertised proof of Theorem 3.3.1 through transpose self-duality is now present on
main: it constructs `Aⁿ → X*`, proves surjectivity, dualizes to an embedding, proves
`(Aⁿ)* ≃ Aⁿ`, decomposes the regular/free modules, and obtains the exact multiplicity
decomposition. The stale tracker record that still described follow-up #7517 as open is corrected
to `covered_full` and `verified`.

Problem 3.3.3 has full factor-algebra and matrix-unit coverage, including inflation from a unique
factor and the explicit decomposition of every finite-dimensional matrix-algebra module. Its
setup and proof hints are recorded at claim granularity rather than only by the three lettered
parts.

Remark 3.3.4 already supplied the free-cover map, formula, surjectivity, and quotient
identification. This pass adds `Etingof.freeCover_unique`, making the source's uniqueness claim
explicit. The exact final decomposition is already public; Lean reaches it through Proposition
3.1.4 rather than the book's quotient-form invocation of Lemma 3.1.6, so that proof-route unit is
honestly marked `covered_elsewhere` rather than left as an omission.

## Validation

- direct build of all four complete providers (1,698 jobs)
- declaration-name audit for every claim endpoint and accepted-axiom check for the new theorem
- scoped scan for `sorry`, `admit`, `proof_wanted`, project axioms, and `sorryAx`
- full `EtingofRepresentationTheory.Chapter3` build
- all repository metadata/dependency validators
- exact scope, predecessor/successor, claim aggregation, and non-scope invariance checks
- JSON parsing and `git diff --check`

This PR is limited to Section 3.3 and Stage 3.2.

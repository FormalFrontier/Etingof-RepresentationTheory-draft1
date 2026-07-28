# Stage 3.2 faithful formalization — Chapter 3 §3.4

## Exact scope

The audited interval is the three consecutive catalog items at indices 144–146:

1. `Chapter3/Introduction_to_3.4`
2. `Chapter3/Definition3.4.1`
3. `Chapter3/Lemma3.4.2`

The immediate predecessor is `Chapter3/Remark3.3.4`; the strict successor is
`Chapter3/Introduction_to_3.5`. This pass changes no item outside that interval and leaves the
existing conservative dependency metadata unchanged.

## Source-to-Lean result

The three source blobs contain 15 independently audited claim units: eight are formalized
directly, five proof-route or library-level units are covered by named declarations elsewhere,
and two are genuinely organizational or methodological prose. There are no omissions,
placeholders, or remaining fidelity gaps.

`Etingof.Filtration` already records all of Definition 3.4.1: a finite `RelSeries` of submodules,
strict adjacent inclusions, first term `⊥`, and last term `⊤`.

The former public statement of Lemma 3.4.2 only returned a Mathlib `CompositionSeries` with its
endpoints. This pass retains that theorem and adds
`Etingof.exists_filtration_with_irreducible_quotients`, whose conclusion uses the repository's
own `Etingof.Filtration` and explicitly proves `IsSimpleModule A` for every adjacent quotient.
The proof converts maximal composition-series steps to strict filtration steps and uses
`covBy_iff_quot_is_simple` to expose irreducibility. Thus the finite chain, both endpoints, and
the source's successive-quotient condition are all visible in the theorem type.

The book's induction-through-preimages proof route is represented honestly at claim granularity.
Lean uses the equivalent finite-length theorem obtained from Noetherian and Artinian module
instances; the quotient and preimage constructions are standard Mathlib declarations rather
than duplicate project wrappers.

## Validation

- direct build of both complete providers
- declaration-name and accepted-axiom audit for the new theorem
- scoped scan for `sorry`, `admit`, `proof_wanted`, project axioms, and `sorryAx`
- full `EtingofRepresentationTheory.Chapter3` build
- all four repository metadata/dependency validators
- exact scope, predecessor/successor, claim aggregation, and non-scope invariance checks
- JSON parsing and `git diff --check`

This PR is limited to Section 3.4 and Stage 3.2.

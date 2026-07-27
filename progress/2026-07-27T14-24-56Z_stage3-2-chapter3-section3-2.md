# Stage 3.2 claim coverage — Chapter 3 §3.2

## Scope

Audited the exact three-item reading-order interval from `Introduction_to_3.2` through
`Theorem3.2.2`, stopping before `Introduction_to_3.3`, against source pages 45–46.

## Claim inventory and fidelity

All twelve source units are accounted for: four endpoint/setup claims are formalized, five proof
or infrastructure units are covered by explicit declarations elsewhere, and three organizational,
attribution, or methodological units are non-formalizable. There are no hidden or intentional
omissions.

The public statements are faithful and nonvacuous:

- `Etingof.irreducible_interpolation` is the exact finite-dimensional irreducible interpolation
  corollary with `k`-linear independence.
- `Etingof.density_theorem_part1` is surjectivity of `A → End_k(V)`.
- `Etingof.density_theorem_part2` is simultaneous surjectivity for a finite family of pairwise
  nonisomorphic simples; its dependent-function codomain is the finite product/direct sum from the
  source.

The only substantive presentation difference is proof order. The book proves interpolation from
Proposition 3.1.4 and then density part (i). Lean proves part (i) independently from Mathlib's
Jacobson density theorem and derives interpolation from it. Part (ii) likewise uses a direct
product-module density proof. These are alternate proofs of the exact statements, not weakened
wrappers.

## Validation

- standalone builds of both providers
- scoped admission and project-axiom scan
- `#print axioms` on all three public declarations
- exact three-item, twelve-unit claim-coverage audit
- full `EtingofRepresentationTheory.Chapter3` build
- all three repository metadata/dependency validators
- JSON parsing and `git diff --check`

This PR is limited to Section 3.2 and Stage 3.2.

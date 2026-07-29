# Stage 3.2 review — Chapter 5, §5.4

## Scope and result

This review covers the thirteen records from `Chapter5/Introduction_5.4` through
`Chapter5/Discussion_proof_of_Theorem5.4.3`. The old #7514 and #7515 scalar-tower regression
notes are stale: all providers now pass fresh source checks and the repository build. The three
formerly partial theorem records and both proof-discussion records are therefore normalized to
full, verified, admission-free coverage.

## Solvability and the character-theoretic input

Mathlib's `IsSolvable` is the standard derived-series formulation equivalent to Definition
5.4.1. `Etingof.Lemma5_4_5` proves the roots-of-unity average dichotomy. In
`Etingof.Theorem5_4_4`, character values and class-sum scalars are shown integral, Bezout turns
their coprime combination into an integral eigenvalue average, and the lemma gives exactly the
source dichotomy: zero character or scalar action.

`Etingof.Lemma5_4_7` proves the precise existence statement required in the next argument:
a nontrivial irreducible representation of dimension not divisible by `p`, with nonzero character
at the chosen element.

## Nonsimplicity and Burnside's theorem

`Etingof.Theorem5_4_6` proves that a prime-power conjugacy class gives a proper nontrivial normal
subgroup. Its implementation follows the same character-table partition and algebraic-integer
contradiction but packages the final step as a proof that a simple group cannot have such a
class. The book's particular generated subgroup is consequently a proof-route witness rather
than a missing endpoint.

Finally, `Etingof.Theorem5_4_3` proves Burnside's theorem by strong induction on group order.
For a nonabelian group it uses the center when possible, and otherwise Sylow theory plus Theorem
5.4.6 to obtain a proper normal subgroup; solvability of that subgroup and the quotient then
implies solvability of the group. The public conclusion is exactly that every group of order
`p^a q^b` is solvable.

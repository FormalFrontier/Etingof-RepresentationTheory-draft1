# Stage 3.2 review — Chapter 5, §5.2

## Scope and result

This review covers the eleven records from `Chapter5/Introduction_5.2` through
`Chapter5/Remark5.2.8`. Every formalizable source endpoint is represented by an admission-free
project declaration or by a named Mathlib declaration. Problem 5.2.7 retains its authoritative
final-exercise audit, whose two source parts are both complete.

## Algebraic numbers and algebraic integers

`Etingof.Definition5_2_1_algebraic_number` and
`Etingof.Definition5_2_1_algebraic_integer` give the source's monic-polynomial definitions.
`Etingof.Definition5_2_2_algebraic` and `Etingof.Definition5_2_2_integer` give the exact
rational- and integer-matrix eigenvalue characterizations. Proposition 5.2.3 proves both
equivalences, and its companion-matrix proof route is exposed separately by
`Etingof.Proposition5_2_3.companionMatrix`, `charpoly_companionMatrix`, and
`charpoly_map_companionMatrix_isRoot`.

The notations Q-bar and Z-bar are genuine bundled subobjects:
`Etingof.algebraicNumbers` is an intermediate field and `Etingof.algebraicIntegers` is an
integral closure. Proposition 5.2.4 records the ring, field, algebraicity, algebraic-closedness,
and algebraic-closure conclusions. `Etingof.Proposition5_2_5` gives the exact intersection
statement for rational algebraic integers.

## Minimal polynomials, conjugates, and vanishing

The minimal-polynomial discussion is covered by Mathlib's `minpoly` API: `minpoly.monic`,
`minpoly.aeval`, `minpoly.min`, and `minpoly.dvd`. `IsConjRoot` identifies algebraic conjugacy
with equality of minimal polynomials; `IsConjRoot.isIntegral` proves preservation of integrality,
and `minpoly.isIntegrallyClosed_eq_field_fractions'` identifies the rational minimal polynomial
of an algebraic integer with the image of its monic integer minimal polynomial.
`Etingof.Lemma5_2_6` proves the stated conjugates-of-a-sum result for an arbitrary finite sum.

Problem 5.2.7 formalizes both the common finite Galois field of definition and the vanishing of
an irreducible character of dimension greater than one. Remark 5.2.8 formalizes the alternative
cyclotomic proof: the coprime power-map bijection and product reindexing, the roots-of-unity
description of character values, the induced Galois action, rationality and integrality of the
product beta, and the final contradiction with the bound supplied by Problem 5.2.7(b).

All §5.2 records now have complete claim ledgers with verified definition integrity, statement
fidelity, and nonvacuity; the problem's more detailed per-part ledger remains unchanged.

# Stage 3.2 claim coverage: Chapter 2 §2.14

## Scope

Audited the exact four-item reading-order interval from `Discussion_2.14_heading` through
`Problem2.14.3`, stopping before `Discussion_2.15_heading`, against the source on page 37.

## Claim inventory

- `Discussion_2.14_heading`: one organizational, non-formalizable unit.
- `Definition2.14.1`: two formalized units—the tensor-product carrier and its Leibniz Lie action.
- `Definition2.14.2`: two formalized units—the dual carrier and contragredient action—and one
  unit covered by Mathlib's genuine Lie-module instances for both constructions.
- `Problem2.14.3`: the requested Hom-space isomorphism is formalized directly; the parenthetical
  identification of Lie-representation morphisms with enveloping-algebra module morphisms is
  covered by the representation equivalence established in Exercise 2.9.11.

All eight mathematical/organizational units are accounted for: five are formalized, two are
covered elsewhere, and one is non-formalizable. There are no intentional omissions.

## Repair

The tensor-Hom equivalence had already been constructed, but the public theorem hid it under
`Nonempty`. Added the named, directly usable
`Etingof.Problem2_14_3.tensorHomAdjunction`; the previous existence theorem remains as a
compatibility wrapper. This resolves the stale partial-coverage note and closed issue #6217.

## Validation

- standalone elaboration of all three providers
- scoped admission and project-axiom scan
- representative `#print axioms` audit
- full `EtingofRepresentationTheory.Chapter2` build
- all three repository metadata/dependency validators
- exact four-item claim-coverage audit, JSON parsing, and `git diff --check`

This PR is limited to Section 2.14 and Stage 3.2.

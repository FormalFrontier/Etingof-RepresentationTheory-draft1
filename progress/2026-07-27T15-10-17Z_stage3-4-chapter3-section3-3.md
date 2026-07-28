# Stage 3.4 dependency audit — Chapter 3 §3.3

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8064 at commit `240f796b`. It covers the
same seven reading-order items from `Chapter3/Introduction_to_3.3` through
`Chapter3/Remark3.3.4` and all four complete Lean provider files. The immediate predecessor is
`Chapter3/Theorem3.2.2`; the strict successor is `Chapter3/Introduction_to_3.4`.

No mathematical definition, theorem statement, or proof changed. This pass is limited to actual
backward dependency metadata and focused direct-import removal.

## Direct import audit

All four provider headers were checked with Mathlib's `#redundant_imports` analysis before and
after trimming. All four providers changed:

- `Theorem3_3_1.lean` removes five redundant Mathlib imports and retains four focused Mathlib
  imports plus the Proposition 3.1.4 project import;
- `Definition3_3_2.lean` removes two redundant Mathlib imports and retains two focused imports;
- `Problem3_3_3.lean` removes four redundant Mathlib imports and the documentation-only Theorem
  3.3.1 project import, retaining three focused Mathlib imports;
- `Remark3_3_4.lean` removes three redundant Mathlib imports and retains one focused import.

Direct imports move from 26 to 11, net `-15`. The final analysis reports no transitively redundant
import in any provider, and the four-provider ordinary build passes from the trimmed headers.

## Actual internal dependency graph

The seven conservative reading-order edges are replaced by five actual backward edges:

1. `Chapter3/Theorem3.3.1` → `Chapter3/Proposition3.1.4`, used by the exact final multiplicity
   decomposition;
2. the proof discussion → Proposition 3.1.4 and Theorem 3.3.1, whose implementation and endpoint
   it records;
3. Problem 3.3.3 → Theorem 3.3.1 for part (c)'s covered-elsewhere endpoint;
4. Remark 3.3.4 → Theorem 3.3.1 for the covered regular/free and final multiplicity
   decompositions.

The heading's formalized setup points forward to the following theorem item and is excluded from
the acyclic backward graph. The methodological transition and Definition 3.3.2 have no internal
project dependency. The proof discussion's Lean implementation constructs its transpose-twisted
dual directly and therefore does not import the separate Definition 3.3.2 provider.

Scoped graph edges move from 7 to 5, net `-2`. All five edges point strictly backward in catalog
order, and every tracker `actual_internal_dependencies` array agrees exactly with
`dependencies/internal.json`.

## Durable tracker result

- all 7 exact records have complete section `3.3` `stage3_4` objects;
- all 7 workflow statuses advance to `dependency_trimmed`;
- Stage 3.2 and Stage 3.3 metadata are unchanged;
- the non-§3.3 tracker projection, non-§3.3 dependency-source projection, and downstream incoming
  edges are unchanged from PR #8064.

## Validation

- final isolated build of all 4 scoped providers: success (1698 jobs; pre-existing linter warnings
  only);
- `lake build EtingofRepresentationTheory.Chapter3`: success (8692 jobs; pre-existing linter
  warnings only);
- initial and final all-provider `#redundant_imports` analysis: no remaining redundant imports;
- exact 7-item tracker/graph agreement and no-forward-edge checks: passed;
- direct-import count: 26 → 11 (`-15`); scoped graph edges: 7 → 5 (`-2`);
- `jq empty progress/items.json dependencies/internal.json`: passed;
- all four repository validators: passed;
- normalized scoped and non-scoped tracker/dependency invariance checks and `git diff --check`:
  passed.

This PR is limited to Chapter 3 §3.3 and Stage 3.4.

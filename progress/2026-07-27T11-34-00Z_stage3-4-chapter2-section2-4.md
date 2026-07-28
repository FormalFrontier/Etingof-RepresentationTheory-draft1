# Stage 3.4 dependency trimming — Chapter 2 §2.4

## Scope

This pass analyzes the actual internal dependencies of exactly
`Chapter2/Discussion_2.4_heading` and `Chapter2/Problem2.4.1` after their Stage 3.3 proofs were
verified.

## Actual dependencies

- `Chapter2/Discussion_2.4_heading` depends directly on `Chapter2/Definition2.3.4` because the
  left- and right-ideal bridges identify the relevant submodules with the project's
  `Etingof.Subrepresentation` abbreviation. The remaining ideal, span, kernel, and simple-ring
  declarations come directly from Mathlib and therefore do not create internal graph edges.
- `Chapter2/Problem2.4.1` has no internal dependency. Its Lean file imports Mathlib only: the left
  and right cases use `Ideal.exists_maximal`, and the two-sided case supplies its own Zorn
  argument.

The conservative linear-chain edges (`Problem2.3.18` for the discussion and the discussion for
the problem) were therefore replaced with these actual dependencies in
`dependencies/internal.json`.

Both items now carry durable `stage3_4` records and move to `dependency_trimmed`.

## Validation

- every new internal target exists in the root item catalog
- `jq empty dependencies/internal.json progress/items.json`
- `git diff --check`

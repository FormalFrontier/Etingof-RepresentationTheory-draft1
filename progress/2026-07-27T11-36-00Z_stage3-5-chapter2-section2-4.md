# Stage 3.5 Mathlib-quality polish — Chapter 2 §2.4

## Scope

This pass reviews exactly the §2.4 files
`Discussion_2_4_heading.lean` and `Problem2_4_1.lean` after dependency trimming.

## Review

The section was checked against the Stage 3.5 criteria:

- The discussion declarations are direct abbreviations for Mathlib structures or short bridge
  theorems whose names expose the book/Mathlib correspondence.
- Imports are focused on subrepresentations, simple rings, kernels, and two-sided span operations.
- The generated-ideal statements reuse Mathlib's universal properties instead of duplicating
  proofs.
- The maximal-left/right proofs delegate directly to `Ideal.exists_maximal`.
- The two-sided proof isolates the only nontrivial ingredient—the chain-union upper bound—before
  applying Zorn, and uses explicit simp sets rather than broad cleanup tactics.
- There are no redundant local helper declarations, unused simp arguments, deprecated tactics,
  flexible `simp at`, or style warnings in either scoped file.

No source rewrite was justified: shortening the explicit Zorn construction would hide the missing
two-sided Mathlib API rather than improve readability. Both items therefore advance from
`dependency_trimmed` to `proof_polished`, with durable `stage3_5` review records.

## Validation

- `lake env lean EtingofRepresentationTheory/Chapter2/Discussion_2_4_heading.lean`
- `lake env lean EtingofRepresentationTheory/Chapter2/Problem2_4_1.lean`
- `lake build EtingofRepresentationTheory.Chapter2`
- `jq empty progress/items.json`
- `git diff --check`

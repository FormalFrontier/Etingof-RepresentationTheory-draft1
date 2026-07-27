# Stage 3.4 dependency audit — Chapter 2 §2.10

## Scope

This review is stacked on the complete Stage 3.3 audit in PR #8026 and covers exactly the two
reading-order items between `Chapter2/Discussion_2.9_Lie_groups` and
`Chapter2/Discussion_2.11_heading`:

1. `Chapter2/Discussion_2.10_heading` (fourteen audited claim units);
2. `Chapter2/Discussion_2.10_continued` (one audited claim unit).

The section has zero Lean provider files. All fifteen inherited Stage 3.2 claims are
`non_formalizable`, and Stage 3.3 consequently found zero declarations and zero proof obligations.

## Actual dependency graph

Both items have `actual_internal_dependencies = []`. The first item's conservative link to the
preceding §2.9 item was merely reading order. The continuation's link to the heading represented a
paragraph split across a page boundary, not a Lean import, declaration use, or mathematical proof
dependency. Neither item has a Lean provider, declaration, or proof term from which a real project
edge could arise.

The two synthetic source edges are therefore removed from `dependencies/internal.json`. The two
keys remain present with empty arrays, preserving complete graph coverage. No non-scoped source
record and no downstream incoming edge is changed.

## Durable tracker result

- both exact items have complete section `2.10` `stage3_4` records;
- both record `actual_internal_dependencies = []` with explicit not-applicable rationales tied to
  all fourteen-plus-one non-formalizable claims;
- both workflow statuses advance to `dependency_trimmed`;
- Stage 3.2 and Stage 3.3 records remain unchanged.

## Validation

- exact two-item Stage 3.4 completeness and zero-dependency check: passed;
- exact Chapter 2 provider search: zero files;
- non-§2.10 tracker and dependency-source projections unchanged from PR #8026;
- scoped Stage 3.2/3.3 projections unchanged;
- `jq empty progress/items.json dependencies/internal.json`: passed;
- `python3 scripts/validate_items.py`: passed with full 5721/5721-line coverage (and replayed
  593 pre-existing extra-field warnings);
- `python3 scripts/validate_dependencies.py`: passed with all 583 entries, 580 edges, and the one
  expected warning for intentionally trimming the conservative default;
- `lake build EtingofRepresentationTheory.Chapter2`: passed (8744 jobs; warnings are in
  pre-existing non-scoped files);
- `git diff --check`: passed.

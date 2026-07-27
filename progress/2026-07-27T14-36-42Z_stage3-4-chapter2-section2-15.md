# Stage 3.4 dependency trimming — Chapter 2 §2.15

## Scope

This pass analyzes the exact two §2.15 catalog items after Stage 3.3: the section heading and
Problem 2.15.1. The exercise is implemented across twelve provider modules.

## Internal dependency result

The organizational heading has no mathematical dependency. Problem 2.15.1 directly uses two
earlier book items:

- `Chapter2/Theorem2.1.1`, for the classification and complete-reducibility results reused by
  the exercise providers;
- `Chapter2/Discussion_concrete_Lie_examples`, for the concrete definition and standard relations
  of `sl(2)` represented by the shared `Sl2Defs` provider.

All other project imports connect providers belonging to Problem 2.15.1 itself. The conservative
reading-order edges were replaced by these actual backward-only dependencies in
`dependencies/internal.json`.

## Import trimming

Mathlib's `#redundant_imports` diagnostic was run by direct elaboration in every one of the twelve
provider modules. Four headers were already transitively irredundant. Eight headers had a total of
45 redundant imports, all of which were removed; the twelve headers now contain 21 imports in
total. No umbrella `import Mathlib` remains in scope, and every edited provider elaborates directly
with the reduced header.

Both scoped items now carry complete `stage3_4` records and have status `dependency_trimmed`.

## Validation

- fresh isolated `.lake/build` baseline build of all twelve providers
- `#redundant_imports` on all twelve provider modules
- direct elaboration of all twelve providers after trimming
- scoped provider build and full `EtingofRepresentationTheory.Chapter2` build
- `scripts/validate_items.py`
- `scripts/validate_dependencies.py`
- `scripts/validate_external_deps.py`
- `scripts/validate_mathlib_coverage.py`
- exact two-item scope, graph, and tracker-invariance checks
- `jq empty dependencies/internal.json progress/items.json`
- `git diff --check`

`scripts/verify_blobs.py` still encounters the repository's pre-existing derived-overlay entries
without an `id`; this pass does not alter blobs or those unrelated records.

# Stage 3.4 dependency trimming: Chapter 2 §2.13

## Scope

This pass analyzes the actual dependencies of the two §2.13 catalog items after Stage 3.3:
`Discussion_2.13_heading` and `Problem2.13.1`.

## Result

Both items are independent of earlier project items. The section heading is organizational only,
and the formalized irrationality proof uses Mathlib directly. The two conservative reading-order
edges were therefore removed from `dependencies/internal.json`.

The proof provider no longer imports the `Mathlib` umbrella. It now imports only two focused
modules: the inverse-trigonometric and irrational-number APIs. Both scoped items carry complete
`stage3_4` records and move to `dependency_trimmed`.

The five geometric claims intentionally omitted under `skipped-exercises.md` remain explicit
scope decisions and introduce no dependency edges.

## Validation

- direct compilation of `Problem2_13_1.lean`
- Mathlib's `#import_bumps`/`minImports` linter (no unneeded import remains)
- full `EtingofRepresentationTheory.Chapter2` build
- `scripts/validate_items.py`
- `scripts/validate_dependencies.py`
- `scripts/validate_external_deps.py`
- exact two-item §2.13 metadata audit
- `jq empty dependencies/internal.json progress/items.json`
- `git diff --check`

This PR is limited to Section 2.13 and Stage 3.4.

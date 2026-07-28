# Stage 3.4 dependency trimming — Chapter 2 §2.14

## Scope

This pass analyzes the actual dependencies of the exact four §2.14 catalog items after Stage 3.3:
the section heading, both definitions, and Problem 2.14.3.

## Result

All four scoped items are independent of earlier project items. The heading is organizational;
the three mathematical providers construct the tensor-product representation, dual
representation, and tensor–Hom adjunction directly from Mathlib APIs. The four conservative
reading-order edges were therefore removed from `dependencies/internal.json`.

The two definition providers already had irredundant focused imports. The problem provider no
longer imports the `Mathlib` umbrella: it now uses the six focused modules reported by Mathlib's
`#min_imports` command, and `#redundant_imports` confirms that none is transitively redundant.
All four items carry complete `stage3_4` records and move to `dependency_trimmed`.

## Validation

- direct compilation of all three providers
- Mathlib's `#redundant_imports` and `#min_imports` diagnostics
- full `EtingofRepresentationTheory.Chapter2` build
- `scripts/validate_items.py`
- `scripts/validate_dependencies.py`
- `scripts/validate_external_deps.py`
- exact four-item §2.14 graph/tracker audit
- `jq empty dependencies/internal.json progress/items.json`
- `git diff --check`

This PR is limited to Section 2.14 and Stage 3.4.

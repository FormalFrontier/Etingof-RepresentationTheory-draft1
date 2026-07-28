# Stage 3.4 dependency trimming — Chapter 3 §3.2

## Scope

This pass analyzes the actual dependencies and direct imports of the exact three §3.2 catalog
items after Stage 3.3: the section heading, Corollary 3.2.1, and Theorem 3.2.2.

## Result

All three backward pedagogical dependency sets are empty. The heading is organizational. Both
density proofs use Mathlib APIs directly and import no project item. The interpolation corollary
imports the later Theorem 3.2.2 provider because Lean proves density first and derives the
corollary afterward. That forward implementation import cannot be represented in the acyclic
backward book-order graph; it is a documented proof-order choice, not a hidden dependency on an
earlier catalog item. The three conservative reading-order edges were removed accordingly.

The theorem provider now has the single focused Mathlib import reported by `#min_imports`; two
redundant direct imports were removed. The corollary provider now imports only the theorem
provider; two redundant Mathlib imports were removed. Final `#redundant_imports` checks report no
transitively redundant import in either provider.

All three items carry complete `stage3_4` records and move to `dependency_trimmed`.

## Validation

- direct compilation of both providers
- Mathlib's `#redundant_imports` and `#min_imports` diagnostics
- full `EtingofRepresentationTheory.Chapter3` build
- `scripts/validate_items.py`
- `scripts/validate_dependencies.py`
- `scripts/validate_external_deps.py`
- exact three-item §3.2 graph/tracker audit
- `jq empty dependencies/internal.json progress/items.json`
- `git diff --check`

This PR is limited to Section 3.2 and Stage 3.4.

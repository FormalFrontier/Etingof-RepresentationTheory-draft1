# Stage 3.4 dependency trimming — Chapter 2 §2.16

## Scope

This pass analyzes the exact six §2.16 catalog items after Stage 3.3: the section heading and
Problems 2.16.1–2.16.5. The exercises are implemented across sixteen direct provider modules,
including the twelve-file development for Problem 2.16.3.

## Internal dependency result

The organizational heading has no mathematical dependency. Each exercise is developed directly
from Mathlib: Problems 2.16.1, 2.16.2, 2.16.4, and 2.16.5 import no project module, while every
project import in the Problem 2.16.3 development connects providers belonging to that same catalog
item. Consequently, all six actual backward internal dependency lists are empty. The six
conservative reading-order edges were removed from `dependencies/internal.json`.

The three deferred classification objects for Problem 2.16.4 and the two permanent classification
omissions for Problem 2.16.5 remain unchanged.

## Import trimming

Mathlib's cumulative `minImports` linter and the exact engine behind `#redundant_imports` were run
provider by provider across all sixteen modules. Three umbrella `import Mathlib` headers were
replaced by focused imports. Seventeen redundant imports were removed from five other headers, and
one focused `Mathlib.Tactic.FieldSimp` import was added directly to the layer provider that uses the
tactic instead of relying on the main Problem 2.16.3 provider's former transitive closure. The
final sixteen headers have no structurally redundant direct imports.

The cumulative linter's declaration-by-declaration instrumentation perturbs two existing tactic
proofs in Problem 2.16.2 and Problem2_16_3_Grading; ordinary direct elaboration succeeds, and neither
instrumented run reports an unneeded final import. All other instrumented provider runs complete
without an unneeded-import warning.

All six scoped items now carry complete `stage3_4` records and have status
`dependency_trimmed`.

## Validation

- fresh isolated `.lake/build` baseline and post-trim builds of all sixteen providers
- cumulative `minImports` and exact structural redundant-import analysis for all sixteen providers
- direct elaboration of all sixteen providers after trimming
- full `EtingofRepresentationTheory.Chapter2` build
- `scripts/validate_items.py`
- `scripts/validate_dependencies.py`
- `scripts/validate_external_deps.py`
- `scripts/validate_mathlib_coverage.py`
- exact six-item scope, omission, graph, provider-body, and non-scope invariance checks
- `jq empty dependencies/internal.json progress/items.json`
- `git diff --check`

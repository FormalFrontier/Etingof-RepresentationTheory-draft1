# Internal dependencies

`internal.json` is the validated direct-dependency graph for the 583-item book
ledger. It began as the Stage 2.1 conservative all-predecessors graph and is
progressively replaced by actual dependencies during Stage 3.4.

## Current state

| Metric | Value |
|---|---:|
| Items | 583 |
| Recorded direct edges | 512 |
| Conservative baseline edges removed | 169,141 |
| Items with no internal dependency | 91 |
| Largest recorded direct dependency set | 4 |
| Items through Stage 3.4 | 147 |
| Items through Stage 3.5 | 129 |

The graph is intentionally mixed-state while the post-formalization quality
workflow continues. Reviewed items record their actual semantic dependencies;
unreviewed later sections generally retain the conservative immediate-predecessor
edge. `progress/items.json` records the item-level Stage 3.4 evidence where that
review is complete.

This dependency workflow is separate from mathematical completion. The latter is
defined by the zero-placeholder and reconciled exercise-coverage gates documented
in the root README.

## Validation

```bash
python3 scripts/validate_dependencies.py
```

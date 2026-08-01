# Internal dependencies

`internal.json` is the validated direct-dependency graph for the 583-item book
ledger. It began as the Stage 2.1 conservative all-predecessors graph and is
progressively replaced by actual dependencies during Stage 3.4.

## Current state

| Metric | Value |
|---|---:|
| Items | 583 |
| Recorded direct proof-term edges | 583 |
| Conservative all-predecessors edges removed | 169,197 |
| Items with no internal dependency | 385 |
| Largest recorded direct dependency set | 16 |
| Items through Stage 3.4 | 583 partition + 10 derived |
| Provider-backed records through Stage 3.5 | 403 partition + 10 derived |

The graph is the completed, acyclic projection of direct kernel constants from
declaration types and theorem/opaque bodies. The immutable 521-edge import-DAG
input is `import-dag-stage3-4-baseline.json`. Re-export hubs are expanded to their
implementation modules under a deterministic single-owner attribution. Stage 3.4
trimmed 133 import edges not recovered through the owned-module kernel mapping
and found 203 proof-supported
associations beyond the import baseline. Item coarsening creates six cyclic
components; `internal.json` contains the maximal deterministic acyclic subset,
while all eight excluded edges and their cycle paths remain explicit in
`progress/reviews/2026-08-01-stage3-4-proof-terms.json`.

Root-imported modules without an unambiguous item owner remain in the declaration
inventory and source-hash audit but are deliberately omitted from the item-level
projection; the certificate lists them under `modules_without_item_owner`.

This dependency workflow is separate from mathematical completion. The latter is
defined by the zero-placeholder and reconciled exercise-coverage gates documented
in the root README.

## Validation

```bash
python3 scripts/validate_dependencies.py
```

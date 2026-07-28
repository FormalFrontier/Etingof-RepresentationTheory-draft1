# Stage 3.4 dependency audit — Chapter 3 §3.1

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8058 at commit `9c241a2f`. It covers the
same ten reading-order items from `Chapter3/Introduction` through
`Chapter3/Discussion_after_Lemma3.1.6` and all seven complete Lean provider files. The immediate
predecessor is `Chapter2/Problem2.16.5`; the strict successor is
`Chapter3/Introduction_to_3.2`.

No mathematical definition, theorem statement, or proof changed. This pass is limited to actual
backward dependency metadata and focused direct-import removal.

## Direct import audit

All 60 public declarations across the seven providers were checked with declaration-level
`#min_imports`, and all seven complete provider headers were checked with `#redundant_imports`.
Five providers changed:

- `Example3_1_2.lean` removes redundant `Mathlib.LinearAlgebra.Basis.VectorSpace`;
- `Remark3_1_3.lean` removes redundant `TensorProduct.Basic`, `Dimension.Free`, and
  `LinearIndependent.Lemmas` imports;
- `Proposition3_1_4.lean` removes redundant `DirectSum.Module`, `Module.Opposite`,
  `Data.Matrix.Basic`, and `LinearIndependent.Defs` imports;
- `Remark3_1_5.lean` removes redundant `SimpleModule.Basic` and `Matrix.ToLin`, leaving its
  Proposition 3.1.4 project import;
- `Lemma3_1_6.lean` removes redundant `Order.Zorn`, `Order.Minimal`, and `DirectSum.Module`,
  leaving one focused simple-module import.

`Definition3_1_1.lean` and the alternative-proof provider were already clean. Direct imports move
from 25 to 12, net `-13`. A final full-scope `#redundant_imports` pass reports no transitively
redundant import in any provider.

## Actual internal dependency graph

The ten conservative reading-order edges are replaced by seven actual backward edges:

1. `Chapter3/Remark3.1.3` → `Chapter2/Corollary2.3.10`, used for the scalar-endomorphism form of
   Schur's lemma;
2. `Chapter3/Remark3.1.5` → `Chapter3/Proposition3.1.4`, whose decomposition and block-matrix
   theorems it generalizes;
3. `Chapter3/Discussion_alternative_proof_of_Proposition3.1.4` → `Chapter3/Remark3.1.3`, whose
   canonical evaluation equivalence it transports along;
4. the final discussion → Proposition 3.1.4, Remark 3.1.5, the alternative-proof discussion, and
   Lemma 3.1.6, exactly matching its four `covered_elsewhere` claim sources.

The remaining six items use only Mathlib or are non-proof-bearing prose. Scoped graph edges move
from 10 to 7, net `-3`. All seven edges point strictly backward in catalog order, and every tracker
`actual_internal_dependencies` array agrees exactly with `dependencies/internal.json`.

## Durable tracker result

- all 10 exact records have complete section `3.1` `stage3_4` objects;
- all 10 workflow statuses advance to `dependency_trimmed`;
- Stage 3.2 and Stage 3.3 metadata are unchanged;
- the non-§3.1 tracker projection, non-§3.1 dependency-source projection, and all downstream
  incoming edges are unchanged from PR #8058.

## Validation

- final isolated build of all 7 scoped providers: success (1977 jobs; pre-existing linter warnings
  only);
- `lake build EtingofRepresentationTheory.Chapter3`: success (8693 jobs; pre-existing linter
  warnings only);
- declaration-level `#min_imports` checks for all 60 public declarations: complete;
- initial and final all-provider `#redundant_imports` checks: clean after trimming;
- exact 10-item tracker/graph agreement and no-forward-edge checks: passed;
- direct-import count: 25 → 12 (`-13`); scoped graph edges: 10 → 7 (`-3`);
- `jq empty progress/items.json dependencies/internal.json`: passed;
- `python3 scripts/validate_items.py`: passed with 5721/5721-line coverage (593 pre-existing schema
  warnings);
- `python3 scripts/validate_dependencies.py`: passed with 583 entries and 579 total edges (one
  pre-existing conservative-default warning);
- `python3 scripts/validate_external_deps.py`: passed;
- `python3 scripts/validate_mathlib_coverage.py`: passed;
- normalized scoped and non-scoped tracker/dependency invariance checks and `git diff --check`:
  passed.

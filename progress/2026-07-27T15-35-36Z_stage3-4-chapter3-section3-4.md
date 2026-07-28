# Stage 3.4 dependency audit — Chapter 3 §3.4

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8071 at commit `0399da14`. It covers the
same three reading-order items from `Chapter3/Introduction_to_3.4` through
`Chapter3/Lemma3.4.2` and both complete Lean provider files. The immediate predecessor is
`Chapter3/Remark3.3.4`; the strict successor is `Chapter3/Introduction_to_3.5`.

No mathematical definition, theorem statement, or proof changed. This pass is limited to actual
backward dependency metadata and focused direct-import minimization.

## Direct import audit

All three authored declarations across the two providers were checked with declaration-level
`#min_imports`, and both complete provider headers were checked with `#redundant_imports`.

- `Definition3_4_1.lean` retains `Mathlib.Order.RelSeries` for the finite strict chain and replaces
  the broader `Mathlib.LinearAlgebra.Span.Basic` import with the reported minimal
  `Mathlib.Algebra.Module.Submodule.Lattice` import for the submodule lattice and its bounds;
- `Lemma3_4_2.lean` removes the transitively redundant `SimpleModule.Basic`, `JordanHolder`, and
  `Artinian.Module` imports. Its two theorems require exactly `FiniteLength`,
  `FiniteDimensional.Defs`, and the local `Definition3_4_1` provider.

Direct imports move from eight to five, net `-3`. A final complete-provider
`#redundant_imports` pass reports no transitively redundant import in either provider.

## Actual internal dependency graph

The three conservative reading-order edges are replaced by one actual backward edge:

1. `Chapter3/Lemma3.4.2` → `Chapter3/Definition3.4.1`, because the exact theorem explicitly
   constructs and returns `Etingof.Filtration`.

The section introduction is organizational prose without a provider, and the definition provider
uses only Mathlib. The helper composition-series theorem is defined in the same tracked lemma item.
Scoped graph edges move from three to one, net `-2`. The retained edge points strictly backward in
catalog order, and every tracker `actual_internal_dependencies` array agrees exactly with
`dependencies/internal.json`.

## Durable tracker result

- all three exact records have complete section `3.4` `stage3_4` objects;
- all three workflow statuses advance to `dependency_trimmed`;
- Stage 3.2, Stage 3.3, claim-coverage, and fidelity metadata are unchanged;
- the non-§3.4 tracker projection, non-§3.4 dependency-source projection, and all downstream
  incoming edges are unchanged from PR #8071.

## Validation

- final isolated build of both scoped providers: success (1,581 jobs);
- `lake build EtingofRepresentationTheory.Chapter3`: success (8,692 jobs; pre-existing linter
  warnings only);
- declaration-level `#min_imports` checks for all three authored declarations: complete;
- initial and final all-provider `#redundant_imports` checks: clean after trimming;
- exact three-item tracker/graph agreement and no-forward-edge checks: passed;
- direct-import count: 8 → 5 (`-3`); scoped graph edges: 3 → 1 (`-2`);
- `jq empty progress/items.json dependencies/internal.json`: passed;
- `python3 scripts/validate_items.py`: passed with 5721/5721-line coverage (593 pre-existing schema
  warnings);
- dependency, external-dependency, and Mathlib-coverage validators: passed;
- normalized scoped and non-scoped tracker/dependency invariance checks and `git diff --check`:
  passed.

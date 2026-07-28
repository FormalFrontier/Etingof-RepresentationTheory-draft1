# Stage 3.4 dependency audit — Chapter 3 §3.7

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8082 at commit
`ac82f667a20b848765aaeb51528d6ec7c2a78c01`. It covers the same three reading-order items
at indices 159–161 and the three exact providers for the Jordan-Holder theorem, its footnote,
and the following length discussion. The immediate predecessor is `Chapter3/Theorem3.6.2`; the
strict successor is `Chapter3/Introduction_to_3.8`.

No definition, theorem statement, proof body, or inherited Stage 3.2/3.3 metadata changed. This
pass is limited to verified direct-import removal, actual internal dependency edges, and durable
`stage3_4` records.

## Direct-import audit

An initial complete-provider `#redundant_imports` pass reported exactly three transitively
redundant imports:

- `Theorem3_7_1.lean`: `Mathlib.Order.JordanHolder`, already supplied by
  `Mathlib.RingTheory.SimpleModule.Basic`;
- `Discussion_footnote_3_7_1.lean`: `Mathlib.LinearAlgebra.Pi` and
  `Mathlib.Algebra.CharP.Defs`, both already supplied through the retained local
  `Theorem3_6_2` import;
- `Discussion_after_Theorem3_7_1.lean`: no redundant direct import.

Only those three reported lines were removed. Direct imports move from six to three (`-3`). A
final complete-provider `#redundant_imports` run reports “No transitively redundant imports
found” independently for all three providers. Removing import lines from both the base and final
sources makes every provider body byte-for-byte identical, so no mathematical content changed.

## Actual internal dependency graph

The three conservative reading-order edges are replaced by one actual backward edge:

1. `Chapter3/Theorem3.7.1` → `Chapter3/Introduction_to_3.6`, because the theorem item's
   characteristic-`p` footnote uses `Etingof.character`, the declaration cataloged under the
   Section 3.6 introduction. The footnote obtains it through its sole retained project import,
   `Theorem3_6_2.lean`.

The §3.7 introduction has no provider, while both the Jordan-Holder provider and the length
discussion provider use only Mathlib. Scoped graph edges therefore move from three to one
(`-2`), and the repository total moves from 582 to 580. The retained edge points strictly
backward, and every tracker `actual_internal_dependencies` array agrees exactly with
`dependencies/internal.json`.

## Durable tracker result

- all three exact records have complete section `3.7` `stage3_4` objects;
- prior workflow statuses and all Stage 3.2/3.3, claim-coverage, fidelity, and proof-integrity
  metadata are unchanged;
- the normalized non-§3.7 tracker projection and non-§3.7 dependency-source projection are
  unchanged;
- external-dependency and Mathlib-coverage maps are unchanged.

## Validation

- final isolated build of all three scoped providers: success (1,960 jobs);
- `lake build EtingofRepresentationTheory.Chapter3`: success (8,692 jobs; pre-existing warnings);
- initial and final complete-provider `#redundant_imports` checks: all providers clean after the
  three verified removals;
- exact three-item tracker/graph agreement and backward-edge checks: passed;
- direct-import count: 6 → 3 (`-3`); scoped graph edges: 3 → 1 (`-2`);
- `jq empty progress/items.json dependencies/internal.json`: passed;
- item, dependency, external-dependency, and Mathlib-coverage validators: passed;
- scoped/non-scoped tracker and dependency invariance checks, provider-body invariance, and
  `git diff --check`: passed.

This PR is limited to Chapter 3 §3.7 and Stage 3.4.

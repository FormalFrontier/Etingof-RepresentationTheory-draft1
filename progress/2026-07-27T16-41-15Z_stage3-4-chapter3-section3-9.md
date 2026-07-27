# Stage 3.4 dependency audit — Chapter 3 §3.9

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8091 at commit
`26a894f7482c0489a7a8b6cb41c80fd6474a4e96`. It covers the same six catalog
items at indices 170–175 and all seven exact providers. The immediate
predecessor is `Chapter3/Remark3.8.6`; the strict successor is
`Chapter3/Introduction_to_3.10`.

No definition, theorem statement, proof body, or inherited Stage 3.2/3.3
metadata changes. This pass is limited to verified direct-import removal,
declaration-backed internal item edges, and durable `stage3_4` records.

## Direct-import audit

The seven providers initially contained 68 direct-import lines. A complete
provider `#redundant_imports` pass identified 40 removable lines. After those
removals, every surviving direct import was deletion-tested by re-elaborating
the complete provider with that one line absent. This found one additional
unused import not reported by the transitive check:
`EtingofRepresentationTheory.Chapter2.Theorem2_1_2_General` in
`Problem3_9_3_TwoDim.lean`.

The final import counts are:

| Provider | Before | After | Removed |
|---|---:|---:|---:|
| `Problem3_9_1` | 8 | 1 | 7 |
| `Problem3_9_2` | 15 | 6 | 9 |
| `Problem3_9_2_Classification` | 5 | 2 | 3 |
| `Problem3_9_3` | 3 | 2 | 1 |
| `Problem3_9_3_TwoDim` | 3 | 1 | 2 |
| `Problem3_9_4` | 6 | 4 | 2 |
| `Problem3_9_5` | 28 | 11 | 17 |
| **Total** | **68** | **27** | **41** |

All 27 remaining imports fail the single-import deletion test. A final complete
provider `#redundant_imports` pass independently reports “No transitively
redundant imports found” for all seven providers. Removing import lines from
both the base and final sources makes every provider body byte-for-byte
identical, so no mathematical content changed.

## Actual internal dependency graph

The six conservative reading-order edges are replaced by five declaration-backed
backward edges:

| Item | Actual internal dependencies |
|---|---|
| `Chapter3/Introduction_to_3.9` | none |
| `Chapter3/Problem3.9.1` | `Chapter2/Corollary2.3.10` |
| `Chapter3/Problem3.9.2` | `Chapter2/Definition2.3.8`; `Chapter3/Problem3.9.1` |
| `Chapter3/Problem3.9.3` | `Chapter2/Theorem2.1.2` |
| `Chapter3/Problem3.9.4` | `Chapter3/Problem3.9.1` |
| `Chapter3/Problem3.9.5` | none |

Problem 3.9.1 uses the Schur lemma for its irreducible extension
classification. Problem 3.9.2 uses the earlier Ext-one framework and the
project's indecomposability predicate. Problem 3.9.3 uses the quiver-equivalence
API, and Problem 3.9.4 uses the Ext-one/coboundary framework. Problem 3.9.5 is
self-contained over Mathlib.

The core Problem 3.9.3 provider also imports `Chapter6.Problem6_9_3` for shared
`simpleRep`, `dimVec`, and Ext infrastructure used to implement the claims of
Problem 3.9.3 itself. This physical implementation-provider reuse is recorded
explicitly but is not represented as a forward book-item edge: adding the later
Problem 6.9.3 catalog item as a prerequisite of Problem 3.9.3 would make the
reading-order dependency graph cyclic. It is analogous to a same-item helper
provider, rather than a mathematical dependence on the later problem's result.

Scoped graph edges therefore move from six to five, and the repository total
moves from 582 to 581. Every scoped `stage3_4.actual_internal_dependencies`
array agrees exactly with `dependencies/internal.json`, and all represented
edges point strictly backward.

## Validation

- final isolated build of all seven providers: success (8,637 jobs);
- initial and final complete-provider `#redundant_imports` checks: all providers
  clean after the 41 verified removals;
- single-import deletion tests: all 27 final imports required;
- direct-import count: 68 → 27 (`-41`); scoped graph edges: 6 → 5 (`-1`);
- full `lake build EtingofRepresentationTheory.Chapter3`: success (8,691 jobs;
  pre-existing warnings only);
- all four repository validators: pass (583 items and 581 dependency edges);
- strict graph/tracker/provider-body/nonscope invariance, represented-edge
  backwardness, JSON validation, and `git diff --check`: pass.

This PR is limited to Chapter 3 §3.9 and Stage 3.4.

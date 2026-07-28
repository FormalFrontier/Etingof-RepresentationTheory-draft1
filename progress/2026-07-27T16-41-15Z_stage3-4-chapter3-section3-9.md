# Stage 3.4 dependency audit — Chapter 3 §3.9

## Scope

The original Stage 3.4 review was stacked on the Stage 3.3 draft provenance
from PR #8091 at commit `26a894f7482c0489a7a8b6cb41c80fd6474a4e96`.
This permanent report was later reconciled with #8101/#8104 and the integrated
§3.9 merge `2725e8a886b888938503b93a064ab2fd82ad184d`. It covers the same six
catalog items at indices 170–175 and all ten current exact providers. The
immediate predecessor is `Chapter3/Remark3.8.6`; the strict successor is
`Chapter3/Introduction_to_3.10`.

No definition, theorem statement, or proof body changes. This integration pass
refreshes inherited Stage 3.2/3.3 metadata made stale by #8101/#8104 and is
otherwise limited to verified direct-import removal, declaration-backed
internal item edges, and durable `stage3_4` records.

## Direct-import audit

The ten providers initially contained 79 direct-import lines after #8101 and #8104. A complete
provider `#redundant_imports` pass identified 45 removable lines. After those
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
| `Problem3_9_4` | 7 | 4 | 3 |
| `Problem3_9_5` | 28 | 11 | 17 |
| `Problem3_9_5_Spinor` | 4 | 2 | 2 |
| `Problem3_9_5_Spinor_Transport` | 3 | 2 | 1 |
| `Problem3_9_5_Spinor_Odd` | 3 | 2 | 1 |
| **Total** | **79** | **33** | **46** |

An integration cross-check tentatively proposed removing
`Mathlib.LinearAlgebra.QuadraticForm.Dual` from `Problem3_9_5_Spinor`, but a
clean-source rebuild invalidated that result: `QuadraticForm.dualProd`,
`LinearMap.dualProd`, and `LinearMap.separatingLeft_dualProd` became unknown.
The import was restored, and its omission then failed in the final deletion
matrix. Thus 33, not 32, is the buildable fixed point.

All 33 remaining imports fail the single-import deletion test. A final complete
provider `#redundant_imports` pass independently reports “No transitively
redundant imports found” for all ten providers. For `Problem3_9_4`, the
four survivors are exactly `Problem3_9_1`, `Mathlib.Algebra.DualNumber`,
`Mathlib.RingTheory.PowerSeries.NoZeroDivisors`, and
`Mathlib.Tactic.NoncommRing`. Removing import lines from
both the base and final sources makes every provider body byte-for-byte
identical, so no mathematical content changed.

## Actual internal dependency graph

The six conservative reading-order edges are replaced by six declaration-backed
backward edges:

| Item | Actual internal dependencies |
|---|---|
| `Chapter3/Introduction_to_3.9` | none |
| `Chapter3/Problem3.9.1` | `Chapter2/Corollary2.3.10` |
| `Chapter3/Problem3.9.2` | `Chapter2/Definition2.3.8`; `Chapter3/Problem3.9.1` |
| `Chapter3/Problem3.9.3` | `Chapter2/Theorem2.1.2` |
| `Chapter3/Problem3.9.4` | `Chapter3/Problem3.9.1` |
| `Chapter3/Problem3.9.5` | `Chapter3/Theorem3.3.1` |

Problem 3.9.1 uses the Schur lemma for its irreducible extension
classification. Problem 3.9.2 uses the earlier Ext-one framework and the
project's indecomposability predicate. Problem 3.9.3 uses the quiver-equivalence
API, and Problem 3.9.4 uses the Ext-one/coboundary framework. Problem 3.9.5
uses Mathlib plus same-item imports among its four provider files, which do not
add catalog dependencies, and the odd-dimensional continuation uses Theorem
3.3.1.

The core Problem 3.9.3 provider also imports `Chapter6.Problem6_9_3` for shared
`simpleRep`, `dimVec`, and Ext infrastructure used to implement the claims of
Problem 3.9.3 itself. This physical implementation-provider reuse is recorded
explicitly but is not represented as a forward book-item edge: adding the later
Problem 6.9.3 catalog item as a prerequisite of Problem 3.9.3 would make the
reading-order dependency graph cyclic. It is analogous to a same-item helper
provider, rather than a mathematical dependence on the later problem's result.

Scoped graph edges remain at six, and on the exact integrated base the
repository total remains 512. Every scoped `stage3_4.actual_internal_dependencies`
array agrees exactly with `dependencies/internal.json`, and all represented
edges point strictly backward.

## Validation

- final isolated build of all ten providers: success;
- initial and final complete-provider `#redundant_imports` checks: all providers
  clean after the 46 verified removals;
- single-import deletion tests: all 33 final imports required;
- direct-import count: 79 → 33 (`-46`); scoped graph edges: 6 → 6 (`0`);
- focused build of all ten exact providers: success (8,642 jobs), with no new
  warnings at the warning gate;
- full `lake build EtingofRepresentationTheory.Chapter3`: success (8,695 jobs;
  pre-existing warnings only);
- CI-equivalent build of 818 target modules: success (9,400 jobs), with no new
  warnings at its warning gate;
- all four repository validators: pass (583 items and 512 dependency edges);
- strict graph/tracker/provider-body/nonscope invariance, represented-edge
  backwardness, JSON validation, and `git diff --check`: pass.

The organizational heading now has canonical top-level status
`non_formalizable`; all five problem items have canonical top-level status
`dependency_trimmed`. This reconciled audit is limited to Chapter 3 §3.9 and
Stage 3.4.

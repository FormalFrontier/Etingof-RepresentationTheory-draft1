# Stage 3.4 dependency audit — Chapter 3 §3.8

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8090 at commit
`4111d2c80cb486353e6ef482616303ed680daec1`. It covers the same eight
reading-order records at indices 162–169 and all thirteen exact providers. The
strict predecessor is `Chapter3/Discussion_after_Theorem3.7.1`; the strict
successor is `Chapter3/Introduction_to_3.9`.

No definition, theorem statement, proof body, or inherited Stage 3.2/3.3
metadata changed. This pass is limited to a proven direct-import removal,
actual internal dependency edges, and durable `stage3_4` records.

## Independent direct-import tests

The thirteen providers initially contain 57 direct import statements. Every
line was tested independently by omitting only that line and re-elaborating the
complete provider with `lake env lean /dev/stdin`. The result is exact:

- 56 omissions fail elaboration, so those imports are retained;
- one omission succeeds:
  `Problem3_8_4.lean` does not need its direct import of `Problem3_8_3`.

Only that proven-redundant line was removed, taking the direct-import count from
57 to 56. The base setup provider still requires its `Mathlib` import. The
separate cancellation provider still requires `Problem3_8_3` for the arbitrary-
field Krull–Schmidt results, so the cross-item dependency remains represented
at the Problem 3.8.4 item.

Removing import lines from the base and final versions makes every provider
body byte-for-byte identical. Thus the edit changes neither mathematical
content nor any declaration body.

## Exact provider graph

After trimming, the providers have 17 retained direct project-import edges.
They split into:

- seven backward cross-item edges represented in the tracker graph;
- nine intra-item edges connecting the eight-file Problem 3.8.4 implementation;
- one forward implementation edge from `Theorem3_8_1` to the later
  `Lemma3_8_2` provider.

The Problem 3.8.4 intra-item chain is exact: cancellation imports Problem 3.8.3;
descent imports functoriality; finite imports power and cancellation; general
imports finite, functoriality, and descent; main imports finite and descent; and
power imports the base setup provider. The base setup and functoriality
providers import no project module.

The theorem-to-lemma import reflects proof order: the theorem is stated before
the lemma in the book, while its Lean proof uses the following lemma. As in the
repository's earlier Stage 3.4 audits, this forward implementation edge is
documented here but excluded from the acyclic backward pedagogical graph.

## Actual item dependency graph

The eight conservative reading-order edges are replaced by seven actual
backward edges:

1. Theorem 3.8.1 → Definition 2.3.8;
2. Lemma 3.8.2 → Definition 2.3.8;
3. Problem 3.8.3 → Theorem 3.8.1;
4. Problem 3.8.3 → Lemma 3.8.2;
5. Problem 3.8.4 → Problem 3.8.3;
6. Problem 3.8.5 → Definition 2.3.8;
7. Remark 3.8.6 → Definition 2.3.8.

The heading has no provider. The proof discussion has no provider separate
from the shared theorem endpoint. Intra-item provider edges collapse at item
granularity. The repository graph therefore moves from 582 to 581 edges. Every
retained item edge points strictly backward, and every scoped
`actual_internal_dependencies` array agrees exactly with
`dependencies/internal.json`.

## Durable tracker result

- all eight exact records have complete section `3.8` `stage3_4` objects;
- inherited workflow status, claim coverage, Stage 3.2, Stage 3.3, fidelity,
  and proof-integrity metadata are unchanged;
- the normalized non-§3.8 tracker projection and non-§3.8 dependency-source
  projection are unchanged;
- external-dependency and Mathlib-coverage maps are unchanged.

## Validation

- all thirteen providers build successfully one at a time;
- the exact thirteen-provider aggregate builds successfully (8,593 jobs);
- the complete 57-case independent omission matrix has 56 required imports and
  one proven redundancy;
- direct-import count: 57 → 56 (`-1`); repository graph: 582 → 581 (`-1`);
- exact eight-item tracker/graph agreement and backward-edge checks: pass;
- provider-body invariance after stripping imports: pass for all thirteen;
- item, dependency, external-dependency, and Mathlib-coverage validators: pass;
- `lake build EtingofRepresentationTheory.Chapter3`: success (8,692 jobs;
  pre-existing linter warnings only);
- scoped/non-scoped tracker and dependency invariance, JSON parsing, and
  `git diff --check`: pass.

This PR is limited to Chapter 3 §3.8 and Stage 3.4.

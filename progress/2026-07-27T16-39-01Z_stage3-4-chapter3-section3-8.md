# Stage 3.4 dependency audit — Chapter 3 §3.8

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8090 at commit
`4111d2c80cb486353e6ef482616303ed680daec1`. It covers the same eight
reading-order records at indices 162–169 and all thirteen exact providers. The
strict predecessor is `Chapter3/Discussion_after_Theorem3.7.1`; the strict
successor is `Chapter3/Introduction_to_3.9`.

No definition, theorem statement, or proof body changes. The corrected terminal
pass completes the import-minimization matrix, fixes source-span and stale
tracker metadata found by the full-stack audit, and records the complete actual
item dependency graph.

## Independent direct-import tests

The thirteen providers initially contain 57 direct import statements. The
published Stage 3.4 pass removed one valid redundancy; the terminal correction
removes 31 more. Every one of the 25 retained lines was then tested
independently by omitting only that line from the fully trimmed provider and
re-elaborating the complete provider with `lake env lean /dev/stdin`. The
result is exact:

- all 25 retained-import omissions fail elaboration;
- the no-omission controls elaborate successfully.

The direct-import count is therefore 57 → 25: 32 proven redundancies removed in
total. The separate cancellation provider still requires `Problem3_8_3` for
the arbitrary-field Krull–Schmidt results, so that cross-item dependency remains
represented at the Problem 3.8.4 item.

Removing import lines from the base and final versions makes every provider
body byte-for-byte identical. Thus the edit changes neither mathematical
content nor any declaration body.

## Exact provider graph

After trimming, the providers have 14 retained direct project-import edges.
They split into:

- five backward direct cross-item edges;
- eight intra-item edges connecting the eight-file Problem 3.8.4 implementation;
- one forward implementation edge from `Theorem3_8_1` to the later
  `Lemma3_8_2` provider.

The Problem 3.8.4 intra-item chain is exact: cancellation imports Problem 3.8.3;
descent imports functoriality; finite imports power and cancellation; general
imports finite and descent; main imports finite and descent; and
power imports the base setup provider. The base setup and functoriality
providers import no project module.

The theorem-to-lemma import reflects proof order: the theorem is stated before
the lemma in the book, while its Lean proof uses the following lemma. As in the
repository's earlier Stage 3.4 audits, this forward implementation edge is
documented here but excluded from the acyclic backward pedagogical graph.

## Actual item dependency graph

The eight actual semantic item edges are:

1. Theorem 3.8.1 → Definition 2.3.8;
2. Lemma 3.8.2 → Definition 2.3.8;
3. Problem 3.8.3 → Theorem 3.8.1;
4. Problem 3.8.3 → Lemma 3.8.2;
5. Problem 3.8.4 → Problem 3.8.3;
6. Problem 3.8.5 → Definition 2.3.8;
7. Remark 3.8.6 → Definition 2.3.8;
8. Remark 3.8.6 → Problem 3.8.5.

The heading has no provider. The proof discussion has no provider separate
from the shared theorem endpoint. Intra-item provider edges collapse at item
granularity. The last edge is semantic rather than a direct import: the
Remark's opening failure claim is witnessed by the explicit Problem 3.8.5
counterexample. The repository graph therefore remains at 582 edges. Every
retained item edge points strictly backward, and every scoped
`actual_internal_dependencies` array agrees exactly with
`dependencies/internal.json`.

## Durable tracker result

- all eight exact records have complete section `3.8` `stage3_4` objects;
- the seven mathematical records are terminal `dependency_trimmed`, and the
  heading is terminal `non_formalizable`;
- claim coverage and proof-integrity results are unchanged, while exact source
  spans, fidelity/coverage, and resolved issue fields are synchronized;
- the normalized non-§3.8 tracker projection and non-§3.8 dependency-source
  projection are unchanged;
- external-dependency and Mathlib-coverage maps are unchanged.

## Validation

- all thirteen providers build successfully one at a time;
- the exact thirteen-provider aggregate builds successfully (8,593 jobs);
- the terminal 25-case retained-import omission matrix has 25 required imports;
- direct-import count: 57 → 25 (`-32`); direct project imports: 14;
  repository graph: 582 → 582;
- exact eight-item tracker/graph agreement and backward-edge checks: pass;
- provider-body invariance after stripping imports: pass for all thirteen;
- item, dependency, external-dependency, and Mathlib-coverage validators: pass;
- `lake build EtingofRepresentationTheory.Chapter3`: success (8,692 jobs;
  pre-existing linter warnings only);
- scoped/non-scoped tracker and dependency invariance, JSON parsing, and
  `git diff --check`: pass.

This note records the corrected Chapter 3 §3.8 terminal dependency audit.

# Stage 3.3 proof-integrity review — Chapter 3 §3.8

## Scope and inherited coverage

This stacked review is based exactly on Stage 3.2 draft PR #8086 at commit
`520d92715627bd4fd113e67b76dd836d8122561e`. The exact scope is the eight
contiguous tracker records at indices 162–169, from
`Chapter3/Introduction_to_3.8` through `Chapter3/Remark3.8.6`. The strict
predecessor is `Chapter3/Discussion_after_Theorem3.7.1`; the strict successor
is `Chapter3/Introduction_to_3.9`.

The inherited 29-claim inventory is unchanged: 18 claims are `formalized`, ten
are `covered_elsewhere`, one heading is `non_formalizable`, and none is a gap.
All 4,390 lines of the thirteen exact providers were included in this audit:
`Theorem3_8_1`, `Lemma3_8_2`, `Problem3_8_3`, the eight-file `Problem3_8_4`
chain, `Problem3_8_5`, and `Remark3_8_6`.

## Durable declaration inventory

The section heading has proof integrity `not_applicable`; the other seven
records are `sorry_free` at the Stage 3.3 gate and have terminal workflow
status `dependency_trimmed`. The heading itself is terminal
`non_formalizable`. Their durable `stage3_3.declarations` arrays contain 84
distinct public authored declarations. The proof discussion intentionally repeats
`Etingof.krull_schmidt_uniqueness`, because its source claims are implemented
inside that shared theorem endpoint. The distinct union still has exactly 84
names.

The inventory is complete by construction: after excluding private and
compiler-generated names, its sorted distinct union exactly matches the public
constants found by exhaustive module-origin enumeration. The public counts are:

- two Theorem 3.8.1 endpoints;
- two Lemma 3.8.2 endpoints;
- four arbitrary-field Problem 3.8.3 wrappers;
- 42 declarations across the complete eight-provider Problem 3.8.4 chain;
- 29 declarations for the literal continuous-function counterexample; and
- five finite-length endpoints for Remark 3.8.6.

Private names and generated names are intentionally excluded from the durable
arrays because they are not stable public API. They were nevertheless included
in the proof-integrity audit below.

## Exhaustive compiled declaration and axiom audit

The comment-stripped sources contain 102 authored declaration heads: 84 public
and 18 private. Lean's module-origin data finds 282 compiled constants in the
same providers, so the audit also covers all 180 compiler-generated proof,
match, simp, and equation helpers. Per-provider compiled counts are:

- `Lemma3_8_2`: 2; `Theorem3_8_1`: 43; `Problem3_8_3`: 4;
- `Problem3_8_4`: 15; `Cancellation`: 17; `Descent`: 2; `Finite`: 18;
- `Functoriality`: 57; `General`: 1; `Main`: 1; `Power`: 22;
- `Problem3_8_5`: 57; and `Remark3_8_6`: 43.

`Lean.collectAxioms` was run on every one of the 282 constants. The exact
transitive-axiom distribution is:

- `[propext, Classical.choice, Quot.sound]`: 186;
- `[propext, Quot.sound]`: 79;
- `[propext]`: 5; and
- no axioms: 12.

No constant depends on `sorryAx` or a project-specific axiom. The private
existence/uniqueness induction and exchange helpers, the cancellation and
finite-length helpers, and every generated structure proof were therefore all
checked rather than inferred from the public endpoints.

A comment-stripped source scan finds no `sorry`, `admit`, `proof_wanted`,
`sorryAx`, `native_decide`, `unsafe`, `axiom`, or source-level `opaque`
declaration. The one raw occurrence of “opaque” is explanatory prose in a
comment in `Problem3_8_4_Descent.lean`.

## Completeness and import durability

The complete proof chains terminate in the advertised endpoints: both
Krull–Schmidt halves, the arbitrary-field wrappers, both general scalar-
extension descent results, the finite-extension and power-cancellation chain,
all four counterexample conclusions, and finite-length existence and
uniqueness. There is no deferred declaration, placeholder, hidden admission,
or orphaned generated helper.

The thirteen providers have 57 direct import statements. They contain the
expected earlier local dependencies and Mathlib dependencies; no provider
imports the Chapter 3 aggregate or a later Chapter 3 section. Imports are
recorded but intentionally unchanged here: redundancy testing and
minimization belong to Stage 3.4.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared
  package cache;
- all thirteen exact providers build successfully together (8,593 jobs);
- exhaustive module-origin enumeration and `Lean.collectAxioms`: 282/282
  constants clean;
- exact public-declaration completeness comparison: 84/84 distinct names;
- exact-provider admission/placeholder and direct-import scans: clean;
- exact proof-integrity aggregation: seven `sorry_free`, one `not_applicable`;
- all four repository validators pass;
- `lake build EtingofRepresentationTheory.Chapter3`: success (8,692 jobs;
  pre-existing linter warnings only);
- removing only `stage3_3` from the eight scoped records reproduces the exact
  Stage 3.2 base;
- the corrected terminal stack preserves the 29-claim inventory and proof
  integrity while synchronizing exact spans, fidelity/coverage, resolved issue
  fields, dependencies, and workflow statuses;
- `jq empty progress/items.json` and `git diff --check`: pass.

This note records the Stage 3.3 proof-integrity result within the corrected
Chapter 3 §3.8 terminal stack.

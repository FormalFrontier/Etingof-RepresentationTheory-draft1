# Stage 3.3 proof-integrity review — Chapter 3 §3.9

## Scope and inherited coverage

This stacked review is based exactly on Stage 3.2 draft PR #8087 at commit
`ab3fb9ca94988b7093e1b02c9d8bd49710515eda`. Reading order gives the six §3.9
catalog items at indices 170–175, from `Chapter3/Introduction_to_3.9` through
`Chapter3/Problem3.9.5`. The strict predecessor is `Chapter3/Remark3.8.6`; the
strict successor is `Chapter3/Introduction_to_3.10`.

The inherited 44-claim inventory is unchanged: 38 claims are `formalized`, three
are `covered_elsewhere`, two are `non_formalizable`, one is an
`intentional_omission` tracked by #6607, and none is a gap. The seven exact
providers are:

- `EtingofRepresentationTheory/Chapter3/Problem3_9_1.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_2.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_2_Classification.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_3.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_3_TwoDim.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_4.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_5.lean`.

The introduction is an organizational heading with no provider or proof
obligation. Its proof integrity is therefore `not_applicable`; all five problem
items are `sorry_free`.

## Exhaustive proof-integrity audit

The durable `stage3_3` inventories contain all 322 stable, named, authored public
declarations: 70 for Problem 3.9.1; 95 across the two Problem 3.9.2 providers; 67
across the two Problem 3.9.3 providers; 35 for Problem 3.9.4; and 55 for Problem
3.9.5. By source declaration kind these comprise eight abbreviations, 78
definitions, one inductive type, 13 named instances, 40 lemmas, one structure,
and 181 theorems. Every durable name was independently matched to a constant
attributed to its exact provider module.

The environment-origin audit was deliberately broader than the durable public
API. `Lean.collectAxioms` checked all 763 constants emitted by the seven exact
providers:

- `Problem3_9_1`: 163 constants;
- `Problem3_9_2`: 145 constants;
- `Problem3_9_2_Classification`: 130 constants;
- `Problem3_9_3`: 26 constants;
- `Problem3_9_3_TwoDim`: 104 constants;
- `Problem3_9_4`: 95 constants;
- `Problem3_9_5`: 100 constants.

This exhaustive set includes 713 public and 50 private constants, as well as all
anonymous instances, constructors and projections, generated equation theorems,
and internal proof declarations. Fourteen use no axioms; 20 use only `propext`;
three use only `Quot.sound`; 264 use `propext` and `Quot.sound`; and 462 use
`propext`, `Classical.choice`, and `Quot.sound`. None depends on `sorryAx` or any
project-specific or unexpected axiom.

A token-aware source scan found no `sorry`, `admit`, `proof_wanted`, `sorryAx`,
`native_decide`, `unsafe`, `axiom`, or source-level `opaque` declaration. Every
scoped theorem and helper is backed by a closed Lean term. No provider source
edit was required.

## Direct-import audit

The seven providers have 68 direct import statements. They were enumerated and
checked for scope hazards, including the local provider chains and the existing
Chapter 6 dependencies of Problem 3.9.3. No import is changed at Stage 3.3.
Redundancy testing and minimization—including the duplicate direct
`Mathlib.LinearAlgebra.Dimension.Finrank` import in `Problem3_9_5.lean`—are
deliberately reserved for Stage 3.4.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared
  package cache;
- all seven exact providers build successfully together (8,638 jobs);
- exhaustive module-origin enumeration and `Lean.collectAxioms`: 763/763
  constants clean;
- exact-provider admission/placeholder and direct-import scans: clean;
- exact six-item aggregation: five `sorry_free`, one `not_applicable`, and 322
  distinct durable declarations;
- `lake build EtingofRepresentationTheory.Chapter3` succeeds (8,692 jobs;
  pre-existing warnings only);
- all four repository validators pass;
- strict tracker/provider/dependency invariance, `jq empty progress/items.json`,
  and `git diff --check` pass.

This PR is limited to Chapter 3 §3.9 and Stage 3.3.

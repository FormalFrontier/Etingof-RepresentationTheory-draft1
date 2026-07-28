# Stage 3.3 proof-integrity review — Chapter 3 §3.9

## Scope and inherited coverage

The original Stage 3.3 review was stacked on the Stage 3.2 draft provenance
from PR #8087 at commit `ab3fb9ca94988b7093e1b02c9d8bd49710515eda`.
This permanent report was later reconciled with #8101/#8104 and the integrated
§3.9 merge `2725e8a886b888938503b93a064ab2fd82ad184d`. Reading order gives the
six §3.9 catalog items at indices 170–175, from
`Chapter3/Introduction_to_3.9` through `Chapter3/Problem3.9.5`. The strict
predecessor is `Chapter3/Remark3.8.6`; the strict successor is
`Chapter3/Introduction_to_3.10`.

The inherited 44-claim inventory has the same source boundaries: 39 claims are
`formalized`, three are `covered_elsewhere`, two are `non_formalizable`, there
is no intentional omission, and none is a gap. The ten exact
providers are:

- `EtingofRepresentationTheory/Chapter3/Problem3_9_1.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_2.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_2_Classification.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_3.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_3_TwoDim.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_4.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_5.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_5_Spinor.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_5_Spinor_Transport.lean`;
- `EtingofRepresentationTheory/Chapter3/Problem3_9_5_Spinor_Odd.lean`.

The introduction is an organizational heading with canonical top-level status
`non_formalizable` and no provider or proof obligation, so its proof integrity
is `not_applicable`. All five problem provider sets are `sorry_free`; their
canonical post-Stage-3.4 top-level status is `dependency_trimmed`.

## Exhaustive proof-integrity audit

The durable `stage3_3` inventories contain all 442 stable, named, authored public
declarations: 70 for Problem 3.9.1; 95 across the two Problem 3.9.2 providers; 67
across the two Problem 3.9.3 providers; 56 for Problem 3.9.4; and 154 across the
four Problem 3.9.5 providers. The Problem 3.9.4 inventory grows by 21 after #8101, including the
dual-number augmentation, scalar-series and cocycle construction, the rigidity
counterexample components, the two low-level coefficient helpers, and
`not_problem3_9_4b_dualNumber`. Problem 3.9.5 retains #8104's approved 20 representative top-level
coverage endpoints separately. By source declaration kind the exhaustive
durable inventory comprises 11 abbreviations, 115 definitions, one inductive
type, 22 named instances, 51 lemmas, one structure, and 241 theorems. Every
durable name was independently matched to a constant
attributed to its exact provider module.

The environment-origin audit was deliberately broader than the durable public
API. `Lean.collectAxioms` checked the invariant all-ten aggregate of 1,304
module-attributed constants emitted by the exact providers. Per-provider
subtotals are intentionally not treated as invariant because compiler
attribution can vary with the import environment. The exhaustive aggregate
includes 1,244 public and 60 private constants, as well as all
anonymous instances, constructors and projections, generated equation theorems,
compiler auxiliaries, and internal proof declarations. The count is taken from
the final post-trimming module-origin map, not merely the ordinary constant
table (which omits compiler auxiliaries). Of these, 260 use no axioms; 20 use
only `propext`; three use only `Quot.sound`; 289 use `propext` and
`Quot.sound`; and 732 use
`propext`, `Classical.choice`, and `Quot.sound`. None depends on `sorryAx` or any
project-specific or unexpected axiom.

A token-aware source scan found no `sorry`, `admit`, `proof_wanted`, `sorryAx`,
`native_decide`, `unsafe`, `axiom`, or source-level `opaque` declaration. Every
scoped theorem and helper is backed by a closed Lean term. No provider source
edit was required.

## Direct-import audit

The ten providers have 79 direct import statements after #8101 and #8104. They were enumerated and
checked for scope hazards, including the local provider chains and the existing
Chapter 6 dependencies of Problem 3.9.3. No import is changed at Stage 3.3.
Redundancy testing and minimization—including the duplicate direct
`Mathlib.LinearAlgebra.Dimension.Finrank` import in `Problem3_9_5.lean`—are
deliberately reserved for Stage 3.4.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared
  package cache;
- all ten exact providers build successfully together;
- exhaustive module-origin enumeration and `Lean.collectAxioms`: 1,304/1,304
  constants clean;
- exact-provider admission/placeholder and direct-import scans: clean;
- exact six-item aggregation: five `sorry_free`, one `not_applicable`, and 442
  distinct durable declarations;
- focused build of all ten exact providers succeeds (8,642 jobs), with no new
  warnings at the warning gate;
- `lake build EtingofRepresentationTheory.Chapter3` succeeds (8,695 jobs;
  pre-existing warnings only);
- the CI-equivalent build of 818 target modules succeeds (9,400 jobs), with no
  new warnings at its warning gate;
- all four repository validators pass;
- strict tracker/provider/dependency invariance, `jq empty progress/items.json`,
  and `git diff --check` pass.

This reconciled audit is limited to Chapter 3 §3.9 and Stage 3.3.

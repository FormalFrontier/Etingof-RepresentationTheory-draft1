# Stage 3.2 fidelity review — Chapter 3 §3.10

## Scope

Reading order gives exactly six contiguous §3.10 catalog items, from
`Chapter3/Introduction_to_3.10` through `Chapter3/Discussion_proof_of_Theorem3.10.2`. The
preceding item is `Chapter3/Problem3.9.5`; the next item is `Chapter4/Introduction`, so the scope
also closes Chapter 3. The six source blobs are served by four Lean providers:
`Exercise3_10_1.lean`, `Theorem3_10_2.lean`, `Remark3_10_3.lean`, and
`TensorProductRadical.lean`.

## Claim audit

All six blobs and all four providers were read in full. The durable inventory has 21 claim units:

- 16 `formalized`;
- 2 `covered_elsewhere` by precise Mathlib or project declarations;
- 3 `non_formalizable` organizational or qualitative units;
- zero accidental or unclassified gaps.

The theorem provider covers part (i), the existence statement in part (ii), and uniqueness up to
factor isomorphism. Its public APIs assume finite-dimensionality only of the representations, not
of the algebras, and regression examples instantiate both parts with the infinite-dimensional
algebra `k[X]`. The exact scoped build now succeeds, so tracker regression #7520 is stale on the
audited `main` commit.

The source proof is also represented independently. `TensorProductRadical.lean` formalizes the
image-algebra reduction, the nilpotent easy inclusion, the semisimple-quotient hard inclusion, the
radical equality, and both quotient identifications. The theorem file itself uses a separate
density/Artinian proof, so the source route and the theorem endpoint do not depend on each other.
Both infinite-dimensional failures in Remark 3.10.3 are covered: the rational-function tensor
algebra is not a field, and the simple entangled Weyl module cannot be an external tensor product
with a simple first factor.

## Declaration and trust audit

Exact module-attribution inspection found 152 constants across the four providers: 120 public and
32 private, comprising 123 theorem declarations and 29 definitions. There are no declaration-level
axioms or opaque declarations. A scoped source scan found no `sorry`, `admit`, `proof_wanted`,
`sorryAx`, `axiom`, `opaque`, or `native_decide`; transitive axiom collection over every attributed
constant found only `propext`, `Classical.choice`, and `Quot.sound`.

## Validation

- local worktree build state uses a worktree-local `.lake/build` and only shares `.lake/packages`;
- all four scoped providers build successfully together; the warnings are pre-existing
  linter/deprecation warnings and the theorem provider's existing style warnings;
- the full `EtingofRepresentationTheory.Chapter3` build succeeds;
- JSON syntax, the exact six-item/21-claim verdict aggregation, the four schema/dependency/coverage
  validators, and normalized out-of-scope tracker invariance pass;
- `scripts/verify_blobs.py` retains its pre-existing `KeyError: 'id'` because it does not skip the
  ten derived overlay records keyed by `derived_from`; no blob or page file changed in this audit;
- `git diff --check` passes.

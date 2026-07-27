# Stage 3.3 proof-integrity review — Chapter 3 §3.6

## Scope

Reading order gives exactly three §3.6 catalog items, the contiguous
`progress/items.json` range 156–158:

1. `Chapter3/Introduction_to_3.6`;
2. `Chapter3/Exercise3.6.1`;
3. `Chapter3/Theorem3.6.2`.

The preceding item is `Chapter3/Proposition3.5.8`; the next item, and strict stopping
boundary, is `Chapter3/Introduction_to_3.7`. This review is based exactly on Stage 3.2
commit `c0c76897bab554d7359a4f0294e19a2d837afb06`.

The 19-claim Stage 3.2 inventory is unchanged: 12 claims are formalized, six are covered
elsewhere, and the organizational heading is non-formalizable. All four exact providers
were audited:

- `Chapter3/Introduction3_6.lean`;
- `Chapter3/Exercise3_6_1.lean`;
- `Chapter3/Theorem3_6_2.lean`;
- `Chapter3/CommutatorMatrixTraceless.lean`.

## Proof-integrity audit

The durable Stage 3.3 inventory records 13 authored public declarations:

- six for the character definition, cyclicity, commutator span, vanishing, and quotient
  factorization in the introduction;
- three for finite-dimensional submodule and quotient instances and character additivity
  in Exercise 3.6.1;
- four for linear independence, the semisimple character basis, and the general and
  `Fin`-indexed matrix commutator/traceless equalities in Theorem 3.6.2.

An exhaustive environment-origin audit inspected all 33 constants emitted by the four
provider modules, including internal proof declarations, private helpers, generated
equations, and the lazily generated `contractLeft.eq_1`. Five use no axioms; two use only
`propext`; six use only `propext` and `Quot.sound`; and 20 use only `propext`,
`Classical.choice`, and `Quot.sound`. No constant depends on `sorryAx` or any other
unexpected axiom.

The scoped source scan finds no `sorry`, `admit`, `proof_wanted`, `sorryAx`,
`native_decide`, `axiom`, or `opaque` declaration. Every scoped theorem and helper is
therefore backed by a closed Lean term. No provider source edit was required.

## Deferred import findings

The direct-import audit found eight transitive-redundancy candidates, intentionally left
unchanged for Stage 3.4:

- six in `Theorem3_6_2.lean`: `LinearIndependent.Lemmas`,
  `SimpleModule.Basic`, `LinearIndependent.Defs`, `IsAlgClosed.Basic`,
  `FiniteDimensional.Defs`, and `TensorProduct.Basic`;
- two in `CommutatorMatrixTraceless.lean`: `Matrix.Basis` and `Matrix.Trace`.

The introduction and exercise providers have no reported redundant direct import. Neither
the provider dependency map nor the aggregate dependency map changes in this Stage 3.3 PR.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared package
  cache;
- all four scoped providers build successfully together (1,957 jobs);
- `lake build EtingofRepresentationTheory.Chapter3` succeeds (8,692 jobs);
- all four repository validators pass;
- the exact three-item Stage 3.3 aggregation reports `complete` and `sorry_free` for
  every item, with 13 distinct durable declarations;
- the Stage 3.2 claim records, status, fidelity, provider metadata, dependency maps, and
  normalized non-scope tracker projection are unchanged;
- `git diff --check` passes.

This PR is limited to Chapter 3 §3.6 and Stage 3.3.

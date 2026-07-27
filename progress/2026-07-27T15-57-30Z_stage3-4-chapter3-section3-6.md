# Stage 3.4 dependency review — Chapter 3 §3.6

## Scope

This review is limited to the three §3.6 catalog items at global
`progress/items.json` indices 156–158:

1. `Chapter3/Introduction_to_3.6`;
2. `Chapter3/Exercise3.6.1`;
3. `Chapter3/Theorem3.6.2`.

The strict boundaries remain Proposition 3.5.8 before the section and the introduction to
§3.7 after it. The branch is based exactly on Stage 3.3 commit
`d9c66ad163115f98680dfbbbd682d92473b21691`.

## Direct-import audit

All four exact providers were audited with `#redundant_imports`. Their direct-import count
falls from 13 to five:

- `Theorem3_6_2.lean` falls from eight imports to two. It retains
  `Mathlib.LinearAlgebra.Trace` and the project provider `Theorem3_2_2`; six transitive
  Mathlib imports are removed.
- `CommutatorMatrixTraceless.lean` falls from three imports to its single project provider,
  `Introduction3_6`; the Matrix basis and trace imports are already supplied transitively.
- `Introduction3_6.lean` and `Exercise3_6_1.lean` retain their sole project import.

After trimming, every one of the four providers reports
`No transitively redundant imports found.` All providers build together in 1,957 jobs.
The only Lean source edits are deletion of those eight import lines; no declaration,
statement, proof term, documentation, or namespace is changed.

## Actual internal dependencies

The section still has three item-level dependency edges, but the graph now records the
actual declaration use rather than reading-order adjacency:

- the introduction has no backward dependency. Its apparent import of `Theorem3_6_2`
  supplies `Etingof.character`, which is cataloged as part of the same introduction item;
- Exercise 3.6.1 depends on the introduction's character definition;
- Theorem 3.6.2 depends on `density_theorem_part2` from Theorem 3.2.2 and on the
  introduction's `commutatorSubmodule`, used by the standalone matrix provider.

Thus the false introduction-to-Proposition-3.5.8 and theorem-to-Exercise-3.6.1 edges are
removed. The true theorem-to-Theorem-3.2.2 and theorem-to-introduction edges are added.
The exercise-to-introduction edge is retained. The repository aggregate remains 582 edges.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared package
  cache;
- all four scoped providers build successfully together (1,957 jobs);
- `lake build EtingofRepresentationTheory.Chapter3` succeeds (8,692 jobs);
- all four providers are `#redundant_imports`-clean after trimming;
- all four repository validators pass;
- Stage 3.2 claim coverage and Stage 3.3 proof-integrity records are unchanged;
- the three scoped item records change only by addition of `stage3_4`;
- the normalized non-scope tracker projection, non-scope dependency projection, external
  dependencies, provider declarations, and proof bodies are unchanged;
- `git diff --check` passes.

This PR is limited to Chapter 3 §3.6 and Stage 3.4.

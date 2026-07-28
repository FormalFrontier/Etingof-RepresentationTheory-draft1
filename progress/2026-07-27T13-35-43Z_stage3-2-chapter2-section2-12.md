# Stage 3.2 fidelity review — Chapter 2 §2.12

## Scope

Reading order gives exactly two §2.12 catalog items:

1. `Chapter2/Discussion_2.12_heading`, page 35 lines 27–33;
2. `Chapter2/Definition2.12.1`, page 36 lines 1–16.

The preceding item is `Chapter2/Exercise2.11.7`; the next item is
`Chapter2/Discussion_2.13_heading`. Thus the nonnumeric introductory discussion is part of the
scope even though it previously had no Lean provider and was labeled `trivial`.

## Claim audit and repairs

Both source blobs were checked in full against the page transcription. The durable inventory has
eleven mathematical claim units, all now `formalized`: three in the introductory discussion and
eight in Definition 2.12.1.

Stage 3.2 repaired the following accidental coverage gaps:

1. A new `Discussion_2_12_heading.lean` provider records `T(V)` as the algebraic direct sum of its
   tensor powers, proves the pure-degree and homogeneous-multiplication formulas, and gives the
   basis-dependent equivalence with the free algebra, including its generator formula.
2. Definition 2.12.1 now exposes the exact generator relations for the symmetric, exterior, and
   universal enveloping algebras.
3. The symmetric algebra is identified with the polynomial algebra on any chosen basis, and the
   exterior algebra with the exterior algebra on the corresponding free coordinate module.
4. The final displayed decompositions are genuine linear equivalences to the exact quotient
   models `Problem2_11_3.SymPow k V n` and `Problem2_11_3.ExtPow k V n`, not merely prose or
   unnamed homogeneous components.

The existing equivalence between coordinate-free `U(L)` and Definition 2.9.9's
basis-and-structure-constants presentation was audited and retained. No claim was downgraded to an
intentional omission or nonformalizable prose.

## Durable tracker result

Both items now have complete Stage 3.2 `claim_coverage` records with verified definition
integrity, statement fidelity, and nonvacuity. The introductory discussion moves from the
incorrect wave-1 `trivial` label to `covered_full`; Definition 2.12.1 remains `covered_full` with
its formerly implicit basis and decomposition claims now inventoried explicitly.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` is linked to the shared package cache;
- both scoped providers build successfully together (8585 jobs);
- full `lake build EtingofRepresentationTheory.Chapter2` succeeds (8745 jobs); replayed warnings
  are pre-existing and outside the changed §2.12 providers;
- the scoped scan finds no `sorry`, `admit`, `axiom`, `proof_wanted`, `opaque`, or
  `native_decide` declarations;
- representative `#print axioms` checks report only standard foundational axioms;
- `jq empty progress/items.json` and the exact two-item/eleven-claim aggregation pass;
- `python3 scripts/validate_items.py` passes with full 5721/5721-line coverage (plus its 593
  pre-existing extra-field warnings);
- `python3 scripts/validate_dependencies.py` passes with its one pre-existing conservative-default
  warning;
- the normalized non-§2.12 tracker projection is unchanged and `git diff --check` passes.

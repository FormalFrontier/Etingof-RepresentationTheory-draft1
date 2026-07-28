# Stage 3.4 dependency trimming — Chapter 2 §2.3

## Scope

This pass analyzes the actual direct internal dependencies of exactly the 24 catalog items from
`Chapter2/Definition2.3.1` through `Chapter2/Problem2.3.18`, excluding the following §2.4 heading.
All scoped proofs were already verified sorry-free in Stage 3.3; this pass does not alter Lean
statements or proofs.

## Result

The conservative reading-order chain had 24 edges across the scoped nodes. Reviewing the scoped
Lean imports, proof terms, and `covered_elsewhere` declaration providers reduced that to eight
direct project edges:

- `Discussion_irreducible_vs_indecomposable` → `Definition2.3.8` for the project
  indecomposability predicate used by both formalized assertions.
- `Remark2.3.11` and `Discussion_proof_Corollary2.3.10` → `Corollary2.3.10`.
- `Discussion_proof_Corollary2.3.12` → both `Corollary2.3.10` and `Corollary2.3.12`.
- `Example2.3.14` → `Definition2.3.8` for the Jordan-block indecomposability results.
- `Problem2.3.16` → `Definition2.3.8` and `Problem2.3.15` for indecomposability and the existence
  of a simple submodule.

The remaining 18 nodes have no internal edge: their source files import and use Mathlib only, or
the item is organizational prose with no proof term. In particular, the consecutive numbering of
the definitions, examples, corollaries, and problems does not itself induce a formal dependency.

Every scoped item now has a durable `stage3_4` record giving its dependency list and audit basis,
and its status is `dependency_trimmed`.

## Validation

- both JSON files parse successfully;
- exactly 24 §2.3 items have complete Stage 3.4 records and exactly eight scoped edges;
- every dependency source and target is present in the item catalog, with no duplicate or
  self-dependency;
- each `stage3_4.actual_internal_dependencies` array agrees exactly with
  `dependencies/internal.json`;
- all scoped Lean modules and the Chapter 2 aggregate build successfully;
- `git diff --check` passes.

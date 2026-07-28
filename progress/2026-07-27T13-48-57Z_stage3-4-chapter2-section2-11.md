# Stage 3.4 dependency audit — Chapter 2 §2.11

## Scope

This review is stacked exactly on Stage 3.3 draft PR #8036 at commit `c94aa99e`. It covers the
same eleven reading-order items from `Chapter2/Discussion_2.11_heading` through
`Chapter2/Exercise2.11.7` and all twelve provider files, including Problem 2.11.3's five providers
and Problem 2.11.6's documentation/policy provider.

No mathematical definition or theorem statement changed. The five intentional Problem 2.11.6
omissions remain omissions and are not assigned proof declarations or synthetic dependency edges.

## Direct import audit

All eleven import-bearing providers were checked with `#redundant_imports`; the import-free
Problem 2.11.6 provider is vacuous. Four providers changed:

- `Discussion_pure_tensors.lean` removes three transitively redundant imports:
  `TensorProduct.Basic`, `LinearAlgebra.Pi`, and `Algebra.Algebra.Bilinear`.
- `Problem2_11_3.lean` replaces `import Mathlib` with focused `Contraction` and `Determinant`
  imports.
- `Problem2_11_3_SymExtPow.lean` replaces `import Mathlib` with focused `Determinant`,
  `ExteriorPower.Basis`, and `PiTensorProduct.Basis` imports. Its one `norm_num` use is replaced
  by the direct proof `Nat.zero_lt_succ 0`, avoiding a tactic-bundle dependency without changing
  the theorem.
- `Problem2_11_3_SymPowBasis.lean` now imports `Data.Sym.Card` directly for
  `Sym.card_sym_eq_choose`; the preceding umbrella import had hidden this dependency.

Five direct lines were removed and six focused lines added: direct imports move from 21 to 22,
for net `+1`. This small increase makes dependencies explicit while eliminating both broad
`Mathlib` imports and three redundant direct imports. A final redundant-import pass reports no
transitively redundant import in any changed provider; the unchanged providers were likewise
clean in the full-scope pass.

## Actual internal dependency graph

The eleven conservative reading-order edges are replaced by two actual, backward project edges:

1. `Chapter2/Discussion_tensors_type` → `Chapter2/Discussion_pure_tensors`, because the mixed
   tensor basis is `Etingof.TensorTypes.tensorTypeBasis` from that provider;
2. `Chapter2/Problem2.11.6` → `Chapter2/Remark2.11.4`, because its non-omitted balanced tensor
   product is `Etingof.TensorProductOverRing`.

The other nine items use only Mathlib, same-item sibling providers, non-catalog infrastructure, or
have no proof-bearing provider. Scoped graph edges therefore move from 11 to 2, net `-9`. Both
remaining edges point strictly backward in catalog order; the explicit forward-edge check returns
an empty result. Tracker `actual_internal_dependencies` arrays agree exactly with
`dependencies/internal.json`.

## Durable tracker result

- all 11 exact records have complete section `2.11` `stage3_4` objects;
- all 11 workflow statuses advance to `dependency_trimmed`;
- the two actual edges are recorded with item-specific bases;
- Stage 3.2 and Stage 3.3 metadata are unchanged;
- the non-§2.11 tracker projection, non-§2.11 dependency-source projection, and all downstream
  incoming edges are unchanged from PR #8036.

## Validation

- isolated worktree build state with worktree-local `.lake/build` and shared package cache;
- final build of all 12 scoped providers: success (8592 jobs; only the pre-existing
  `Infrastructure/Triangularization.lean` header warning replayed);
- `lake build EtingofRepresentationTheory.Chapter2`: success (8744 jobs; pre-existing warnings
  only);
- initial full-scope and final changed-provider `#redundant_imports` checks: clean after trimming;
- exact 11-item tracker/graph agreement and no-forward-edge checks: passed;
- direct-import count check: 21 → 22 (`+1`); scoped edge count: 11 → 2 (`-9`);
- `jq empty progress/items.json dependencies/internal.json`: passed;
- `python3 scripts/validate_items.py`: passed with 5721/5721-line coverage;
- `python3 scripts/validate_dependencies.py`: passed with 583 entries and 573 total edges;
- `python3 scripts/validate_external_deps.py`: passed;
- normalized scoped/non-scoped invariance checks and `git diff --check`: passed.

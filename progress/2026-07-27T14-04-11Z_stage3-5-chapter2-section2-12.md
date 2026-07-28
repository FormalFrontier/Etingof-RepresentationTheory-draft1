# Stage 3.5 Mathlib-quality review — Chapter 2 §2.12

## Scope and inherited state

This stacked review is based exactly on Stage 3.4 draft PR #8045 at commit `18eb5145` and keeps
the same two reading-order items: `Chapter2/Discussion_2.12_heading` and
`Chapter2/Definition2.12.1`. The review covers all 32 public declarations defined by their two
providers: seven in the tensor-algebra discussion and twenty-five in Definition 2.12.1.

Stages 3.2–3.4 had already established full claim coverage, admission-free proof integrity, and
the exact minimal import/dependency surface. Stage 3.5 preserves those mathematical statements,
proof terms, and graph records.

## Declaration and source review

Temporary `#lint+ docBlameThm`, `#redundant_imports`, and `#min_imports` commands were run inside
both complete providers and then removed.

The first 17-linter pass found exactly two `simpNF` issues:

1. `tensorAlgebraEquivDirectSum_tprod` was marked `[simp]`, although Mathlib first normalizes
   `TensorAlgebra.tprod` to the product of degree-one generators;
2. `coordFreeToUeaBasis_ι` was marked `[simp]`, although Mathlib first unfolds the canonical UEA
   inclusion to `UniversalEnvelopingAlgebra.mkAlgHom` applied to `TensorAlgebra.ι`.

Both book-facing statements are clearer in their existing forms, so the justified repair is to
retain the public theorems and remove only the inappropriate simp registrations. The second full
linter pass reports zero errors: all 17 linters pass for 7 declarations in the discussion and 25
declarations plus 27 generated declarations in the definition provider.

Manual review confirms descriptive namespace-qualified names, complete declaration docstrings,
focused theorem statements, explicit universal-property proofs, and no fragile or deprecated
tactic pattern. Both files have zero lines over Mathlib's 100-character style limit and elaborate
standalone without warnings. Their Stage 3.4 import minima remain transitively irredundant.

## Integrity result

The declaration-wide `#print axioms` audit for all 32 public declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`. The scoped scan finds no `sorry`, `admit`, `proof_wanted`,
project `axiom`, vacuous `True` endpoint, or leftover diagnostic command.

## Durable tracker result

- both exact items now have status `proof_polished`;
- both have complete, verified section `2.12` `stage3_5` objects;
- the Stage 3.2 claim, Stage 3.3 proof-integrity, and Stage 3.4 dependency records are unchanged;
- no item, provider, graph record, or metadata outside §2.12 is modified.

## Validation

- both scoped providers build and elaborate standalone in the isolated worktree;
- `lake build EtingofRepresentationTheory.Chapter2`: success, with only pre-existing warnings
  outside the scoped providers;
- all 32 public declarations pass the foundational-axiom audit;
- `python3 scripts/validate_items.py`: passed with full byte coverage;
- `python3 scripts/validate_dependencies.py`: passed;
- `python3 scripts/validate_external_deps.py`: passed;
- exact Stage 3.5 scope/status aggregation, normalized non-scoped invariance, JSON parsing,
  line-length/admission/diagnostic scans, and `git diff --check`: passed.

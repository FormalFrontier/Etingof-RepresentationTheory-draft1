# Stage 3.4 dependency and import review — Chapter 2 §2.12

## Scope and inherited state

This stacked review is based exactly on Stage 3.3 draft PR #8042 at commit `cf4cde87` and keeps
the same two reading-order items: `Chapter2/Discussion_2.12_heading` and
`Chapter2/Definition2.12.1`. They remain bounded by `Chapter2/Exercise2.11.7` and
`Chapter2/Discussion_2.13_heading` in `progress/items.json`.

The inherited internal graph still used the conservative reading-order chain:

- `Discussion_2.12_heading ← Exercise2.11.7`;
- `Definition2.12.1 ← Discussion_2.12_heading`.

Neither edge reflects an actual project declaration dependency.

## Genuine project-item dependencies

The tensor-algebra discussion imports only Mathlib and therefore has no internal project-item
dependency.

Definition 2.12.1 has exactly three genuine backward dependencies:

1. `Chapter2/Discussion_2.6`, supplying `PresentedAlgebra`, its quotient generators, lift, relator
   theorem, and hom-extensionality principle used by the chosen-basis UEA presentation;
2. `Chapter2/Definition2.9.9`, supplying the earlier `UniversalEnvelopingAlgebraDef` alias that
   `ueaBasisAlgEquiv` explicitly connects to the coordinate-free construction;
3. `Chapter2/Problem2.11.3`, supplying the book's exact `SymPow` and `ExtPow` quotient models,
   their bases, and `exteriorPowerEquiv` used in both homogeneous decompositions.

Accordingly, `dependencies/internal.json` removes both conservative chain edges and records these
three exact edges. No other dependency or external-dependency record changes.

## Import audit

Temporary `#redundant_imports` and `#min_imports` diagnostics were run on both complete providers,
then removed from the committed sources.

- `Discussion_2_12_heading.lean`: no redundant imports; minImports retained exactly
  `Mathlib.LinearAlgebra.TensorAlgebra.Basis` and
  `Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower`.
- `Definition2_12_1.lean`: the initial diagnostic identified all five direct Mathlib imports as
  transitively redundant and retained exactly the three project imports above. After removing the
  five imports, the diagnostic reported no redundancy and the same three-import minimum.

The import-only source change preserves every declaration and proof term from Stages 3.2–3.3.

## Durable tracker result

- both exact items have status `dependency_trimmed` and complete section `2.12` `stage3_4`
  objects;
- actual internal-dependency split: zero for the discussion, three for the definition;
- the Stage 3.2 claim-coverage and Stage 3.3 proof-integrity records remain unchanged;
- no intentional omission is introduced or reclassified.

## Validation

- each scoped provider compiles standalone after the import trim;
- `lake build EtingofRepresentationTheory.Chapter2`: success, with only pre-existing warnings
  outside the scoped providers;
- `python3 scripts/validate_items.py`: passed with full byte coverage;
- `python3 scripts/validate_dependencies.py`: passed;
- `python3 scripts/validate_external_deps.py`: passed;
- exact scoped graph/tracker agreement, backward-edge ordering, three-edge aggregation, and
  normalized non-scoped invariance: passed;
- `jq empty` on both JSON files and `git diff --check`: passed.

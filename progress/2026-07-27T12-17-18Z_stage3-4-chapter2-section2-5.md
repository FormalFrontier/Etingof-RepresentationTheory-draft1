# Stage 3.4 dependency trimming — Chapter 2 §2.5

## Scope

This pass analyzes the actual internal dependencies of exactly
`Chapter2/Discussion_2.5_heading`, `Chapter2/Discussion_2.5_well_defined`,
`Chapter2/Problem2.5.1`, and `Chapter2/Problem2.5.2` after their Stage 3.3 proofs were verified.

## Actual dependencies

- `Chapter2/Discussion_2.5_heading` has no internal dependency. Its quotient-algebra type,
  quotient map, coset-equality bridge, and multiplication formula use Mathlib directly.
- `Chapter2/Discussion_2.5_well_defined` depends directly on
  `Chapter2/Discussion_2.5_heading`: its representative-independence proofs reuse the quotient
  map and coset-equality bridge from that item in their shared Lean file. Its quotient-module
  infrastructure otherwise comes directly from Mathlib.
- `Chapter2/Problem2.5.1` depends directly on `Chapter2/Definition2.3.8`, whose
  `Etingof.IsIndecomposable` predicate is the conclusion of the theorem. The remaining proof
  uses Mathlib's polynomial, quotient-ring, local-ring, and submodule infrastructure.
- `Chapter2/Problem2.5.2` also depends directly on `Chapter2/Definition2.3.8`: the final
  coregular example is stated using `Etingof.IsIndecomposable`. Its cyclicity definitions and
  proofs, coregular module, and concrete algebra construction are otherwise self-contained over
  Mathlib.

Thus the four conservative reading-order edges

```text
Discussion_2.5_heading       -> Problem2.4.1
Discussion_2.5_well_defined -> Discussion_2.5_heading
Problem2.5.1                 -> Discussion_2.5_well_defined
Problem2.5.2                 -> Problem2.5.1
```

become the four actual dependency records (three direct edges and one empty set)

```text
Discussion_2.5_heading       -> []
Discussion_2.5_well_defined -> Discussion_2.5_heading
Problem2.5.1                 -> Definition2.3.8
Problem2.5.2                 -> Definition2.3.8
```

All four items now carry durable `stage3_4` records and move to `dependency_trimmed`.

## Validation

- every internal dependency target exists in the root item catalog
- `python3 scripts/validate_items.py`
- `python3 scripts/validate_dependencies.py`
- relevant Chapter 2 Lean modules build
- `git diff --check`

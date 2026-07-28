# Stage 3.3 proof verification — Chapter 2 §2.4

## Scope

This Stage 3.3 pass covers exactly `Chapter2/Discussion_2.4_heading` and
`Chapter2/Problem2.4.1`. The faithful statement/definition review belongs to the preceding
Stage 3.2 PR and is not repeated here.

## Result

Every formal claim recorded by the §2.4 Stage 3.2 audit has a complete proof or construction:

- the ideal/subrepresentation bridges are definitional equalities;
- membership in the left/right views of a two-sided ideal uses Mathlib's exact carrier lemmas;
- the generated-ideal universal properties and `a * s * b` characterization are proved by
  Mathlib's span API;
- the kernel membership bridge is proved by `TwoSidedIdeal.mem_ker`;
- maximal left and right ideals follow from Mathlib's Krull theorem;
- maximal two-sided ideals have the explicit Zorn proof already present in `Problem2_4_1.lean`.

A source scan of the two scoped Lean files finds no `sorry`, `admit`, or project `axiom`.
The existing `sorry_free` item statuses remain valid. Durable `stage3_3` records now identify the
verified declarations for both items.

## Validation

- `lake build EtingofRepresentationTheory.Chapter2`
- scoped source scan for `sorry`, `admit`, and `axiom`
- `jq empty progress/items.json`
- `git diff --check`

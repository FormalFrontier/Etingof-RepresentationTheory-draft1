# Stage 3.2 fidelity audit — Chapter 2 §2.4

## Scope

This review covers exactly `Chapter2/Discussion_2.4_heading` and
`Chapter2/Problem2.4.1`. It performs Stage 3.2 only.

## Claim coverage

The section discussion contains substantive definitions and examples, so its earlier
`coverage_swept: trivial` classification was not sufficient. The new
`Discussion_2_4_heading.lean` records the complete dictionary:

- left and right ideals are submodules of the appropriate regular representations;
- two-sided ideals expose the same carrier as both a left and a right ideal;
- `⊥`, `⊤`, and `IsSimpleRing` match the zero ideal, whole ring, and simple-ring definition;
- `TwoSidedIdeal.ker` realizes kernels as two-sided ideals;
- one-sided spans have the required least-ideal universal properties;
- `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure` identifies the generated two-sided ideal
  with the additive span of the products `a * s * b`.

For Problem 2.4.1, `IsCoatom` is exactly the book's maximality condition. The three conclusions
are separately present as `exists_maximal_left_ideal`, `exists_maximal_right_ideal`, and
`exists_maximal_twoSided_ideal`; in particular, the two-sided conclusion was not silently replaced
by a one-sided theorem.

## Fidelity and non-vacuity

- The ring hypotheses include `Nontrivial A`, matching the book's implicit exclusion of the zero
  ring in the existence statement.
- Left, right, and two-sided ideals use distinct types, so none of the three conclusions implies
  the others by a vacuous type synonym.
- `IsCoatom I` includes `I ≠ ⊤` and forces every strict enlargement to be `⊤`.
- The generated-ideal statements retain both left and right multiplication in the two-sided case.
- No definition or data field contains `sorry`; the scoped proofs are already sorry-free.

## Durable state

Both items now have a `claim_coverage` object in `progress/items.json` with the complete claim
enumeration, declaration mapping, definition-integrity result, fidelity result, and non-vacuity
result. Existing advanced proof statuses were preserved.

## Validation

- `lake env lean EtingofRepresentationTheory/Chapter2/Discussion_2_4_heading.lean`
- `lake build EtingofRepresentationTheory.Chapter2` (passes; existing unrelated linter warnings remain)
- `jq empty progress/items.json`

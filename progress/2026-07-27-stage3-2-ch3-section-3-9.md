# Stage 3.2 claim audit: Chapter 3, Section 3.9

Reviewed on 2026-07-27 against the coverage, definition-integrity, anti-vacuity,
and statement-fidelity gates in `PLAN.md`, from exact base
`8c9904371093ccbe36d0ca0691e4f6095ca73f4d`.

## Scope

The audit covers the six contiguous tracker records strictly between
`Chapter3/Remark3.8.6` and `Chapter3/Introduction_to_3.10`:

- `Chapter3/Introduction_to_3.9`
- `Chapter3/Problem3.9.1`
- `Chapter3/Problem3.9.2`
- `Chapter3/Problem3.9.3`
- `Chapter3/Problem3.9.4`
- `Chapter3/Problem3.9.5`

Every exact source blob (book pages 56–59) and all ten Lean providers were
read in full. The providers are `Problem3_9_1`, `Problem3_9_2`,
`Problem3_9_2_Classification`, `Problem3_9_3`, `Problem3_9_3_TwoDim`,
`Problem3_9_4`, `Problem3_9_5`, `Problem3_9_5_Spinor`,
`Problem3_9_5_Spinor_Transport`, and `Problem3_9_5_Spinor_Odd`.

## Result

The 44 source claim units are recorded in `progress/items.json` with these
dispositions:

- 39 `formalized`
- 3 `covered_elsewhere`
- 2 `non_formalizable`
- 0 `intentional_omission`
- 0 `gap`

In particular:

- Problem 3.9.1 implements the cocycle/coboundary extension model, its exact
  sequence, the change-of-splitting criterion, the quotient classification,
  and the irreducible scalar-orbit criterion. The standard identification of a
  quotient by a kernel with a range is supplied by
  `LinearMap.quotKerEquivRange`.
- Problem 3.9.2 includes the full two-dimensional normal form and precise
  isomorphism criteria for the Jordan and split families, so its earlier
  partial-coverage history no longer describes the current providers.
- Problem 3.9.3 formalizes the simple modules, the exact Ext-one dimension
  formula, and an exhaustive two-dimensional normal form with the requested
  parameter and support criteria. Its earlier classification gap is closed.
- Problem 3.9.4 formalizes the deformation object, isomorphism, triviality,
  constant deformation, and the Ext-one rigidity implication. The source's
  open-ended question asking whether the converse holds remains classified as
  `non_formalizable` in the source-claim inventory. The integrated provider now
  also proves the derived negative answer in the suggested dual-number case:
  every deformation of the augmentation representation is constant while its
  self-Ext¹ is nonzero, yielding `not_problem3_9_4b_dualNumber`. This
  provider-authored answer is recorded in derived coverage and does not replace
  the interrogative source unit.
- Problem 3.9.5 formalizes both the abstract Clifford-algebra classification
  and the requested explicit exterior-algebra spinor proof. The continuation
  providers construct wedge and contraction, the hyperbolic spin
  representation and parity operator, transport arbitrary nondegenerate even
  forms to the hyperbolic model, and construct, separate, and exhaust the two
  odd spinors.

The current tracker preserves #8104's approved `covered_full` semantics, four
provider files, and 20 representative top-level endpoints while adding
stage-specific exhaustive audit objects.

## Declaration and axiom audit

A scratch import checked all 78 distinct declarations cited by the claim
inventory, including the ten provider chains and the relevant Mathlib
Clifford/quotient endpoints. Every declaration elaborated. `#print axioms`
reported only `propext`, `Classical.choice`, and `Quot.sound`; none depends on
`sorryAx` or a project-specific axiom. The scratch file was removed after the
check.

A token-aware source scan of all ten providers found no `sorry`, `admit`,
`proof_wanted`, `sorryAx`, `native_decide`, `axiom`, or `opaque` declaration.

## Validation

- Exact provider build: `lake build` on all ten scoped modules succeeds
  (pre-existing linter warnings only).
- Full chapter build: `lake build EtingofRepresentationTheory.Chapter3`
  succeeds (8,692 jobs; pre-existing linter warnings only).

The original Stage 3.2 source inventory remains exactly 44 units with the
dispositions above. This integration audit additionally refreshes derived
coverage and later-stage metadata made stale by the subsequent provider work;
it does not invent a new source claim from that provider-authored mathematics.

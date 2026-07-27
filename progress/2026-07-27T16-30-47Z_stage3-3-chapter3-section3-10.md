# Stage 3.3 proof verification — Chapter 3 §3.10

## Scope and result

This pass preserves the exact six-item, four-provider §3.10 scope established by Stage 3.2 at
commit `a98ea72b8a85ac7bf678b4aa32b7d4c9ba366813`. That audit inventoried 21 claims: 16
formalized, 2 covered elsewhere, 3 nonformalizable organizational or qualitative statements,
and no gaps. Stage 3.3 does not change those verdicts, declaration providers, or source files.

Five items are proof-bearing and verified `sorry_free`; the pre-theorem organizational preview
is `not_applicable`. The durable tracker arrays contain 77 declaration references, representing
74 unique declarations: all 70 durable authored declarations in the exact providers and four
external declarations used by the section. Repeated theorem endpoints in the proof discussion
remain explicit so that each item's proof basis is independently reviewable.

No Lean proof repair, import edit, or source change was required.

## Exhaustive environment audit

A scratch module imported all four exact providers and selected constants by Lean's recorded
module attribution. This inventories generated and private proof constants that a text-only list
of top-level commands would miss. It found 152 attributed constants:

- 106 have non-reserved public names, 14 have reserved generated names, and 32 are private;
- 123 are proof constants (82 non-reserved public, 14 reserved generated, and 27 private);
- the remaining 29 are definitions; there are no attributed constructors, inductives, recursors,
  opaque declarations, axioms, or quotients;
- the 106 non-reserved public constants comprise 70 durable authored declarations, 5 explicit
  local instance declarations used as implementation or regression scaffolding, and 31
  elaborator-generated public proof helpers.

The provider totals are:

- `Exercise3_10_1.lean`: 1 constant / 1 proof / 1 durable authored declaration;
- `Theorem3_10_2.lean`: 30 constants / 28 proofs / 6 durable authored declarations;
- `TensorProductRadical.lean`: 33 constants / 27 proofs / 24 durable authored declarations;
- `Remark3_10_3.lean`: 88 constants / 67 proofs / 39 durable authored declarations.

Every attributed constant was passed to `Lean.collectAxioms`, the engine used by
`#print axioms`. The audit fails on a direct project axiom or any dependency outside `propext`,
`Classical.choice`, and `Quot.sound`; it passed. The four external declarations
`Algebra.TensorProduct.tmul_mul_tmul`, `isSimpleModule_self_iff_isUnit`,
`Etingof.density_theorem_part1`, and `Algebra.TensorProduct.lift` were separately resolved and
audited with the same rule. Thus no scoped endpoint or provider-attributed constant contains
`sorryAx` or a project axiom.

The source-level scan likewise found no `sorry`, `admit`, `proof_wanted`, `sorryAx`,
`native_decide`, project `axiom`, or `opaque` declaration in the four providers.

## Direct-import audit

All 26 direct imports were reviewed and preserved without minimization: 2 in
`Exercise3_10_1.lean`, 8 in `Theorem3_10_2.lean`, 1 in `TensorProductRadical.lean`, and 15 in
`Remark3_10_3.lean`. The provider sources and their import lists are byte-for-byte unchanged
from the Stage 3.2 base.

## Validation

- exact four-provider build: success (8,588 jobs);
- full `EtingofRepresentationTheory.Chapter3` build: success;
- exhaustive attributed-constant and external-declaration axiom audit: success;
- exact six-item Stage 3.3 tracker audit and JSON parse: success;
- `scripts/validate_items.py`, `scripts/validate_dependencies.py`,
  `scripts/validate_external_deps.py`, and `scripts/validate_mathlib_coverage.py`: success;
- `scripts/verify_blobs.py` remains inapplicable to the repository's derived overlay records: it
  exits at the first derived record with the pre-existing `KeyError: 'id'`;
- normalized non-scope tracker projection and scoped records with `stage3_3` removed are unchanged
  from the exact Stage 3.2 base; dependency metadata and all provider sources are unchanged;
- only `.lake/packages` is shared, and `git diff --check` passes.

This PR is limited to Chapter 3 §3.10 and Stage 3.3.

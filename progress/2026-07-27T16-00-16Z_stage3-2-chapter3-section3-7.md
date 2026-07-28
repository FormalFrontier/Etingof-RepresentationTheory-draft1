# Stage 3.2 claim-coverage audit — Chapter 3 §3.7

## Scope

Reading order gives exactly three §3.7 tracker items (indices 159–161):

1. `Chapter3/Introduction_to_3.7` (page 53);
2. `Chapter3/Theorem3.7.1` (pages 53–54, including footnote 5);
3. `Chapter3/Discussion_after_Theorem3.7.1` (page 54).

The predecessor is `Chapter3/Theorem3.6.2`; the strict successor is
`Chapter3/Introduction_to_3.8`. The exact Lean providers are:

- `EtingofRepresentationTheory/Chapter3/Theorem3_7_1.lean`;
- `EtingofRepresentationTheory/Chapter3/Discussion_after_Theorem3_7_1.lean`;
- `EtingofRepresentationTheory/Chapter3/Discussion_footnote_3_7_1.lean`.

The footnote provider is attached to the theorem item by its existing tracker notes. No other
source file is assigned to this section.

## Claim audit

All three blobs were read in full and divided into 28 claim units. The durable dispositions in
`progress/items.json` are:

- 9 `formalized` claims;
- 15 `covered_elsewhere` claims;
- 4 `non_formalizable` expository claims;
- 0 gaps.

The theorem statement is fully represented, not merely by equality of lengths:
`Etingof.jordan_holder_equivalent` exposes the complete composition-series equivalence,
`Etingof.jordan_holder_factors` exposes the factor-index bijection and linear equivalences, and
`Etingof.jordan_holder` exposes `n = m`. `Etingof.compositionFactor` is the genuine consecutive
submodule quotient, while `covBy_iff_quot_is_simple` identifies each covering step with a simple
(irreducible) quotient.

The characteristic-zero proof ingredients are covered by character additivity and
`Etingof.characters_linearly_independent`. The footnote's concrete obstruction in characteristic
`p` is directly formalized by `Etingof.character_fin_pi` and
`Etingof.character_pcopies_eq_zero`. The general proof's quotient, intersection, direct-sum,
composition-series-existence, and comparison steps are covered by checked Mathlib infrastructure
and `Etingof.exists_composition_series`; its exact factor-multiset endpoint is exposed by
`Etingof.jordan_holder_factors`.

The discussion's filtration-independent length and greatest strict-chain length are directly
covered by `Etingof.jordan_holder`, `Module.length_compositionSeries`, and
`Etingof.jordanHolder_length_isGreatest_strict`. The remaining use of “length” and
“Jordan-Holder series” is standard terminology attached to `Module.length` and
`CompositionSeries`.

The existing tracker statuses and fields, including the theorem's older `fidelity = partial`
field, are intentionally preserved: this Stage 3.2 change adds only the durable
`claim_coverage` records. The detailed 2026-07-21 theorem review already established full
statement fidelity and a concrete length-two non-vacuity witness.

## Declaration, axiom, and placeholder checks

A temporary `#check` harness importing `EtingofRepresentationTheory.Chapter3` verified every
declaration cited by the new records. `#print axioms` was also run on all thirteen cited project
declarations. Each depends only on the expected standard Lean/Mathlib axioms
`propext`, `Classical.choice`, and/or `Quot.sound`; none depends on `sorryAx` or a project axiom.
The temporary harness was removed after the check.

An exact-provider scan found no `sorry`, `admit`, `sorryAx`, or `axiom` declaration.

## Validation

- exact three-provider build: success (1960 jobs);
- `lake build EtingofRepresentationTheory.Chapter3`: success (8692 jobs; pre-existing warnings);
- `python3 scripts/validate_items.py`: passed, 5721/5721 lines and 583 unique blob IDs;
- `python3 scripts/validate_dependencies.py`: passed, 583 entries and 582 edges;
- `python3 scripts/validate_external_deps.py`: passed, 58 external dependencies;
- `python3 scripts/validate_mathlib_coverage.py`: passed, 58/58 entries represented;
- removing `claim_coverage` from the three scoped records reproduces `origin/main` exactly;
- every non-§3.7 tracker record is byte-for-byte unchanged after canonical JSON projection;
- all three Lean provider files are byte-for-byte unchanged from `origin/main`;
- `jq empty progress/items.json` and `git diff --check`: passed.

# Stage 3.3 proof-integrity review — Chapter 3 §3.7

## Scope and inherited coverage

This stacked review is based exactly on Stage 3.2 draft PR #8080 at commit
`4835e01ce0dfc4e1cf783991be5a8cf363272300`. Reading order gives the three §3.7 catalog
items at indices 159–161, from `Chapter3/Introduction_to_3.7` through
`Chapter3/Discussion_after_Theorem3.7.1`. The strict predecessor is
`Chapter3/Theorem3.6.2`; the strict successor is `Chapter3/Introduction_to_3.8`.

The 28-claim Stage 3.2 inventory is unchanged: nine claims are `formalized`, fifteen are
`covered_elsewhere`, four are `non_formalizable`, and none is a gap. The three exact providers
are:

- `EtingofRepresentationTheory/Chapter3/Theorem3_7_1.lean`;
- `EtingofRepresentationTheory/Chapter3/Discussion_after_Theorem3_7_1.lean`;
- `EtingofRepresentationTheory/Chapter3/Discussion_footnote_3_7_1.lean`.

The introduction has no provider or proof obligation. The footnote provider belongs to the
theorem item, as established by the inherited tracker notes and Stage 3.2 audit.

## Exhaustive proof-integrity audit

The durable `stage3_3` inventories contain only the ten authored declarations: nine on the
theorem item (including the footnote) and one on the discussion item. The introduction is
`not_applicable`; the other two items are `sorry_free`.

The audit itself was deliberately broader. Lean module-origin data exhaustively identified all
12 constants emitted by the exact providers. `Lean.collectAxioms` classified them as follows:

- `[propext, Classical.choice, Quot.sound]` (8):
  `Etingof.compositionFactor`, `Etingof.jordan_holder_equivalent`,
  `Etingof.jordan_holder_factors`, `Etingof.jordan_holder`,
  `Etingof.jordanHolder_length_isGreatest_strict`, `Etingof.trace_diagPi_fin`,
  `Etingof.character_fin_pi`, and `Etingof.character_pcopies_eq_zero`;
- `[propext, Quot.sound]` (4): `Etingof.diagPi`, `Etingof.diagPi_apply`, the generated
  equation theorem `Etingof.diagPi.eq_1`, and the internal proof constant
  `Etingof.diagPi._proof_1`.

Thus all 12 constants are backed by closed Lean terms using only the expected foundational
axioms. None depends on `sorryAx` or a project axiom. The generated equation theorem and internal
proof constant are recorded here and were included in the exhaustive audit, but are correctly
excluded from the durable authored-declaration arrays.

A direct source scan found no `sorry`, `admit`, `proof_wanted`, `sorryAx`, `native_decide`,
`unsafe`, `axiom`, or source-level `opaque` declaration. No proof repair was required.

## Direct-import audit

The three providers contain exactly six direct import statements:

- `Theorem3_7_1.lean`: `Mathlib.Order.JordanHolder` and
  `Mathlib.RingTheory.SimpleModule.Basic`;
- `Discussion_after_Theorem3_7_1.lean`: `Mathlib.RingTheory.Length`;
- `Discussion_footnote_3_7_1.lean`: the earlier local provider
  `EtingofRepresentationTheory.Chapter3.Theorem3_6_2`, `Mathlib.LinearAlgebra.Pi`, and
  `Mathlib.Algebra.CharP.Defs`.

There is no aggregate chapter import, later-section import, or hidden additional project edge.
The imports were audited but intentionally not changed: redundancy testing and minimization are
reserved for Stage 3.4.

## Validation

- `.lake/build` is worktree-local; only `.lake/packages` links to the shared package cache;
- all three exact providers build successfully together (1,960 jobs);
- exhaustive module-origin enumeration and `Lean.collectAxioms`: 12/12 constants clean;
- exact-provider admission/placeholder and direct-import scans: clean;
- exact three-item aggregation: two `sorry_free`, one `not_applicable`, ten distinct authored
  declarations;
- `lake build EtingofRepresentationTheory.Chapter3`: success (8,692 jobs; pre-existing warnings);
- all four repository validators pass;
- removing only `stage3_3` from the three scoped records reproduces the Stage 3.2 base exactly;
- the inherited claim coverage, normalized non-scope tracker projection, dependency maps, and all
  three provider files are unchanged;
- `jq empty progress/items.json` and `git diff --check`: pass.

This PR is limited to Chapter 3 §3.7 and Stage 3.3.

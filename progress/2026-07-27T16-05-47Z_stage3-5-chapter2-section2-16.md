# Stage 3.5 — Chapter 2, §2.16

Completed the Mathlib-quality pass for the exact six-item §2.16 interval, stacked on the Stage 3.4
dependency audit in PR #8070. The section uses sixteen direct providers: one each for Problems
2.16.1, 2.16.2, 2.16.4, and 2.16.5, plus the twelve-file Problem 2.16.3 development.

The prerequisite stages remain complete and unchanged: Stage 3.2 audited claim fidelity,
definition integrity, and nonvacuity; Stage 3.3 certified proof integrity and axioms; and Stage 3.4
audited actual dependencies and imports. The three deferred Problem 2.16.4 classification units
and the two permanent Problem 2.16.5 exhaustive-classification exclusions remain exactly the five
honest omissions recorded by those earlier passes. No placeholder declaration represents them.

## Declaration and documentation audit

- Temporary per-file `#lint+ docBlameThm` ran all 16 default declaration linters plus
  `docBlameThm`: zero findings across 865 named and 720 automatically generated declarations.
- Added 203 missing theorem and instance docstrings across the representation-classification,
  free-Lie quotient, grading, loop-layer, cocycle, characteristic-p, and quantum-group APIs.
- Removed five non-normal simp attributes and made their affected proofs explicit.
- Kept the established source-numbered namespaces and API names under documented,
  declaration-local naming exceptions. The intentionally phantom representation indices on
  `oneDimModule` and `Fam` additionally retain a documented unused-argument exception because
  they distinguish typeclass structures on the same carrier.

## Proof and source-quality cleanup

The cold scoped baseline had 72 warnings; the polished providers have zero. The cleanup replaced
goal-changing `show`, deprecated `push_neg`, flexible `simp`, unused simp arguments and section
variables, unnecessary sequence-focus combinators, an unused parameter, and line/whitespace
issues. Fragile endomorphism-bracket and power-action proofs were rewritten with explicit typed
steps. All pre-existing linter-disable options in scope were removed, and every scoped line is at
most 100 characters.

Manual review found no unstable suggestion tactic, admission, project axiom, opaque declaration,
`native_decide`, diagnostic command, or linter-disable option.

## Imports and axioms

Temporary `#redundant_imports` checks report no transitively redundant import in any provider. An
environment audit selected every constant attributed to the sixteen modules and passed all 1,585
through `Lean.collectAxioms`, including 1,463 exported and 122 private constants. The only
dependencies reported were `propext`, `Classical.choice`, and `Quot.sound`; no declaration depends
on `sorryAx` or another nonstandard axiom.

## Durable status and validation

All six exact items now have `status = proof_polished` and complete Stage 3.5 metadata. The
heading's quality status is correctly `not_applicable`; the five exercise items are `verified`.
Earlier-stage metadata, dependency maps, claim verdicts, and the exact five omissions are
unchanged.

- direct elaboration and a scoped build of all sixteen providers, with zero warnings
- all 17 declaration linters and per-provider redundant-import audits
- exhaustive attributed-constant axiom audit
- `scripts/validate_items.py`
- `scripts/validate_dependencies.py`
- `scripts/validate_external_deps.py`
- `scripts/validate_mathlib_coverage.py`
- exact six-item scope, omission, and non-scope tracker invariance checks
- admission, diagnostic, deprecated-tactic, linter-suppression, and 100-character scans
- `jq empty` on repository JSON and `git diff --check`

`scripts/verify_blobs.py` retains the repository's known derived-overlay `KeyError: 'id'`; this
pass does not alter blobs or those unrelated records. All temporary diagnostic sources and
commands were removed.

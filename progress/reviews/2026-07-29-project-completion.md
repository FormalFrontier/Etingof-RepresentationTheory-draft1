# Project completion review (2026-07-29)

## Completion decision

The mathematical formalization of the book is complete under the repository's
documented scope policy.  Stage 3.4 dependency trimming and Stage 3.5 lint
polishing remain useful post-formalization quality work, but they are not part of
the mathematical completion gate.

Ado's theorem is intentionally excluded.  Its single `proof_wanted (ado)` marker
is approved by metadata and is non-blocking; no other proof placeholder remains.

## Evidence

- `lake build` completed successfully: 9,416 jobs.
- The CI-equivalent per-module build completed successfully: 9,404 jobs.
- `check_proof_placeholders.py --enforce-completion` found zero blocking
  placeholders, one approved Ado marker, zero unapproved markers, and zero
  approval-metadata errors.
- The reconciled exercise ledger contains 102 exercises/problems and 407 claim
  units: 96 are `covered_full`, six are documented scope/correction partials,
  and there are zero untracked gaps.
- The exercise claims comprise 359 formalized units, 23 covered elsewhere, 16
  intentional omissions, eight non-formalizable units, and one source
  correction.
- The item, internal-dependency, and external-dependency validators pass.
- The script test suite passes all ten tests.
- The CI warning ratchet passes with no new warnings; nine stale baseline entries
  were removed after their modules became warning-free.

## Clean-build repairs

The final aggregate rebuild exposed several integration-only defects that did
not appear in isolated section builds.  The audit repaired three local-instance
name collisions, made character evaluation simplification explicit, replaced a
brittle dependent rewrite by a definitional local binding, and narrowly scoped a
typeclass-search allowance for the linear-dual weight-space argument.  The full
root build passes after these repairs.

## Remaining work

There is no remaining non-skipped mathematical content.  Future Stage 3.4/3.5
work may further minimize imports and shrink the existing warning baseline, but
that work is maintenance and polish rather than unfinished book formalization.

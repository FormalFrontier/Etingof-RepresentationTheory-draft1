# Claim-coverage durable-state backfill

Status: prospective staged work under the periodic PLAN status checks; not a
blocker to closing the historical #5140 umbrella.

## Finding

`PLAN.md` now requires a durable `claim_coverage` object on every formalizable
item, but `progress/items.json` currently contains no such object on any of its
593 records.  The existing evidence is substantial but uses older, coarser
fields: 234 records have `fidelity: verified`, and 101 of 102 exercise records
already had an exercise `coverage` state before the #5140 audit repair.

This is the rollout state anticipated by merged PR #5141: missing
`claim_coverage` means "audit pending", not "failed", and existing items must
not be retroactively un-verified.  The latest #5140 maintainer status likewise
uses the named mathematical residuals, not this prospective backfill, as its
closure gate.

This cannot be backfilled honestly by copying `status`, `fidelity`,
`coverage_note`, or a declaration name.  `claim_coverage` is explicitly a
per-conjunct semantic comparison with the source.  Inferring it mechanically
would recreate the exact failure mode that Stage 3.2 steps 6-7 were added to
prevent: a related declaration could be recorded as covering a stronger book
claim.

## Exact record format

Backfilled records should use one object with an ordered claim list:

```json
"claim_coverage": {
  "claims": [
    {
      "claim": "One normalized source claim or conjunct",
      "verdict": "formalized",
      "lean_decl": "Etingof.example"
    },
    {
      "claim": "A claim proved at another source location",
      "verdict": "covered_elsewhere",
      "lean_decl": "Etingof.otherExample"
    },
    {
      "claim": "Historical or motivational prose",
      "verdict": "non_formalizable",
      "reason": "Why no mathematical proposition is asserted"
    }
  ]
}
```

Allowed verdicts are `formalized`, `covered_elsewhere`, and
`non_formalizable`.  The first two require a resolvable `lean_decl`; the last
requires a concrete `reason`.  A dropped or unformalized source conjunct is not
given a success verdict: it must become a derived gap record and an issue under
the existing Stage 3.7 process.

## Bounded work plan

1. **Claim-bearing statements (266 records).** Review theorem, lemma,
   proposition, corollary, definition, example, and remark records in chapter
   batches.  Reuse the existing fidelity reports as evidence, but enumerate the
   source conjuncts again and resolve every named Lean declaration.
2. **Exercises (102 records).** Reuse the exercise coverage-arm reports and
   record sub-parts as separate claims.  Also backfill the 82 missing
   `lean_decl` pointers; a `covered_partial` record must say exactly which
   sub-parts remain.
3. **Prose and remaining formalizable items.** Process discussion and
   introduction records from the deterministic coverage worklist.  Record
   genuinely non-formal prose with reasons instead of manufacturing Lean
   coverage.
4. **Enforcement.** Once a batch is backfilled, extend
   `scripts/validate_items.py` to validate the object shape and declaration or
   reason requirement.  Keep an explicit shrinking list of not-yet-audited
   item IDs.  Turn missing `claim_coverage` into a repository-wide hard error
   only when that list reaches zero; new items must never be added to it.

## Completion criteria

- Every formalizable partition item has a reviewed `claim_coverage.claims`
  list.
- Every `formalized` / `covered_elsewhere` entry names a checked declaration.
- Every `non_formalizable` entry gives a source-specific reason.
- Every uncovered conjunct has a derived record and issue.
- The validator rejects malformed records and any newly added unaudited item.
- The audit reports the claim-coverage total separately from byte coverage,
  exercise coverage, and fidelity coverage.

The periodic PLAN status check can run these batches directly.  Maintainers may
open a dedicated process issue if coordination needs one, but the backfill need
not become a new permanent issue and must not keep #5140 open after its named
actionable residuals are resolved.

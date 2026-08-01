# Stage 3.6 bounded completeness-audit certificate

Final reconciliation date: 2026-08-01.

This certificate closes the bounded audit described in `PLAN.md`. It is a
risk-reduction certificate, not a proof that the formalization contains every
mathematically expressible consequence of the book.

## Coverage arm

- The deterministic and adversarial sweeps covered all 211 prose blobs; the
  detailed worklist, signal classes, and per-wave counts are preserved in
  `coverage-wave-1.md`.
- The two final adversarial passes were dry: wave 3 found no new Chapter 5
  claim, and wave 4 found no new claim in any of the 35 high-risk displayed-math
  blobs. This meets the two-consecutive-dry-wave stopping rule.
- All ten accepted derived claims have an originating coverage issue and a
  sorry-free Lean provider that completed the diagnostic pass. The one legacy record that stores only
  `lean_file` is the GL₂ conjugacy-class-count provider; its complete declaration
  inventory is recorded in that derived item's note.
- The two residual prose gaps discovered during final reconciliation are now
  closed: `Chapter2/Discussion_faithful_example` points to the characteristic-p
  nonfaithfulness and faithful-`repE` theorems, and
  `Chapter3/Discussion_proof_of_Theorem3.10.2` points to the public
  `tensorProductRangeRep` / `tensorProductRangeModule` image-algebra descent.
- Every one of the 102 exercise/problem items has an honest `coverage` field:
  96 `covered_full`, 6 `covered_partial`. The partial units are exactly the
  scope- or source-correction-justified units enumerated in
  `exercise-coverage.md`; there are no untracked exercise gaps.

## Fidelity arm

- All 266 claim-bearing partition items have the normalized verdict
  `fidelity: verified`; no `unchecked`, `gap`, or historical nonstandard verdict
  remains.
- Every fidelity-verified claim-bearing item has a structured
  `claim_coverage` record. The 25 older wave verdicts were migrated by the
  finite, idempotent `scripts/backfill_claim_coverage.py` migration, which
  refuses to overwrite an existing record or bless a non-verified item.
- The former Young-projector prose residual is closed by the existing explicit
  ideal isomorphism `spechtModule_linearEquiv_youngProjectorLeftIdeal` and the
  new public theorem `youngProjector_ne_zero` for the source claim `c_λ ≠ 0`.
- The Chapter 9 wave-9 gap in Definition 9.5.1 was previously repaired by
  restricting linking chains to simple objects and defining blocks through
  Jordan–Hölder factors. Final dry rechecks found no ledger item with a gap or
  missing claim-coverage record; repeating the same deterministic recheck after
  metadata normalization again returned zero. These are the two final dry
  reconciliation passes. Mathematical verdict details remain in the nine
  fidelity-wave certificates.

## Residual risk

The audit deliberately terminates after a fixed full sweep plus two dry
high-risk/reconciliation passes. False negatives remain possible, especially
inside dense expository passages whose claims do not use the mined signal
phrases. Exercise omissions approved in `skipped-exercises.md` remain outside
the release obligation and are reported separately rather than counted as
formalized.

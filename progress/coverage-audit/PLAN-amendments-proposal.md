# Proposed PLAN.md amendments: claim-coverage completeness

Status: DRAFT for Kim's review. Not applied to PLAN.md (off-limits roadmap).

## Why

Two audits (see `exercise-coverage.md`, `prose-claim-seed.md`) found that the
existing claim-coverage controls in Stage 3.1 step 3 and the Stage 3.2 coverage
audit were never executed for prose blobs or exercises:

- 0 / 247 prose items carry the mandated `non_formalizable` status or `reason`
  field; no coverage-audit artifact exists anywhere in the repo.
- 89 candidate formalizable claims sit inside 55 prose blobs with no recorded
  assessment.
- All 102 exercise items are marked `sorry_free`, but only 3 name-match a Lean
  file; the status is vacuously true and tracks nothing.

Byte-coverage is 100% and every numbered statement is an item. The hole is
*claim*-coverage, which the plan already required but did not enforce. The fix
is mostly enforcement of existing stages plus three additions below.

Guiding principle throughout: **byte-coverage and claim-coverage are different
metrics. No report may present one as evidence of the other.**

---

## Amendment 1 (enforcement): make the Stage 3.1/3.2 prose audit auditable after the fact

Stage 3.1 step 3 and the Stage 3.2 coverage audit already specify the right
behaviour. They failed silently because their output lived only in (now-merged)
PR bodies, not in any queryable artifact. Add to **Stage 3.2**:

> The coverage-audit checklist for each item must also be recorded in
> `progress/items.json` on the item itself: a `claim_coverage` object with
> `claims` (the enumerated claims), and for each claim a `verdict` of
> `formalized` (with `lean_decl`), `covered_elsewhere` (with `lean_decl`),
> or `non_formalizable` (with `reason`). An item is not `definition_verified`
> until its `claim_coverage` is present. A periodic check (Amendment 4) fails
> if any formalizable item lacks `claim_coverage`.

This converts the audit from a one-time PR-body note into durable, greppable
state, so a skip is detectable rather than invisible.

---

## Amendment 2 (data model): the `derived` claim-overlay record

Found claims are sub-spans of existing blobs. The Stage 1.6 partition forbids
overlaps, so a found claim cannot be a partition item. Add a separate overlay:

> **Derived items.** A claim discovered inside an existing blob is recorded as an
> item with `type: "derived"` and the following fields:
> - `derived_from`: the parent item id (e.g. `Chapter2/Discussion_faithful_example`)
> - `source_span`: the exact quoted sentence(s) from the blob (provenance, so any
>   reviewer can re-locate the claim)
> - `claim`: a one-line normalized statement of the mathematical content
> - `status`: one of `accepted` (a real gap to formalize), `rejected_duplicate`,
>   `rejected_trivial`, `rejected_nonformal`, `rejected_already_covered`
> - `lean_decl`: the covering declaration, once formalized or located
>
> Derived items are an **overlay on the partition, not part of it**: the Stage 1.6
> contiguity check skips `type == "derived"` entirely. They flow through the normal
> Stage 3.3 work loop once `accepted`.

Rejection-reason taxonomy is mandatory: "not worth it" must name which of the four
rejection statuses applies, so triviality decisions are auditable rather than taste.

---

## Amendment 3 (exercises): a coverage ratchet, not a completion requirement

Exercises are high-value and the book's are excellent, but full coverage must not
be a precondition for declaring the formalization "done". Instead, track honestly
and ratchet. Add a short stage (or fold into the Stage 3.3 status check):

> **Exercise coverage tracking.** Replace the blanket `sorry_free` on exercise
> items with an honest per-exercise `coverage` field: `covered_full`,
> `covered_partial`, `not_started`, or `non_formalizable` (with `reason`), plus
> `lean_decl` pointer(s). Multi-part problems (e.g. Problem 2.15.1 parts (a)-(n))
> are tracked at sub-part granularity via `derived` items, one per part, so partial
> credit and the live frontier are visible.
>
> Report a single monotonic metric in `progress/coverage-audit/exercise-coverage.md`:
> fraction of exercise sub-parts at `covered_partial` or better. This metric may only
> ratchet upward; a status check that lowers it without explanation is a regression.
>
> **The project's "done" criterion does NOT include 100% exercise coverage.** Exercise
> coverage is a tracked, ratcheting goal, reported separately, never a release check.

---

## Amendment 4 (the new stage): Stage 3.7 Completeness Audit (bounded)

A late-stage audit that runs once substantial Lean coverage exists. It is a
**bounded risk-reduction audit, not an open-ended LLM hunt**, and it does not claim
to prove completeness.

> ### Stage 3.7: Completeness Audit
>
> Runs after Stage 3.5 has covered most items. Three steps, in order:
>
> 1. **Deterministic pre-pass.** Mine every prose and exercise blob for high-yield
>    claim signals ("(check it!)", "well-defined", "is faithful/simple/irreducible",
>    "does not depend on", "if and only if", "this defines", dimension formulas,
>    displayed equations in discussion/remark/introduction). Output a seed list of
>    candidate claims with provenance. Cheap, explainable, re-runnable. (Tooling and
>    a first seed list already exist under `progress/coverage-audit/`.)
>
> 2. **Per-claim coverage check.** For each candidate, an agent decides
>    `covered_elsewhere` / `genuine_gap` / `non_formalizable` against the *actual*
>    Lean (comparing declarations, signatures, and docstrings, not just names, since
>    coverage is frequently folded into a neighbouring theorem). Genuine gaps become
>    `accepted` derived items (Amendment 2) with GitHub issues; the rest are recorded
>    with a rejection status. Use a different model for this judge than for the finder,
>    to reduce shared blind spots.
>
> 3. **Bounded adversarial sweep.** For semantically-phrased claims the keyword pass
>    misses, run independent adversarial finders over the high-risk blobs (those with
>    displayed math or construction language). Each finding passes the same per-claim
>    judge before becoming a derived item.
>
> **Termination is a bounded audit certificate, not a completeness proof.** Record in
> `progress/coverage-audit/completeness-audit-wave-N.md`: which blobs were swept, which
> signal classes were checked, how many independent final sweeps returned zero accepted
> claims (target: 2), and an explicit statement that residual risk remains. "Loop until
> dry" is an operational stopping heuristic inside a fixed budget, never a headline
> claim of completeness.
>
> **Output:** new `derived` items in `progress/items.json`; GitHub issues for accepted
> gaps; the audit certificate file.

---

## Amendment 5 (regression guard): extend the Stage 3.3 periodic status check

Add one bullet to the every-50-PRs status check so the prose/exercise skip cannot
recur silently:

> - **Claim-coverage regression check.** Verify every formalizable item has a
>   `claim_coverage` record (Amendment 1) and every exercise has a `coverage` field
>   (Amendment 3). Any item missing these is a finding and must become an issue.

---

## Amendment 6 (statement integrity): an enforced anti-vacuity check

The per-claim check (step b) incidentally found that `sorry_free` is being used for
statements that are vacuous `True` stubs (16 across 13 files, including the induced
representation Definition 5.8.1). A sorry-free build proves nothing if the statements
are `True`. Add a required check, runnable standalone and folded into the Stage 3.3
periodic status check:

> **Statement-integrity (anti-vacuity) check.** Scan all item `.lean` files for:
> (a) theorem/lemma/example conclusions that are `True` (or otherwise trivially provable
>     placeholders); (b) `True` used as a hypothesis; (c) definitions whose data is `sorry`.
> Any hit is a finding. The item's status must reflect it: introduce a status
> `statement_vacuous` (distinct from `sorry_free`), and never let a `True`-stub item be
> reported as formalized. Reconcile with the existing `needs_statement` and
> `has_true_hypothesis` fields, which currently track this only partially.
>
> **`sorry_free` must mean "real statement, real proof."** A vacuous-but-sorry-free item is
> a regression, not a completion. The project's headline progress metric must exclude
> `statement_vacuous` and `needs_statement` items from the "formalized" count.

This is the single most important change: it makes the progress numbers honest. Today a
`True := by trivial` item is indistinguishable from a genuine sorry-free proof in the
status tracking.

## What this is NOT

- Not a re-run of Stage 1.6 structure analysis (the partition is correct).
- Not a claim that the audit proves completeness (it reduces risk and tracks it).
- Not a 100%-exercise-coverage release requirement.

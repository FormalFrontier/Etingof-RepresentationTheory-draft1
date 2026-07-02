# Execute a Review Work Item

You are a **review** session. Your job is to claim and execute a pre-planned review
work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to review sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label review` to find work for this session type.

## Review Focus Areas

Each session should pick **one or two** focus areas and go deep, rather than
superficially covering everything. The issue body will specify what to focus on.
Rotate through these areas across sessions:

**Refactoring and code improvement** (top priority):
- Can code be simplified? Are there redundant steps?
- Would extracting a function/lemma improve readability or enable reuse?
- Are there generally useful constructions worth upstreaming?

**Slop detection**:
- Dead code, duplicated logic, verbose comments, unused imports
- Other signs of AI-generated bloat

**Idioms and best practices**:
- Are newer APIs or language features being used where appropriate?
- Opportunities to improve type safety, remove unsafe operations

**Toolchain**:
- Check if a newer stable toolchain release is available; upgrade if tests pass

**File size and organization**:
- Files over 500 lines are candidates for splitting; never let a file grow past 1000

**Security**:
- Check for new issues in recent code, verify past fixes

## Fidelity-audit review items (Stage 3.7 sweep, epic #5338)

Some `review` issues are fidelity audits, not code-improvement passes. These ask you
to set each item's `fidelity` field in `progress/items.json` to `verified` or `gap`
by applying PLAN.md Stage 3.2 steps 6–7 (anti-vacuity, then conjunct-by-conjunct
no-silent-weakening) against the item's blob, judged with a **different model** than
formalized it and calibrated on #5322/#5323/#5326. Record findings in
`progress/coverage-audit/fidelity-wave-N.md`. A `gap` opens a `bug`+`review` repair
issue linked to the audit issue.

- **Re-audit `gap` items whose repair issue has closed with a merged PR** — a closed
  repair issue is NOT proof of faithfulness. Repairs are sometimes merged having added
  the object but silently dropped a conjunct (seen with Q8 #5632/#5708: 2-dim rep built,
  but irreducibility and the four 1-dim reps still missing → stayed a gap under new
  issue #5831). Re-run steps 6–7 against the current Lean before flipping to `verified`.
- **Cross-check sibling items formalized in one PR batch** against each other — a
  divergence (e.g. two of three parallel examples prove `Simple` and the third does not)
  is a reliable tell that the odd one out's repair is incomplete.
- **Normalize non-schema `fidelity` values** (e.g. `ok`) to `verified`/`gap`, and
  reconcile stale `status` (e.g. a `proof_partial` item that is actually sorry-free) by
  checking `lake build` — that rot is separate from `fidelity`.

## Updating Skills

When you discover a recurring pattern or encounter a situation not covered by
existing skills, update the relevant skill file or create a new one.

## Reflect

Run `/reflect` before finishing.

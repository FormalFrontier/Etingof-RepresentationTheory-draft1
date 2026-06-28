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

## Fidelity-audit issues (Stage 3.7, epic #5338)

If your issue is a fidelity sweep or an adjudication of `unsure` verdicts, read the
latest `progress/coverage-audit/fidelity-wave-*.md` for calibration, then for each item
re-read its blob + Lean declaration (different model than formalized it) and resolve to
`verified` or `gap`. Recording convention (do not rediscover from git):

- **In `progress/items.json`**, set on the item: `fidelity` (`verified`/`gap`),
  `fidelity_note` (your reasoning), `fidelity_decl` (the declaration name, or
  `(none found)`), and for gaps `fidelity_issue: <N>`. Leave `status`/`sorry_free` as-is;
  the project metric is `min(sorry_free fraction, fidelity-verified fraction)`, so a `gap`
  is excluded from the fidelity count without touching the sorry arm.
- **Open one issue per gap.** Two kinds:
  - *No declaration but formalizable claim* → title `Missing formalization: <ItemID>`,
    labels `review,agent-plan`.
  - *Declaration present but vacuous/strictly weaker* → title `Fidelity gap: <ItemID>`,
    labels `bug,feature,agent-plan`.
  Body: header citing epic #5338 / parent issue + Item / Lean decl / Why flagged / Dropped
  / Fix lines (mirror an existing wave-1 issue, e.g. #5357 or #5366).
- **Calibration:** absence is `verified` (not a gap) when the content needs out-of-scope
  machinery (manifolds, analysis) or is a hard low-value infinite-dim narrative; it is a
  `gap` when the claim is clean, self-contained, and formalizable at this level. A
  definition that constructs the right object via a provably-equivalent encoding is
  faithful; a faithful statement whose *proof* has a `sorry` is still `verified` (that is
  the sorry arm, not fidelity).

## Updating Skills

When you discover a recurring pattern or encounter a situation not covered by
existing skills, update the relevant skill file or create a new one.

## Reflect

Run `/reflect` before finishing.

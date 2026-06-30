# Execute a Review Work Item

You are a **review** session. Your job is to claim and execute a pre-planned review
work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to review sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label review` to find work for this session type.

## Fidelity-audit issues are content fixes, not refactors

Many `review`-labelled issues (e.g. from the fidelity sweep, epic #5338) are
**not** code-quality reviews — they are audit findings that a Lean item is
weaker than, or absent versus, the book. The body reads "Finding: ... gap ...
Re-confirm before fixing." For these: (1) re-confirm each gap against the blob
and the Lean file, (2) **fix** the Lean content (strengthen/add the
statement+proof), not just comment on it. Treat them with the
`agent-worker-flow` execute/verify/publish loop, and the lean-formalization
skill, exactly like a `feature`. If a finding has several gaps and one is large
new infrastructure (a from-scratch algebra, a first-of-its-kind `Ext` proof),
close the tractable gaps and ship `coordination create-pr <N> --partial`,
linking the dedicated issue for the residual rather than stubbing it.

## Review Focus Areas

If the issue is a genuine code-quality review (not a fidelity fix above), each
session should pick **one or two** focus areas and go deep, rather than
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

## Updating Skills

When you discover a recurring pattern or encounter a situation not covered by
existing skills, update the relevant skill file or create a new one.

## Reflect

Run `/reflect` before finishing.

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

## Fidelity-audit reconciliation (Stage 3.7 sweep issues)

When a fidelity-audit issue's items already carry verdicts from a prior
partial pass (common: an earlier wave set `verified`/`gap`/`faithful` and
opened repair issues but never wrote a wave certificate), do **not** trust
the existing verdicts:

- **Re-audit the previously-`verified` items too**, not just `gap`/`unchecked`
  ones. Prior passes miss real gaps — re-auditing routinely refutes some
  `verified` items (e.g. a multi-part example/definition whose second clause or
  a named sub-notion is absent, or a docstring that promises more than the decl
  asserts).
- **Reconcile merged repairs against the *current* Lean.** For each `gap` whose
  repair issue has closed/merged, read the post-repair file: flip to `verified`
  only if the fix is genuinely faithful and non-vacuous, and drop the stale
  `fidelity_issue`/`fidelity_note`.
- **Reopen (or open) a repair issue for every residual gap.** A partial repair
  that merged and closed its issue still leaves an open gap — reopen it with a
  residual-scope comment, or open a fresh `bug`+`review` issue linked to the
  audit issue.
- **Normalize non-standard labels** (`faithful` → `verified`) so the final
  state is only `verified` or `gap`.
- Judge with a **different model** than the author, and use parallel
  sub-auditors + adjudication for scale. Write the wave certificate to
  `progress/coverage-audit/fidelity-wave-N.md`.

## Updating Skills

When you discover a recurring pattern or encounter a situation not covered by
existing skills, update the relevant skill file or create a new one.

## Reflect

Run `/reflect` before finishing.

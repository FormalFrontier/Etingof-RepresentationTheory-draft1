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

## Verifying sorry-freeness (fidelity audits)

`grep -c sorry` is unreliable for "is this file sorry-free?": it counts the
substring `sorry-free` inside comments, so a fully-complete file can report a
large nonzero count (e.g. 10 comment mentions → looks like 10 sorries). Always
confirm real sorries with `grep -n sorry <file> | grep -v sorry-free`, and treat
`#print axioms <decl>` (no `sorryAx` in the list) as the ground truth for whether
a declaration is genuinely sorry-free. Do not trust a stale sorry-count from the
issue body — re-check it.

To run `#print axioms`, **append the `#print axioms <decl>` lines to the end of
the target source file** and run `lake env lean <that-file>` (restore the file
after). Do NOT create a separate scratch file that `import`s the target module and
run `lake env lean` on it — loading a project olean that way can demand a transitive
olean the local build never produced and fail with a spurious
`object file '…/SomeOtherModule.olean' … does not exist`, even for a module the
target does not import. Running against the actual source file only needs the
target's own already-built dependency oleans, so it works after a successful
`lake build EtingofRepresentationTheory.<Module>`.

## Completing the Review

Post your report as a comment on the review issue. Then close the issue yourself —
a review's deliverable is the report, not a code change, so there is usually **no PR**
to swap `claimed` → `has-pr`, and an unclosed issue would stay stuck in `claimed`:

- **No defect found:** `gh issue close <N> --comment "Review complete — PASS. See report above."`
- **Defect found:** open a fix PR (`coordination create-pr <N>` — this closes the issue on
  merge) **or** a follow-up `feature` issue for the fix, then close the review issue with a
  link to it. Do not leave the review issue open waiting on a human.

`coordination create-pr` builds the PR body itself from the commit (`Closes #N` +
session + commit subjects); it does **not** read a piped/`--body` body. When the issue
requires the per-check verdict *in the PR body*, either put that reasoning in the commit
message or add it afterward with `gh pr edit <N> --body-file <file>`.

Any progress-file commit lives on your branch; there is no need to push or PR it for a
report-only review.

## Updating Skills

When you discover a recurring pattern or encounter a situation not covered by
existing skills, update the relevant skill file or create a new one.

## Reflect

Run `/reflect` before finishing.

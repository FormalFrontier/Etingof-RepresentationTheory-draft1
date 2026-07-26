# Execute a Review Work Item

You are a **review** session. Your job is to claim and execute a pre-planned review
work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to review sessions.

## Before You Start: Verify the Worktree Is Not Stale

Pod overwrites `.claude/commands` and `.claude/skills` with a copy bundled inside the
installed dev-pod package at the start of *every* session — see #7935 for the call site.
That bundled copy is frozen at dev-pod install time and so is older than `main`, which
means you are very likely running on guidance that has since been superseded, and a later
`git add -A` would revert it on `main`. Run this unconditionally, before Step 1:

```bash
git status --short
git diff --numstat HEAD -- .claude/
```

Any pure-deletion lines under `.claude/` are pod's bundled copy, not your work. A
`SessionStart` hook (`.claude/hooks/restore-claude-config.sh`) normally restores them before
you get here, so `git status` may already be clean. **That does not mean the text you were
served is current**: the command file and the skill are both snapshotted at session start,
before the hook's writes become visible to the loader (measured directly in #7935). Restore
anything the hook left with `git checkout HEAD -- .claude/`, and reload the
`agent-worker-flow` skill and this command either way, since the copies you loaded were the
old ones.

Use `Read`, not the Skill tool: re-invoking a skill that is already loaded answers
"instructions unchanged" and hands back the stale copy from session start, so it silently
does nothing. (Earlier revisions of this file advised the reverse.)

Cheaper still, the `gitStatus` block in your system prompt already lists these files at
session start — five modified files under `.claude/` there is the signal, and it costs no
tool call to notice.

## Claiming Your Issue

Use `coordination list-unclaimed --label review` to find work for this session type.

## Read the Comments Before Deciding the Deliverable

A review issue's body describes the world as it was when the issue was *filed*. If the
issue was later closed and reopened, the reopening comment — not the body — defines the
live scope, and **a `review` issue can carry construction scope**. When it does, the
deliverable is a PR with real `.lean` work, not a report, and "Completing the Review"
below does not apply.

Check before you start:

```bash
gh issue view <N> --json stateReason,comments \
  --jq '.stateReason, (.comments[] | "--- \(.createdAt) \(.author.login)\n\(.body)")'
```

`stateReason == "REOPENED"` is the reliable tell. Two softer ones: a linked *merged* PR
that already performed the audit named in the body, and a body whose factual claims about
the repo no longer hold. Any of the three means re-derive the scope from the comments.

Do not pattern-match on a `Reopening:` prefix — reopening comments are written in prose.
#7276 was filed as a report-only Stage 3.7 fidelity audit of `Chapter4/Problem4_12_5.lean`,
its audit ran and merged as #7300, and it was then reopened with a comment beginning
"Reopening because the audit treated unformalized existence/model identification as
sufficient." The new scope was to *construct* the icosahedral vertex/face/edge actions and
prove transitivity/stabilizer facts — hours of Lean work, still wearing a `review` label,
with the body still describing the finished report-only audit. A session that read the body
and skipped the comments would have written a second report on an already-audited file and
closed the issue, leaving the real gap open.

This is not rare: as of 2026-07-26, 17 open `agent-plan` issues have
`stateReason == "REOPENED"`, seven of them unclaimed.

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

**Beware a false `sorryAx` from the append-to-source method.** `lake env lean`
re-elaborates the whole source from scratch, and for some files that re-elaboration
is nondeterministically flaky (e.g. `synthInstanceFailed` or `rewrite failed` on a
line that compiles fine under `lake build`). Lean fills a failed elaboration with
`sorryAx`, so a genuinely sorry-free decl can be reported as depending on `sorryAx`
— a false positive. Tell it apart from a real sorry: if the same `lake env lean`
run prints **any `error:`** on lines of the target decl (or its helpers), the
`sorryAx` is an elaboration artifact, not a real sorry. To confirm, cross-check
against the built oleans: after `lake build EtingofRepresentationTheory.<Module>`
succeeds, create a scratch file that only `import`s the module and runs
`#print axioms` there, then `lake env lean` it. Because every olean already exists,
the "object file does not exist" hazard above does not fire, and the axiom list is
computed from the compiled olean rather than a fresh re-elaboration — this is the
authoritative result. (Observed on `Chapter3/Problem3_9_2.lean`, audit #7375.)

## Editing `progress/items.json` (coverage-arm audits)

Coverage-arm audits record verdicts by editing one entry in
`progress/items.json` — a single ~8000-line JSON array shared by every session.
When you rewrite it programmatically (e.g. Python `json.dump`), **match the
existing serialization exactly or you will reformat the whole file** into a
spurious multi-thousand-line diff that is merge-conflict bait and hides your real
change. The file uses `indent=2`, `ensure_ascii=False` (unicode kept literal, not
`\uXXXX`), and a trailing newline. Concretely:

```python
json.dump(items, open(p, "w"), indent=2, ensure_ascii=False)
open(p, "a").write("\n")   # restore trailing newline json.dump omits
```

Then **verify the diff is localized** before committing:
`git diff --stat progress/items.json` should report a handful of changed lines,
not thousands. If it is large, `git checkout progress/items.json` and redo with
the right format. Prefer editing the single target entry over touching others.

## Completing the Review

**This section assumes the report-only case.** If the comments re-scoped the issue to
construction work (see "Read the Comments Before Deciding the Deliverable"), ignore it:
finish the Lean work and publish with `coordination create-pr <N>` like a feature session.

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

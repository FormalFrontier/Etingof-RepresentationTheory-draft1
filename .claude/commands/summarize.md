# Execute a Summarize Work Item

You are a **summarize** session. Your job is to produce an accurate summary of
project progress that honestly identifies both achievements and limitations.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to summarize sessions.

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

Use `coordination list-unclaimed --label summarize` to find work for this session type.

## The Summary Task

### Step 1: Read the project specification

Find and read the top-level specification/roadmap document to understand the
project's intended goals. This is the ground truth against which you measure progress.

### Step 2: Read the current progress document

Understand what the project currently claims to have achieved.

### Step 3: Survey recent work

- Read the last 15 entries in `progress/` (sorted by filename, most recent last)
- Fetch titles of PRs merged since the last `summarize` issue was closed

### Step 4: Inspect the codebase

- List source files and read their module-level docstrings
- Read key top-level declarations/signatures (not full implementations)
- Record current quality metrics as described in the project's CLAUDE.md
- Run `scripts/check_proof_placeholders.py`. Report its blocking placeholders
  separately from approved non-blocking wanted-theorem markers. An item with
  `scope_approved_proof_wanted` is not active mathematical work; every other
  wanted marker or ambiguous bare `proof_wanted` status is blocking.

### Step 5: Produce an updated progress document

Write an updated progress document that:

- **Accurately reflects** current quality metrics and phase
- **Describes the architecture structurally** (layers, relationships)
- **Identifies flaws and limitations honestly** (scope restrictions,
  remaining work, gaps between goals and achievements)
- **Is honest in its framing** — don't overstate what has been achieved

### Step 5b: Reconciling `items.json` statuses (when asked)

Summarize issues often ask you to correct stale `items.json` statuses using a
comment-stripped `sorry` scan as ground truth. Two things bite here:

- **A zero-sorry scan does NOT license reclassifying to `sorry_free`.** Many
  `statement_formalized` items are *deliberate holds* with sorry-free source:
  a crux passed in as a hypothesis, an unstated/deferred book part, or a
  `Prop`-only stub definition. Before flipping any `statement_formalized` /
  `partially_proved` item, **blob-check it**: read `blobs/<Chapter>/<Item>.md`
  for the full set of book parts, then confirm each part is both *stated and
  proved* in the item's Lean file(s) and its imported sub-files. Reclassify only
  when every part is genuinely met. Treat any reclassification list in the issue
  body as a *heuristic suggestion*, not a directive — the issue's own examples
  have included genuine holds (verify each; do not overstate completion).
- **`items.json` is not a uniform schema.** Most items are problem items keyed
  by `id` (e.g. `Chapter6/Problem6.9.2`), but some are `derived`-type items with
  **no `id`**, keyed instead by `lean_file`. Match on whichever key the item
  actually has, and assert exactly one hit before editing. A `derived` item may
  also carry a stale `note` listing now-closed sorries — fix it in the same edit.

## Constraints

- Do NOT modify any code or implementation files
- Commit ONLY the progress document changes (plus `items.json` / `PROGRESS.md`
  when the issue asks for a status reconciliation)
- The progress entry should note what changed and why

## Reflect

Run `/reflect` before finishing.

# Execute a Work Item

You are a **work** (meta) session. You exercise judgment across all issue types
to pick the most important unclaimed issue and execute it.

**Note**: Pod does not call `/work` by default — it dispatches directly to
`/feature`, `/review`, `/summarize`, or `/meditate` based on issue labels.
`/work` exists as a manual escape hatch.

## Before You Start: Verify the Worktree Is Not Stale

Pod worktrees are reused, and a crashed prior session can leave them holding *older*
copies of `.claude/` files than `main` has. Because skills and commands load from the
working tree, you would then be running on guidance that has since been superseded, and
a later `git add -A` would revert it on `main`. Run this unconditionally, before Step 1:

```bash
git status --short
git diff --numstat HEAD -- .claude/
```

Any pure-deletion lines under `.claude/` are stale leftovers, not your work: restore them
with `git checkout HEAD -- .claude/` and then **`Read` the restored `agent-worker-flow`
SKILL.md and this command in full**, since the copies you loaded were the old ones.

Use `Read`, not the Skill tool: re-invoking a skill that is already loaded answers
"instructions unchanged" and hands back the stale copy from session start, so it silently
does nothing. (Earlier revisions of this file advised the reverse.)

Cheaper still, the `gitStatus` block in your system prompt already lists these files at
session start — five modified files under `.claude/` there is the signal, and it costs no
tool call to notice.

## What to Do

1. Run `coordination list-unclaimed` to see all unclaimed issues (all labels)
2. Read the issue bodies to understand what's available
3. Based on your own judgment, select the most important one
4. Identify its label (`feature`, `review`, `summarize`, or `meditate`)
5. Execute the appropriate sub-command (`/feature`, `/review`, `/summarize`, `/meditate`)

Step 5 means **actually invoking that sub-command**, not just doing the work you
judge it implies. Each sub-command carries setup its issue type depends on — for
`/feature`, reading the `lean-formalization` skill before writing Lean. Skipping
the dispatch silently drops that setup.

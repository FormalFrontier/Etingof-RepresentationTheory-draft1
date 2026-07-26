# Execute a Work Item

You are a **work** (meta) session. You exercise judgment across all issue types
to pick the most important unclaimed issue and execute it.

**Note**: Pod does not call `/work` by default — it dispatches directly to
`/feature`, `/review`, `/summarize`, or `/meditate` based on issue labels.
`/work` exists as a manual escape hatch.

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

Reload by `Read`ing those paths. **Do not use the Skill tool for this**: it caches per
session and answers an already-loaded skill with `instructions unchanged` without re-reading
the file, so the restored content never reaches you and the "unchanged" reply tells you
nothing about what is on disk.

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

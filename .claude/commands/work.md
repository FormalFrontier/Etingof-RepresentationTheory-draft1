# Execute a Work Item

You are a **work** (meta) session. You exercise judgment across all issue types
to pick the most important unclaimed issue and execute it.

**Note**: Pod does not call `/work` by default — it dispatches directly to
`/feature`, `/review`, `/summarize`, or `/meditate` based on issue labels.
`/work` exists as a manual escape hatch.

## Before anything else: check the worktree is not stale

Pod reuses worktrees, and a killed session can leave uncommitted **deletions** of
tracked `.claude/` files. Skills and commands load from the working tree, so a
truncated `SKILL.md` means you silently run the whole session on an old copy of the
guidance and never see the parts that were added since. Run this **before** invoking
any skill:

```bash
git status --porcelain
wc -l .claude/skills/agent-worker-flow/SKILL.md
git show origin/main:.claude/skills/agent-worker-flow/SKILL.md | wc -l
```

If the counts differ, or `git status` shows modified `.claude/` files you did not
write, `git checkout -- .claude/` first, then invoke the skill. The skill carries the
same check, but that copy only reaches an agent who already has the full file — which
is exactly the agent who does not need it. This is why the check lives here too.

(2026-07-25, session `444393c8`: arrived with 291 lines deleted across
`agent-worker-flow/SKILL.md`, `commands/review.md` and `commands/summarize.md`,
invoked the skill before looking, and so missed the Step 7 rules on replacing
`create-pr`'s placeholder PR body and on never running `gh pr merge --auto` — then
broke both.)

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

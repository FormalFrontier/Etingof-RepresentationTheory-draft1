# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

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

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Executing Implementation Work

**Before writing any Lean, read the `lean-formalization` skill.** It is a long
accumulated record of this project's traps, and most of them cost a build cycle
each to rediscover. Search it for the vocabulary of your item (the ambient
structure, the Mathlib API, the tactic that just failed) rather than reading it
top to bottom. A rewrite or `simp` that fails to find a pattern the goal visibly
contains is almost always one of the documented instance/elaboration traps, not
a mistake in your proof — check the skill before rewriting the proof.

Follow the plan's deliverables. For new implementations, follow the development
cycle described in the project's CLAUDE.md.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

## Reflect

Run `/reflect` before finishing.

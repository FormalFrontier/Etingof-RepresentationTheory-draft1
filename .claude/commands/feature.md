# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

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
with `git checkout HEAD -- .claude/` and then reload the `agent-worker-flow` skill and this
command, since the copies you loaded were the old ones.

Reload by `Read`ing those paths. **Do not use the Skill tool for this**: it caches per
session and answers an already-loaded skill with `instructions unchanged` without re-reading
the file, so the restored content never reaches you and the "unchanged" reply tells you
nothing about what is on disk.

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Executing Implementation Work

**Before writing any Lean, read the `lean-formalization` skill** — and don't just
read the top: it is thousands of lines of accumulated traps, so `grep` it for the
file, chapter item, and Mathlib types you are about to touch (e.g.
`grep -n 'Problem2_16_3\|LieSubalgebra' .claude/skills/lean-formalization/SKILL.md`).
Most items already have a section naming the exact instance/tactic trap that will
otherwise cost you a build cycle to rediscover. A rewrite or `simp` that fails to
find a pattern the goal visibly contains is almost always one of those documented
instance/elaboration traps, not a mistake in your proof — check the skill before
rewriting the proof.

Follow the plan's deliverables. For new implementations, follow the development
cycle described in the project's CLAUDE.md.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

## Reflect

Run `/reflect` before finishing.

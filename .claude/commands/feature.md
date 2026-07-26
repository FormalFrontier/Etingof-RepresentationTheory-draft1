# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

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

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Executing Implementation Work

**Before writing any Lean, read `.claude/skills/lean-conventions/SKILL.md` in full.**
It is deliberately short and holds the house rules every Lean session
needs: the build commands, the lint-clean policy and the exact `omit`/`set_option`
ordering, import practice, and the non-negotiables. Sessions that skip it spend build
cycles re-deriving the same handful of rules. Read it with `Read`, not the Skill tool.

**Then use the `lean-formalization` skill as a reference** — do not read it top to
bottom: it is thousands of lines of accumulated traps, so `grep` it for the
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

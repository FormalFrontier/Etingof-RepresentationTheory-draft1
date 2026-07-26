# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Executing Implementation Work

**Before writing any Lean, read the `lean-formalization` skill** — and don't just
read the top: it is thousands of lines of accumulated traps, so `grep` it for the
file, chapter item, and Mathlib types you are about to touch (e.g.
`grep -n 'Problem2_16_3\|LieSubalgebra' .claude/skills/lean-formalization/SKILL.md`).
Most items already have a section naming the exact instance/tactic trap that will
otherwise cost you a build cycle to rediscover.

Follow the plan's deliverables. For new implementations, follow the development
cycle described in the project's CLAUDE.md.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

## Reflect

Run `/reflect` before finishing.

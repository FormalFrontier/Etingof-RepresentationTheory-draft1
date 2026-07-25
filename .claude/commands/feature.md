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

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

Follow the plan's deliverables. For new implementations, follow the development
cycle described in the project's CLAUDE.md.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

### Phase 3 Formalization

When working on Lean formalization items, read the `lean-formalization` skill
for the translate/scaffold/prove workflow, tactic selection, and Aristotle
escalation protocol. Key points:

- **One tactic at a time** — check diagnostics after each step
- **Verify Mathlib declarations exist** before using them (`#check`)
- **Escalate to Aristotle** after 2-3 serious failed proof attempts
- **Never commit `admit`** — only use in temporary Aristotle submission files

## Reflect

Run `/reflect` before finishing.

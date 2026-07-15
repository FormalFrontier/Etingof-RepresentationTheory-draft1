# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Check for Already-Landed Work First

Statement-pass and formalization issues frequently go **stale**: their exact
deliverables land via *other* PRs between issue creation and your claim. Before
writing any code, cheaply confirm the work is still needed:

- Check `progress/items.json` status for each item id the issue lists.
- Check whether the target `.lean` files already exist and are wired into the
  chapter aggregator (`grep` the item's file in `Chapter<N>.lean`).
- If already present, confirm with `git log origin/main -- <file>` and a chapter build.

If every deliverable is already `statement_formalized`/present on `main`, the
issue is **complete, not skippable**. Close it with `gh issue close <N> --comment`
pointing at the merged PRs (per the worker skill's "no code changes" path) — do
**not** `coordination skip` (that routes to replan for work that no longer exists).

## Then Confirm Dependencies Actually Landed (assembly/wiring issues)

`check-blocked` unblocks an issue once its `depends-on` issues are **closed** — but a
closed issue is **not** the same as a merged PR. An issue can be closed while its PR is
still open (conflicted, in repair, or closed without merging), so its theorems are **not on
`main`**. If your issue *references lemmas from dependency issues* (assembly, "wire together",
"replace the sorry by chaining #A/#B/#C"), before writing code confirm each referenced symbol
actually exists on `main`:

```bash
grep -rn "<Lemma.name>" EtingofRepresentationTheory/   # or: lake build <the dep's file>
```

If a dependency's theorem is missing (only in an open/conflicted PR), you cannot reference it —
`coordination skip <N>` with a reason naming the missing symbol and the open PR, so a planner
re-blocks on that PR landing. Do not scaffold a duplicate of the dependency's theorem.

## Executing Implementation Work

Follow the plan's deliverables. For new implementations, follow the development
cycle described in the project's CLAUDE.md.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

## Reflect

Run `/reflect` before finishing.

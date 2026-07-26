---
name: agent-worker-flow
description: Standard claim/branch/verify/publish workflow for pod agent sessions. Read this skill at the start of any feature, review, summarize, or meditate session.
allowed-tools: Bash, Read, Glob, Grep
---

# Standard Worker Flow for Pod Agent Sessions

This skill covers the shared workflow used by all pod worker agents.
Session-specific commands reference this skill rather than duplicating it.

## Step 0: Check you are reading the current skill (do this first)

Reused worktrees keep arriving with `.claude/` guidance deleted, and skills load from
the working tree — so the copy you are reading may be a stale revision with exactly the
guidance you need cut out. Run this **before Step 1**, whether or not anything looks wrong:

```bash
git status --short
wc -l .claude/skills/agent-worker-flow/SKILL.md
git show HEAD:.claude/skills/agent-worker-flow/SKILL.md | wc -l
```

If the counts differ: save the diff (`git diff > /tmp/<uuid>-stale.patch`), restore with
`git checkout HEAD -- .claude/`, then **`Read` the restored `SKILL.md` in full** and start
over from Step 1. Do the same for your `/command` file.

**Re-invoking the Skill tool does not work for this** — it answers "already loaded above;
instructions unchanged" and hands back the stale copy it loaded at session start, without
re-reading the file you just restored. Treat that "unchanged" reply as telling you nothing
about the file on disk; `Read` is the only way to see the restored text. (Earlier revisions
of this file said the opposite. 2026-07-26, #7873: a session followed that advice, saw
"unchanged" after restoring 477 deleted lines, and only got the current guidance because it
fell back to `Read`.)

**The earliest signal is free and arrives before any tool call**: the `gitStatus` block in
your system prompt lists modified files at session start. Five modified files under
`.claude/` there means a stale worktree — act on it *then*, not after you have already
chosen an issue and started working on it against guidance that may be missing the check
you needed.

This check lives at the top of the file on purpose. The fuller treatment is in Step 2 under
"If the branch already exists", but every observed truncation left lines 1-70 intact while
cutting blocks further down — so an instruction placed there is one a stale session never
sees, and only this one is reliably reachable. (2026-07-25: four worktrees that day arrived
with 169, 279, 193 and 209 lines of `.claude/` guidance deleted and nothing added. Three ran
to completion on the old copy; the fourth caught it at Step 2 but only re-read the restored
skill at the end of the session, after already publishing.)

## Coordination Reference

The `coordination` script handles all GitHub-based multi-agent coordination.
Session UUID is available as `$POD_SESSION_ID` (exported by `pod`).
The `gh` CLI defaults to the current repo, so `--repo` is not needed.

| Command | What it does |
|---------|-------------|
| `coordination orient` | List unclaimed/claimed issues, open PRs, PRs needing attention |
| `coordination plan [--label L] "title"` | Create GitHub issue with agent-plan + optional label; body from stdin |
| `coordination create-pr N [--partial] ["title"]` | Push branch, create PR closing issue #N, enable auto-merge, swap `claimed` → `has-pr`. With `--partial`: adds `replan` label. |
| `coordination claim-fix N` | Comment on failing PR #N claiming fix (30min cooldown) |
| `coordination close-pr N "reason"` | Comment reason and close PR #N |
| `coordination list-unclaimed [--label L]` | List unclaimed agent-plan issues (FIFO order); optional label filter |
| `coordination queue-depth [L]` | Count of unclaimed issues; optional label for per-type count |
| `coordination claim N` | Claim issue #N — adds `claimed` label + comment, detects races |
| `coordination skip N "reason"` | Mark claimed issue as needing replan — removes `claimed`, adds `replan` label |
| `coordination add-dep N M` | Add `depends-on: #M` to issue #N's body; adds `blocked` label if #M is open |
| `coordination check-blocked` | Unblock issues whose `depends-on` dependencies are all closed; remove orphan `blocked` from issues whose body has no `depends-on:` lines |
| `coordination check-has-pr` | Remove orphan `has-pr` from open issues that have no currently-open PR closing them (post audit comment) |
| `coordination release-stale-claims [SECS]` | Release claimed issues with no PR after SECS seconds (default 4h); **manual use only** |
| `coordination release-orphan-claims` | Release claims whose owning session UUID is no longer in `.pod/agents/` (liveness-based, no age threshold); **manual use only** |
| `coordination lock-planner` | Acquire advisory planner lock (20min TTL) |
| `coordination unlock-planner` | Release planner lock early |
| `coordination critical-path-depth [L]` | Count unclaimed critical-path issues; optional label filter |
| `coordination set-target N` | Planner sets recommended target agent count (wind-down use only) |

**Issue lifecycle**: planner creates issue (label: `agent-plan`) →
worker claims it (adds label: `claimed`) → worker creates PR closing it
(label swaps to `has-pr`) → auto-merge squash-merges.
Issues marked `replan` (by skip, partial completion, or worker-led
decomposition) are handled by the next planner. Issues with `has-pr` are
excluded from `list-unclaimed` and `queue-depth`.

**Never apply `has-pr` manually.** The label is set automatically by
`coordination create-pr` (full path) and cleared by GitHub's auto-close
on merge of a `Closes #N` PR. Hand-applying it desynchronises the label
from any actual PR — when the supposed PR closes or merges without
`Closes #N`, the issue stays `has-pr` forever and is silently excluded
from the work queue. If you want to "park" an issue while sub-issues
do the work, use `coordination add-dep <parent> <sub>` for each
sub-issue: the parent becomes `blocked`, and `check-blocked` auto-clears
the label when all subs close. The orphan-label housekeeping cycle
(`check-has-pr`, `check-blocked`) auto-removes mis-applied labels and
posts an audit comment on the issue.

**Partial completion**: worker uses `--partial` → label swaps to
`replan`. A planner creates a new issue for remaining work, then closes
the `replan` issue with a link to the new one.

**Worker-led decomposition**: if the claimed issue is too large for one
session, worker creates sub-issues and `coordination skip`s the parent
with a `Decomposed into #X, #Y` breadcrumb comment. The next planner
either closes the parent (sub-issues fully cover it) or narrows it to the
residual scope. See "Assess Scope" (Step 4b) for the full procedure.

**Dependencies**: Issues can declare `depends-on: #N` in their body.
`coordination plan` auto-adds the `blocked` label if any dependency is
open. `check-blocked` (run by `pod` each loop) removes `blocked` when
all dependencies close. Blocked issues are excluded from
`list-unclaimed` and `queue-depth`.

**Dependency code that lives only in an unmerged PR**: a dependency issue
can be *closed* while the def/lemma it produced is still in an open PR
(residual assembly, split work), so it is absent from `main`.

**Check first whether that PR is simply mergeable — if so, merge it and work
off `main`.** This is strictly better than either stacking or skipping, and it
is the same merge sweep CLAUDE.md prescribes, just triggered by need rather
than by the calendar. Require every check to have *completed successfully*
(`gh pr view <N> --json mergeable,mergeStateStatus,statusCheckRollup`;
`MERGEABLE` + `CLEAN` + every `statusCheckRollup` entry `COMPLETED`/`SUCCESS`)
— "not failing" is not "passing", and a PR whose checks are still queued has
empty `conclusion` fields. Merge with `gh pr merge <N> --squash
--delete-branch`, re-`git fetch`, confirm the decls are on `main`, and proceed
normally. (2026-07-25: #7807's stated foundation was in open PR #7809, green
and clean; merging it removed the stacking problem entirely.)

If the PR is *not* mergeable (conflicts, failing or still-running CI), do NOT
wait or skip — `git fetch`
that PR's head branch and base your branch on it
(`git reset --hard origin/<pr-head>`). Then in your PR body add an
ordering note naming the predecessor PR and the exact rebase command, so a
repair/planner agent can sequence the merges. Confirm the dependency file
actually builds on that base before writing new code.

The rebase is **not** a plain `git rebase origin/main`. A squash merge
collapses the predecessor's commits into one new commit that is not
patch-equivalent to any of them, so a plain rebase re-applies them on top of
`main`, which already has the same content — an add/add conflict on every
file the predecessor created. Replay only *your* commits instead:

```bash
git rebase --onto origin/main <pr-head-sha-you-branched-from> <your-branch>
```

See Step 2 for the publish-time version of this.

**Branch naming**: `agent/<first-8-chars-of-UUID>`
**Plan files**: `plans/<UUID-prefix>.md`
**Progress files**: `progress/<UTC-timestamp>_<UUID-prefix>.md`

## Step 1: Claim a Work Item

```
coordination orient
```

**Priority order:**
0. **Directives first**: Check for open `directive` issues before anything else.
   These are direct instructions from the project owner — work flowing *down* from
   the human, not work awaiting human attention — and take absolute precedence over
   all other work:
   ```
   coordination list-unclaimed --label directive
   ```
   If any are open and unclaimed, claim the oldest one immediately.
   **Directives cannot be skipped or refused because you disagree with the approach.**
   The valid exits from a `directive` are (a) completing the deliverables and
   **closing the issue yourself**, (b) opening a partial PR and noting the
   remaining scope so a successor can pick it up, or (c) posting a comment
   explaining a genuine technical blocker (e.g. a missing dependency) and
   `coordination skip` with that reason. Do **not** leave a directive open
   with a "for owner closure" note — if the deliverables are in, close it.
   Do not `skip` because you think a different approach is better — that is
   the owner's call, not yours.
1. **Oldest unclaimed issue** of your type:
   ```
   coordination list-unclaimed --label <your-label>
   ```

   **`coordination list-unclaimed` caps its output at 20 and shows the *newest* issues, not the
   oldest, despite the table above documenting FIFO order.** So genuinely starved issues are
   invisible to it: on 2026-07-26 the head of `list-unclaimed` was 2026-07-22, while #6045, #6053,
   #6217, #6276 and others had sat unclaimed since 2026-07-09. If you want the real FIFO head, ask
   GitHub directly:
   ```bash
   gh issue list --state open --label agent-plan --json number,title,labels,createdAt --limit 200 \
     --jq 'map(select([.labels[].name] | (contains(["claimed"]) or contains(["has-pr"])
       or contains(["blocked"]) or contains(["replan"])) | not))
       | sort_by(.createdAt) | .[:10] | .[] | "\(.number) \(.createdAt) \(.title)"'
   ```
   Prefer a starved issue over a fresh one when both are in scope: the queue view means nobody
   else is seeing it. (2026-07-26: #6276 had been reopened with expanded scope on top of a merged
   PR and then sat unclaimed for 17 days purely because it fell off the bottom of this list.)

**Don't repair PRs from a worker session.** PR health (merge conflicts,
failed CI, stuck CI) is the `repair` agent's responsibility; pod dispatches
`/repair` automatically when `coordination list-pr-repair` reports
candidates, ahead of `/plan` / `/work`. Focus on fresh issue work.

If the queue is empty, write a brief progress note and exit.

```
coordination claim <issue-number>
```

**You MUST check the output.** If it says `CLAIM FAILED`, you MUST NOT work
on that issue — pick a different one. Only proceed if the output says
`Claimed issue #N`. Read the full issue body:
```
coordination read-issue <N> --json body --jq .body
```

**Read the comments too, not just the body.** An issue that was closed and reopened
keeps its original body, so the body describes the state of the world when it was
filed — the *live* scope is in the reopening comment. Bodies also go stale when a
later PR lands part of the work:

```bash
gh issue view <N> --json comments --jq '.comments[] | "\(.createdAt) \(.body)"'
```

Treat any comment starting "Reopening:" as authoritative over the body, and check the
body's factual claims about the repo before acting on them. (2026-07-25, #7320: the
body said an item in `progress/items.json` had no `coverage` field and "was never
coverage-audited"; it had been audited three days earlier and reopened over a
*different*, narrower objection recorded only in a comment. A session that trusts the
body redoes finished work and misses the actual ask.)

## Step 2: Set Up

```bash
git checkout -b agent/<first-8-chars-of-session-UUID>
git rev-parse HEAD      # record starting commit
```

**If the branch already exists** (common in reused worktrees): check for an
open PR on it first (`gh pr list --head agent/<id>`). If a PR exists, create
a new branch with a suffix (`agent/<id>-v2`). If no PR exists, reset it to
the default branch: `git checkout agent/<id> && git reset --hard origin/main`
(this repo's default branch is `main`, not `master`).

**Do not try to `git checkout main` in a pod worktree.** `main` is checked out
in the primary worktree, so the checkout fails — and if you chain it as
`git checkout main || git checkout master` the first failure is silent and you
only see a confusing "pathspec 'master' did not match" error. Fetch and compare
against `origin/main` instead: `git fetch origin && git log --oneline -1 origin/main`.

**Before that `git reset --hard`, run `git status --short` and inspect any
uncommitted changes** (`git diff`). A reused worktree can carry in-progress
edits from a crashed prior session; `reset --hard` discards them irrecoverably.
If the changes look like real work (not stray build artifacts), stash them
(`git stash`, never `git stash -u`) or commit them on a scratch branch before
resetting.

**Run `git status --short` even when you do not reset** — including when the
branch already exists with no PR and no commits ahead of `main`. Leftover
uncommitted edits are not inert:

- `coordination create-pr` stages the whole worktree, so they land in your PR
  as unrelated changes, and edits under `.claude/` will get the PR rejected.
- The Skill tool serves the **working-tree** copy of `.claude/skills/*/SKILL.md`.
  A prior session's half-finished edit there means you are reading truncated
  workflow instructions without knowing it. If `git diff` touches a skill or
  command file, re-read the `HEAD` version (`git show HEAD:<path>`) before
  trusting what you loaded.

Back the diff up (`git diff > /tmp/<session-id>-stale.patch`) and restore the
files (`git checkout HEAD -- <paths>`) so your branch starts clean; note the
backup path in your progress entry.

Judge that inspection in *both* directions: stray changes you leave in place ride
along into your PR as unrelated regressions. Check `git diff --numstat` for changes
that are pure *deletions* against `main` in files you were not asked to touch,
especially under `.claude/`. A crashed session can leave an accidental revert of
accumulated workflow guidance, which is easy to commit without noticing and hard to
spot in review. Restore those (`git checkout HEAD -- <paths>`) rather than carrying
them. (2026-07-25: four times, worktrees arrived with 169, 279, 320 and 364 lines of
`.claude/` guidance deleted and nothing added — always the same five files. In the third
case the session-start `git status` listed all five modified files right in the agent's
context and it committed them anyway, because its own stale copy of this skill lacked this
check — see the publish-time backstop in Step 7. The fourth session caught it, but only
because the duplicate of this check in `.claude/commands/{work,feature}.md` reached it when
this file could not. **Keep that duplication.** A check that lives only inside the file that
goes stale cannot fire in the case it exists for.)

A tell for staleness rather than real work: `git diff --numstat` showing near-pure
deletions, where the handful of "insertions" turn out to be older wordings of lines that
still exist. Real work adds something.

**If the restored files include this skill or your `/command` file, re-read them.**
Skills load from the working tree, so a truncated `SKILL.md` means the guidance you
started the session on was the deleted version and you never saw these instructions.

That instruction only reaches an agent who already *has* the full file, so do not rely
on it — run the check unconditionally, right after `git status`, whether or not
anything looked wrong:

```bash
wc -l .claude/skills/agent-worker-flow/SKILL.md
git show HEAD:.claude/skills/agent-worker-flow/SKILL.md | wc -l
```

If the counts differ, restore and **`Read` the restored file** (the Skill tool will just
reply `instructions unchanged` without re-reading disk — see Step 0), then restart the
workflow from Step 1. Guidance added since the stale revision is exactly the guidance you
are most likely to need — e.g. the Step 7 rules on replacing `create-pr`'s placeholder PR
body and on never running `gh pr merge --auto` yourself.
(2026-07-25: a third worktree that day arrived 193 lines stale; the session ran to
completion on the old copy and shipped a placeholder PR body. A fourth arrived at 318
lines against 539; that session restarted from Step 1 on the restored copy, which is
the only reason it saw these two rules at all.)

**If you branched off an unmerged PR's head** (see "Dependency code that lives
only in an unmerged PR" above), decide at publish time:

- Predecessor already merged → replay only *your* commits onto `main` with
  `git rebase --onto origin/main <pr-head-sha> <your-branch>`, then push.
- Predecessor still open → publish anyway rather than stalling the session, and
  leave a PR comment naming it and giving that exact command. Do not wait more
  than ~15 minutes on someone else's CI; a `repair` agent can fix the conflict
  if one appears, but only if the PR says what it is stacked on.

Record any project-specific quality metrics (e.g. sorry count, test coverage)
as described in the project's CLAUDE.md.

## Step 3: Codebase Orientation

Read the specific files mentioned in the plan/issue. Understand the current state
of code you'll be modifying. Don't read progress history — the issue body provides
that context.

## Step 4: Verify Assumptions

Check that the plan's assumptions still hold:
- Quality metrics match what the issue says
- Files mentioned in the issue still exist and haven't been restructured
- No recently merged PR invalidates the plan
- **A foundation the issue says "landed in #N" is actually in `main`.** Planners
  often reference a sibling PR/commit by number as if merged. If the issue's
  "Current state" describes machinery you'll build on (e.g. "added in #7222"),
  confirm it: `grep` for the named decls in the target file, and if absent check
  whether #N is still an *open* PR (`gh pr view <N>`, `git merge-base --is-ancestor
  <sha> origin/main`). If the foundation is only in an unmerged branch, follow
  "Dependency code that lives only in an unmerged PR" above: **merge #N first if
  it is mergeable with all checks passed** (the common case, and it makes the
  problem go away); otherwise `coordination skip` with a "blocked on unmerged #N"
  reason rather than stacking your work on that branch (a stacked PR against
  `main` carries the other PR's commits and conflicts on merge).
- **If the foundation is in no PR either, it may exist on a dead session's local
  branch — look before you rewrite it.** A session killed mid-task leaves its
  commits on a local branch in its own worktree: no PR, usually no remote branch,
  nothing `coordination` can see. Worktrees share one object store, so those
  commits *are* reachable from here — but only if you go looking. Whenever an
  issue's "Current state" describes work as landed and `main` disagrees, run

  ```bash
  python3 scripts/list_stranded_branches.py --verbose
  git log --all --oneline -- '<path/you/expected>'   # targeted second pass
  ```

  `--verbose` reports every local `agent/*` branch carrying commits nobody can
  see; the `git log --all` is the backstop for branches the script rules out
  (e.g. a *live* session's, which it suppresses by design). If you find the work,
  cherry-pick it onto your branch and credit the original commits in your PR body
  rather than rewriting it. If it belongs to someone else's issue, run
  `python3 scripts/list_stranded_branches.py --recover` so the branch is pushed
  and its issue gets a comment, and carry on with your own item.

  (2026-07-26: three commits and ~370 lines of finished, compiling Lean for
  Problem 8.2.10 sat on dead `agent/65a63411`. #7881's body said they had landed;
  they had not, and a worker who trusted the body would have rewritten all of it.
  Recovered in PR #7890; the detector exists because of #7891.)
- **The "missing"/"partial" result may already exist — grep before implementing.**
  Any issue that describes a gap — an audit reconciliation flagging a
  `covered_partial` residual, *or* a feature issue asserting a result is "not in
  Mathlib and not yet in this repo" — describes it as of when the issue was
  written, which can be stale: a parallel agent may since have proved it, often in
  a *more general* form and in a *different, downstream* file than the issue names
  (e.g. #7315 asked to build reducible "characters determine the representation"
  from scratch; `Etingof.charEq_iso` in `Chapter5/CharEqIso.lean` already had it).
  Before writing any new lemma — *especially* general infrastructure an issue calls
  missing — `grep -rn "<decl_name>\|<key phrase>"` across `EtingofRepresentationTheory/`
  for an existing version; a name collision at build time is the expensive way to
  discover this. If it already exists, reuse it: the task shrinks to a thin
  bridge/assembly (or, for audits, a tracking reconciliation — flip `items.json`,
  repoint `lean_ref`, drop the residual issue), not new infrastructure.
- **The issue's work may be *entirely* done and merged already — if so `close` it,
  don't `skip` it.** A PR whose body omits `Closes #N` merges without closing its
  issue, so the issue keeps appearing in `coordination list-unclaimed` forever and
  the next worker redoes landed work. Cheapest check, before claiming: scan
  `git log origin/main --oneline -20` for a commit whose title matches the issue
  title or cites `#N`, then confirm the decls are on `main`
  (`git show origin/main:<file> | grep <decl>`). If they are, `gh issue close <N>
  --comment "Completed by PR #M (merged as <sha>); the PR body omitted a Closes
  line."` — `coordination skip` is wrong here, it only re-queues the issue for a
  planner. (2026-07: #7704, landed in #7722, sat unclaimed for a full cycle.)
- **A "restore/regression" issue whose reproduction is `lake env lean <file>` may
  be a false positive — reconfirm the failure with `lake build <Module>` before any
  work.** `lake env lean` drops the lakefile's `[leanOptions]` (`maxSynthPendingDepth
  = 3`, `backward.isDefEq.respectTransparency = false`), so files with deep instance
  chains or `isDefEq` diamonds throw spurious `synthInstanceFailed` / instance-path
  errors under it that never occur under `lake build`. See `lean-formalization`
  ("Typecheck with `lake build`, NOT `lake env lean`") for the full account. If
  `lake build <Module>` is green and `#print axioms` on the endpoints is clean, the
  issue is already resolved (often by a since-merged dependency fix) — close it with
  the build evidence rather than editing a working file. (2026-07: #7490, #7547.)

If stale:
```
coordination skip <issue-number> "reason: <what changed>"
```
Go back to Step 1 and try the next issue.

**If the premise is wrong but the problem is real, fix the real defect, not the
prescribed one.** A third case sits between "proceed" and `skip`: the issue reports a
genuine failure but misdiagnoses its cause, so following it literally would leave the
failure in place or actively damage correct data. Neither exit fits: proceeding as
written does harm, and `skip` abandons a real defect. Instead:

- Deliver the issue's stated **verification criterion**, not its prescribed **method**.
  The criterion is what the planner wanted; the method was a guess at how to get there.
- Comment on the issue, before or alongside opening the PR: what the actual defect was,
  why the prescribed fix was rejected, and what you did instead.
- Repeat that reasoning in the PR body, so a reviewer meeting a diff that touches
  different files than the issue named is not surprised by it.
- This still counts as full completion (no `--partial`) as long as the criterion is met.

Worked example: #7712 correctly reported `scripts/validate_items.py` exiting 1 with ten
errors, but blamed `progress/items.json`. Both remedies it proposed would have corrupted
correct data: the ten entries already matched `PLAN.md` Stage 1.6, and the defect was in
the validator, which never implemented that part of the spec. PR #7713 fixed the validator,
met the stated criterion (`validate_items.py` exits 0), and left `items.json` content
untouched.

**Where the authority sits.** `PLAN.md` is the spec and is off-limits to agents, so when an
issue body and `PLAN.md` disagree, `PLAN.md` wins and the issue is the thing that is wrong.
This is the *reverse* of the `directive` rule in Step 1, and the two are easy to confuse: a
`directive` carries the owner's own stated approach, which is not yours to second-guess even
when you would have done it differently; an `agent-plan` issue carries a planner's guess,
which you are expected to check against the spec and the code.

| Situation | Exit |
|---|---|
| Plan is stale (work already done, or moot) | `coordination skip` |
| Prerequisite file/lemma exists only in a healthy open PR | stack on it (see below) |
| Prerequisite does not exist anywhere | `coordination skip` |
| Symptom real, diagnosis or prescribed fix wrong | fix the real defect, document the deviation on the issue and in the PR |
| `directive` whose approach you would have chosen differently | do it as asked (Step 1) |

**A prerequisite sitting in an open PR is a reason to stack, not to skip.** Issue
bodies are written from the planner's view of `main`, and in a repo with this much
PR concurrency they routinely describe a file as "landed" when it is still in an
open PR. Do not `skip` on that alone — the issue is fully specified and its
foundation exists; only *where* it lives is wrong. Check the PR's health first
(`gh pr view <N> --json state,mergeable,statusCheckRollup`); if it is `MERGEABLE`
and CI is not failing:

```bash
git log --oneline origin/main..origin/<their-branch>   # find the commit you need
git cherry-pick <sha>                                  # develop against it locally
```

Keep the cherry-pick as its own commit so it is trivially droppable, rebase onto
`origin/main` just before pushing (if their PR merged first, the commit rebases
away to nothing), and **say so in a PR comment** — otherwise a reviewer or repair
agent meeting an unexplained extra commit will treat the PR as scope-creeping.
Reserve `skip` for the case where the prerequisite exists nowhere, or its PR is
itself unhealthy. Worked example: #7911 named `Chapter8/KoszulBasis.lean` as
landed while it was still in open PR #7913; PR #7918 stacked on it and landed the
full deliverable.

**items.json status reconciliation — sorry-free ≠ item-complete.** For issues
that ask you to flip a `partially_*`/`statement_formalized`/`formalized` entry
to `sorry_free` because "the `.lean` file is sorry-free," read the entry's
existing `coverage_note`/`fidelity_note` **before** changing anything. Those
notes often record a deliberate "sorry-free file but kept `partially_*` because
book part (X) is not formalized as a theorem / is only a `Prop`-def / is an
informal identification" decision that a raw sorry-count sweep cannot see.
Cross-check each part against the item's `blobs/…` file. A file with zero
sorries can still leave a book part unformalized; flipping it to `sorry_free`
hides genuine remaining exercise work. Only set `sorry_free` when a **complete**
sorry-free file backs the item. (Recurred: #7001, #7092.)

**items.json is Unicode + 2-space-indented — preserve both when scripting an
edit.** The file contains math glyphs (`ℂ`, `λ`, `≅`, em-dashes). A naive
`json.dump(d, f, indent=2)` escapes every glyph to `\uXXXX` and reflows the whole
file, turning a 3-line change into a multi-thousand-line diff. Always dump with
`indent=2, ensure_ascii=False` and re-add the trailing newline
(`f.write("\n")`), then confirm with `git diff --stat` that only your entry
changed. For a single-field flip, a targeted `Edit` on the entry is simpler and
safer than a full re-dump.

**PR fix plans**: If the plan asks you to fix a broken PR, use judgement. If the
PR is low quality or not worth salvaging:
```
coordination close-pr <pr-number> "reason: <why not worth fixing>"
```

## Step 4b: Assess Scope

After orienting but **before writing code**, check whether the task fits
in a single session. Warning signs it doesn't:

- Target file is 500+ lines and you need to understand most of it
- The work naturally splits into independent sub-lemmas or sub-tasks
- Difficulty feels higher than the issue says

If the issue is too large, **decomposing it into smaller sub-issues is a
normal success path**, not a failure mode. You have the freshest codebase
context and can usually scope sub-tasks more accurately than a planner could
in advance. A good decomposition is more valuable than a failed heroic
attempt — and far better than overrunning the session trying to salvage it.

You may decompose when any of these is true:
- the claimed issue is too large for one session,
- the work naturally splits into independent sub-tasks,
- you can write self-contained successor issues without further investigation.

```bash
# 1. Create self-contained sub-issues. Use `coordination plan` exactly as a
#    planner would — same body template (Current state / Deliverables /
#    Context / Verification), same label. Note: `coordination plan` does
#    only best-effort title-keyword overlap warnings; it does not hold the
#    planner lock and cannot atomically dedupe against concurrent creators.
#    If you see open issues that look related, link or coordinate
#    explicitly in the sub-issue body rather than relying on the warning.
echo "body..." | coordination plan --label feature "Sub-task 1: ..."
echo "body..." | coordination plan --label feature "Sub-task 2: ..."

# 2. Link ordering dependencies if any sub-task must precede another.
#    Do NOT add `depends-on: #<parent>` — the parent is about to be
#    superseded; depend on real predecessor sub-issues instead.
coordination add-dep <sub2> <sub1>

# 3. Leave a machine-readable breadcrumb on the parent. The planner's
#    replan-triage step keys off this exact `Decomposed into #X, #Y`
#    phrasing — keep it on a single line at the start of the comment.
gh issue comment <parent> --body "Decomposed into #<sub1>, #<sub2>

(reason: <one-line scope assessment>)"

# 4. Release the claim by marking the parent for planner triage. This
#    routes through pod's claim-state machinery and clears the in-process
#    `state.claimed_issue` correctly. Do NOT use `gh issue close` directly:
#    it leaves pod's session-end cleanup thinking the issue is still
#    claimed and will attempt a stray `coordination skip` on a closed
#    issue at exit.
coordination skip <parent> "Decomposed into #<sub1>, #<sub2> — see comment"
```

The planner's next replan-triage cycle picks the parent up and either
closes it (if the sub-issues fully cover it) or narrows the body to the
residual scope (if not).

After decomposing, you have two options:

1. **Continue on one of the sub-issues**: claim it via `coordination claim`,
   then return to Step 2 with the sub-issue. Common case when the parent
   was just two work items glued together.
2. **Stop and exit**: if you've used most of your session orienting, write a
   brief progress entry and exit. The next worker will claim a sub-issue.

If you've already done a coherent subset of the parent's work *before*
deciding to decompose, prefer the partial-PR path:

```bash
# Steps 1-3 above (create sub-issues for the remaining work, leave the
# `Decomposed into #X, #Y` breadcrumb on the parent).

# Then land your coherent subset. `--partial` marks the parent `replan`.
coordination create-pr <parent> --partial "feat: <what landed>"
```

The next planner sees the breadcrumb on the parent and closes it with a
forward link to the sub-issues.

## Step 5: Execute

After each coherent chunk of changes:
- Build and test using the project's build commands (see project CLAUDE.md)
- Commit with conventional prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`

Each commit must compile. One logical change per commit.

**Commit early, push early, create PRs early.** Sessions can terminate at any time.

**Push the branch the moment you have your first commit**, long before it is
PR-worthy:

```bash
git push -u origin <branch>      # repeat after later commits; no PR needed yet
```

A commit that exists only locally is invisible to every other agent and every
other worktree, and a killed session leaves no trace of it anywhere the
coordination layer looks — the issue's claim is released, the issue goes back on
the queue, and the next worker rewrites work that already exists. Pushing costs
nothing and downgrades that to a branch `scripts/list_stranded_branches.py` will
report and `--recover` can link back to its issue. Do it even if you expect to
force-push over it later. (2026-07-26: ~370 lines of finished Lean for Problem
8.2.10, found by accident days later — #7891.)

- Commit after every compiling milestone. Don't wait for the full feature.
- WIP commits are fine: `feat: WIP prove helper_lemma (2/4 sorries remain)`
- If 20+ minutes have passed without a commit, stop and commit now.
- Use `coordination create-pr N --partial` as soon as you have useful
  progress, even if incomplete. This saves the work as a visible PR.

**Failure handling:**
- Build fails on pre-existing issue → log and work around
- Stuck after 3 fundamentally different attempts → decompose into sub-issues (Step 4b)
- 3 consecutive iterations with no commits → end session, document blockers
  (does not apply to review or self-improvement sessions)
- If `/second-opinion` or `/reflect` is unavailable, skip and note in progress entry

## Step 5b: Context Health

**If conversation compaction occurs:**
1. Finish your current sub-task (get to compiling state)
2. Commit what you have
3. Skip remaining deliverables — do NOT start new work
4. Go directly to Step 6 then Step 7 with `--partial`

Commit early and often. Each commit is a checkpoint.

## Step 6: Verify

Build and test the project. Compare quality metrics with the starting values.
Review your diff: `git diff <starting-commit>..HEAD`.
Use `/second-opinion` if available.

## Step 7: Publish

Write a progress entry to `progress/<UTC-timestamp>_<UUID-prefix>.md`:
- Date/time (UTC), session type, what was accomplished
- Decisions made, key patterns discovered
- What remains, quality metric deltas

**Before pushing, check the scope of your diff: `git diff --stat origin/main...HEAD`.**
Every changed file must belong to the issue you claimed. **Never stage with a blanket
`git add -A`/`git commit -a`** — in a reused worktree that sweeps up whatever a previous
session left behind, and stale `.claude/` copies land on `main` as silent reverts of
accumulated guidance. Stage the paths you actually touched. This is the backstop for the
Step 2 stale-worktree check: it catches the same damage even when the copy of this skill
you started on was itself the truncated one. (2026-07-25: PR #7834 shipped a clean
Künneth proof together with a 320-line revert of `.claude/`, repaired by #7835.)

**Full completion:**
```bash
git push -u origin <branch>
coordination create-pr <issue-number>
gh pr edit <new-pr-number> --body "$(cat <<'EOF'
This PR ...
EOF
)"
```

**`create-pr` writes a placeholder body, so replace it.** The body it generates is just
the `Closes #N` line, your session UUID, and a raw `git log`; it takes no body argument
and reads nothing from stdin. Follow it with `gh pr edit <N> --body`, opening with a
paragraph that starts "This PR ..." in imperative present, since that paragraph becomes
the release note. Keep the `Closes #N`, `Session:` and `🤖 Prepared with Claude Code`
lines.

**Do not run `gh pr merge --auto --squash` yourself.** `create-pr` already attempts to
enable auto-merge, and on this repo it reports `auto-merge not available (branch
protection may not be set up)`. That warning is the whole story: with auto-merge
unavailable, a follow-up `gh pr merge <N> --auto --squash` does not queue behind CI, it
**merges immediately**, landing your branch on `main` with `build` still `IN_PROGRESS`.
For a Lean change that means unbuilt code on `main` and a broken base for every other
agent. Leave the PR alone after `create-pr`; the next planning cycle's merge sweep
checks `statusCheckRollup` before merging. (2026-07-25: PR #7725 merged 24s after
creation, both `build` checks still running.)

**This rule overrides the project `.claude/CLAUDE.md`, which still says to run
`gh pr merge "$PR_NUM" --auto --squash` right after `create-pr`.** That file is
off-limits to agents, so the contradiction cannot be fixed at the source — when the
two disagree, follow this skill. (2026-07-25: an agent that had read CLAUDE.md's PR
workflow section ran the command on its own PR #7744 *and* on another session's #7743,
merging both with `build` still `IN_PROGRESS`.)

**The merge sweep in CLAUDE.md has the same hazard: its jq filter is
`all(.conclusion != "FAILURE" and .conclusion != "CANCELLED")`, which is vacuously
true for a PR whose checks are still queued or running (`conclusion` is empty), and
also true for a PR with no checks at all.** Before merging anything in the sweep,
require every check to have *completed successfully* — e.g. select on
`(.statusCheckRollup | length > 0 and all(.conclusion == "SUCCESS"))`, or just read
`gh pr checks <N>` and skip anything `pending`. "Not failing" is not "passing".

**Once the PR is created, exit.** Do not poll CI, wait for the merge, or
otherwise spin on the PR. Another session will pick up any follow-up work
(e.g. a "fix PR #N" issue if CI fails). Polling burns context and tokens
for no benefit.

**Partial completion** (did NOT complete all deliverables):
- Progress entry lists: completed deliverables, NOT-completed deliverables and why,
  whether unfinished work needs a new issue
- Use `--partial`:
  ```
  coordination create-pr <N> --partial "feat: what was actually done"
  ```

**If you only closed a bad PR** (no code changes):
```bash
gh issue close <N> --comment "Closed PR #M as not worth salvaging. See progress entry."
```

## Step 8: Reflect

Run `/reflect`. If it suggests improvements to skills or commands, make those
changes and commit before finishing. Do NOT modify the project's top-level
CLAUDE.md or roadmap files — those are off-limits to agents.

# Execute a Meditate Work Item

You are a **meditate** (self-improvement) session. Your job is to improve the
agent workflow by updating skills, commands, and tooling based on accumulated
experience.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to meditate sessions.

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

Use `coordination list-unclaimed --label meditate` to find work for this session type.

## The Meditate Task

The issue body will describe the specific focus — common themes include:
- Consolidating frequently-seen struggle patterns into new or updated skills
- Updating workflow commands that have become stale
- Researching better approaches to recurring challenges
- Improving the coordination tooling based on pain points in recent progress entries

### Step 1: Survey recent struggles

Read the last 20 entries in `progress/` (sorted by filename, most recent last).
Look for:
- Repeated failure patterns (tried N approaches, gave up)
- "Couldn't figure out" or "blocked by" notes
- Similar mistakes appearing in multiple sessions
- Complaints or workarounds that suggest missing guidance

### Step 2: Read existing skills

Read the relevant SKILL.md files (both project-level in `.claude/skills/` and
config-level) to understand what guidance already exists and where the gaps are.

### Step 3: Update or create skills

Read the `acquiring-skills` skill before writing any new skill.

For each gap or recurring struggle:
- If it fits in an existing skill, add a new section to that SKILL.md
- If it's a new topic area, create a new skill

### Step 4: Update commands if stale

Read the command files. If any contain guidance that contradicts recent experience
or refers to obsolete workflows, update them.

### Step 5: Commit and publish

Each skill update should be its own commit. Command updates are a separate commit.
Write a clear progress entry documenting what changed and why.

## Constraints

- Do NOT modify the project's top-level CLAUDE.md or roadmap files
- Only commit skill and command changes (plus progress entry)
- No code changes — this is workflow, not implementation

## Reflect

Run `/reflect`. If it suggests further improvements beyond what you already did,
capture them in a meditate issue for the next session.

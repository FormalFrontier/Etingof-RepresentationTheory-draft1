# Execute a Meditate Work Item

You are a **meditate** (self-improvement) session. Your job is to improve the
agent workflow by updating skills, commands, and tooling based on accumulated
experience.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to meditate sessions.

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

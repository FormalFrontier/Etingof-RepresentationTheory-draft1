#!/usr/bin/env bash
# SessionStart backstop for the pod `.claude/` staleness bug (issue #7935).
#
# pod's `install_agent_config` (dev-pod `pod/cli.py`, the Claude branch of that
# function) does an unconditional
#     shutil.copytree(bundled/commands, .claude/commands, dirs_exist_ok=True)
#     shutil.copytree(bundled/skills,   .claude/skills,   dirs_exist_ok=True)
# into every freshly-created worktree, from a copy bundled inside the installed
# dev-pod package. That bundled copy is frozen at dev-pod install time, while
# this repo's `main` keeps improving the same files via meditate sessions. So
# every session starts with `.claude/commands` and `.claude/skills` reverted to
# whatever dev-pod shipped, showing up as a pure-deletion diff against HEAD.
#
# This hook restores those two directories to HEAD before the agent works, so a
# later `git add -A` cannot revert the newer guidance on `main`. It does NOT fix
# the agent being *served* the stale command/skill text: that content is
# snapshotted at session start, before this hook's writes are visible. See the
# "Verify the Worktree Is Not Stale" section in `agent-worker-flow` for the
# in-session half of the defence.
#
# Deliberately narrow:
#   - only `.claude/commands` and `.claude/skills`, the two paths pod overwrites;
#   - only tracked files (`git checkout HEAD --` never touches untracked ones),
#     so new skills/commands an agent is drafting survive;
#   - the pre-restore diff is saved to /tmp first, so nothing is unrecoverable;
#   - wired to the `startup` matcher only, never `resume`/`compact`, so it cannot
#     discard a meditate session's own in-progress edits.
# Always exits 0: a broken backstop must not take the session down with it.

set -uo pipefail

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || exit 0
cd "$repo_root" || exit 0

paths=(.claude/commands .claude/skills)

# Nothing tracked-and-modified under those paths => nothing to do.
if git diff --quiet HEAD -- "${paths[@]}" 2>/dev/null; then
  exit 0
fi

stamp=$(date -u +%Y-%m-%dT%H-%M-%SZ)
backup="/tmp/pod-claude-staleness-${stamp}-$$.patch"
git diff HEAD -- "${paths[@]}" > "$backup" 2>/dev/null

summary=$(git diff --numstat HEAD -- "${paths[@]}" 2>/dev/null \
  | awk '{add+=$1; del+=$2; n++} END {printf "%d file(s), +%d/-%d", n, add, del}')

git checkout HEAD -- "${paths[@]}" 2>/dev/null

echo "[restore-claude-config] reverted stale pod-bundled .claude/ config to HEAD (${summary}); pre-restore diff saved to ${backup}" >&2
exit 0

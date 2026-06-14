**This is a harness-infrastructure escalation, not formalization work. It cannot be fixed by an agent worker inside this repository — the fix is one line in the `pod` Python package — so it is filed for human / pod-maintainer attention and paired with a `return-to-human` signal.**

## Symptom

The dispatcher's work-accounting reports an empty queue while 32 `agent-plan` issues are open (11 of them ready/claimable). Every cycle the dispatcher therefore launches a *planner* (queue looks empty) but never a *worker* (no claimable issues visible), so the core formalization frontier never gets worked. This matches the long run of "Nth consecutive planner no-op cycle" commits.

Observed, right now, on `main`:

```
coordination list-unclaimed   -> (empty)
coordination list-replan      -> (empty)
coordination queue-depth      -> 0
```

But direct `gh` shows 32 open `agent-plan` issues, of which 11 carry only `[agent-plan,feature]` (no `claimed`/`blocked`/`has-pr`/`replan`) and are genuinely ready: #2978 #2977 #2976 #2974 #2967 #2853 #2823 #2801 #2793 #2769 #2693.

## Root cause

`pod/cli.py` `_agent_config_sync_check()` prints template-divergence diagnostics to **stdout** (not stderr), at approximately lines 408-419:

```python
if updated:
    print(f"pod: updated {len(updated)} file(s) from new pod version: ...")
if custom:
    print(f"pod: {len(custom)} project-customised file(s) differ from pod template: ...")
if conflicts and not first_run:
    print(f"pod: WARNING: {len(conflicts)} file(s) modified in both ...")
elif conflicts and first_run:
    print(f"pod: {len(conflicts)} file(s) differ from pod template ...")
```

`ensure_config()` calls this check on essentially every `pod` invocation. The coordination commands that need a trusted-author view of issues (`list-unclaimed`, `list-replan`, `queue-depth`, and the issue sections of `orient`) obtain it by spawning a **subprocess** `pod _filter-trusted-issues …` and capturing its stdout (`coordination.py:_filter_trusted_issues`). The warning line is therefore prepended to the captured JSON:

```
pod: 3 project-customised file(s) differ from pod template: commands/meditate.md, commands/plan.md, skills/agent-worker-flow/SKILL.md
[ { ...real issue JSON... } ]
```

`coordination.py:_safe_json` does `json.loads(stripped)`, which fails on the leading non-JSON line and returns the `default=[]`. So the entire issue list is silently dropped. Verified: feeding the same `_filter-trusted-issues` output through a parser that skips the warning line yields 32 issues / 11 ready, exactly as expected.

Commands that query `gh` directly in-process (`list-pr-repair`, the PR/directive sections of `orient`) are unaffected — which is why directives (#4516) and PR-repair still flow while ordinary feature/replan work is invisible.

## Trigger (project side)

The warning fires because this project intentionally customises three agent-config files, all of which differ from the pod template in the committed `main` state (so this affects every worktree, every session, persistently):

- `.claude/commands/plan.md`
- `.claude/commands/meditate.md`
- `.claude/skills/agent-worker-flow/SKILL.md`

These customisations are legitimate (the project's CLAUDE.md directs agents to "Update skills and commands instead"). Reverting them is **not** the right fix.

## Fix

In `pod/cli.py` `_agent_config_sync_check()`, route the four diagnostic `print(...)` calls to stderr: add `file=sys.stderr` (or use a logger). Diagnostics must never share stdout with machine-readable command output.

Optional defense-in-depth in `coordination.py`: make `_safe_json` tolerant of leading non-JSON lines (skip to the first `[`/`{`), and/or have `_filter_trusted_issues` pass a quiet flag to the subprocess.

## Impact

Until fixed, the autonomous loop cannot dispatch workers to the formalization frontier; it can only spin planners (no-op) and service directives / PR-repair. Paired with a `return-to-human` signal so this is seen promptly rather than burning further planner cycles.

🤖 Prepared with Claude Code

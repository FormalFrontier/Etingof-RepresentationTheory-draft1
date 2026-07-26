#!/usr/bin/env python3
"""Report local `agent/*` branches whose commits are invisible to everyone else.

A pod agent session that is killed mid-task leaves its commits on a local
branch in its own worktree. Nothing in the coordination layer sees them:
`release-orphan-claims` releases the *issue claim* of a dead session but never
looks at its branch, and `check-has-pr` only audits issues that already claim a
PR. The commits are reachable only by someone running `git log --all` from a
worktree that shares the repository. That is how ~370 lines of finished Lean for
Problem 8.2.10 went missing until they were found by accident (recovered in
PR #7890, see issue #7891).

This script makes that state visible, and with `--recover` pushes the branch so
every other agent and worktree can see it.

Usage
-----
    python3 scripts/list_stranded_branches.py            # report (read-only)
    python3 scripts/list_stranded_branches.py --json     # machine-readable
    python3 scripts/list_stranded_branches.py --verbose  # list the commits
    python3 scripts/list_stranded_branches.py --recover  # push + comment

Exit status is 0 whether or not anything is stranded; a non-zero status means
the check itself could not run (unreadable `.pod/agents/`, git failure). That
split matters: "no strandings" and "could not tell" must not look alike.

Scope: local branches only. Remote `agent/*` branches are deliberately not
scanned — this repository has ~2700 of them, squash-merging leaves every one of
them permanently "ahead of main", and deciding the question needs one PR lookup
each.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

BRANCH_GLOB = "agent/*"
DEFAULT_BASE = "origin/main"

# `agent/<first-8-of-uuid>` with an optional trailing tag (`-v2`, `-skill`,
# `-progress`), all of which appear in this repository's history.
UUID_PREFIX_RE = re.compile(r"^agent/([0-9a-f]{8})(?:-|$)")

ISSUE_REF_RE = re.compile(r"#(\d+)")


class CheckFailed(Exception):
    """The check could not reach a verdict — distinct from 'nothing stranded'."""


def git(*args: str, check: bool = True) -> str:
    r = subprocess.run(
        ["git", *args], capture_output=True, text=True, timeout=60,
    )
    if check and r.returncode != 0:
        raise CheckFailed(f"git {' '.join(args)} failed: {r.stderr.strip()}")
    return r.stdout.strip()


def main_repo_root() -> Path:
    """Repository root, resolved through a worktree to the primary checkout.

    `.pod/` lives at the primary root only, so a worktree that resolved its own
    directory would silently find no agent metadata and report every branch as
    orphaned.
    """
    return Path(git("rev-parse", "--git-common-dir")).resolve().parent


def live_session_uuids(root: Path) -> set[str]:
    """UUIDs of sessions pod still considers alive.

    Mirrors `coordination`'s own liveness rule. Note the *filename* under
    `.pod/agents/` is not the session UUID (`8fc88fff.json` holds session
    `2886438e-...`), so the `uuid` field has to be read out of each file.
    """
    agents_dir = root / ".pod" / "agents"
    if not agents_dir.is_dir():
        raise CheckFailed(
            f"cannot read {agents_dir} — refusing to call any session dead "
            f"without liveness data"
        )
    live: set[str] = set()
    for p in sorted(agents_dir.glob("*.json")):
        if p.name.endswith(".tmp"):
            continue
        try:
            d = json.loads(p.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if d.get("status") in ("dead", "stopped", "killed"):
            continue
        uuid = d.get("uuid")
        if isinstance(uuid, str) and uuid:
            live.add(uuid)
    return live


def branch_owner_is_live(branch: str, live: set[str]) -> bool | None:
    """True/False if the branch names a session, None if it names none.

    Hand-named branches (`agent/continue-completeness-audit`) have no owning
    session to be alive, so their commits are nobody's responsibility to push.
    """
    m = UUID_PREFIX_RE.match(branch)
    if not m:
        return None
    prefix = m.group(1)
    return any(u.startswith(prefix) for u in live)


def rev_count(rng: str) -> int:
    return int(git("rev-list", "--count", rng))


def rev_count_excluding(base: str, branch: str, excluded: list[str]) -> int:
    """Commits on `branch` but on neither `base` nor any of `excluded`."""
    return int(git("rev-list", "--count", branch, f"^{base}",
                   *(f"^{ref}" for ref in excluded)))


def ref_exists(ref: str) -> bool:
    return subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", ref + "^{commit}"],
        capture_output=True, text=True, timeout=30,
    ).returncode == 0


def prs_for_branch(branch: str) -> list[dict]:
    r = subprocess.run(
        ["gh", "pr", "list", "--head", branch, "--state", "all",
         "--json", "number,state,headRefOid", "--limit", "20"],
        capture_output=True, text=True, timeout=60,
    )
    if r.returncode != 0:
        raise CheckFailed(f"gh pr list --head {branch} failed: {r.stderr.strip()}")
    try:
        return json.loads(r.stdout) or []
    except json.JSONDecodeError:
        raise CheckFailed(f"gh pr list --head {branch} returned non-JSON")


def classify(branch: str, base: str) -> dict | None:
    """Return a stranding record for `branch`, or None if its work is visible.

    Visible means every commit not on `base` is reachable from something
    somebody else can see: the branch's own remote ref, or the head a PR points
    at. Three ways to be invisible, in decreasing severity:

    `no-remote-no-pr`   nothing was ever pushed (the issue #7891 case)
    `unpushed-commits`  a PR exists but the branch grew past what it points at
    `pushed-no-pr`      pushed, but no PR ever linked it to an issue

    Commit counts alone cannot decide this. Squash-merging rewrites the
    branch's commits into one that is not patch-equivalent to any of them, so
    every merged branch stays "ahead of main" forever — 2700-odd of them here.
    What settles it is reachability from a *visible* ref.
    """
    ahead = rev_count(f"{base}..{branch}")
    if ahead == 0:
        return None

    prs = prs_for_branch(branch)

    # Refs that make a commit visible to other agents. A PR's head counts even
    # when `origin/<branch>` is gone: the merge sweep runs `--delete-branch`, so
    # the remote ref of a landed branch normally does not survive.
    remote = f"origin/{branch}"
    has_remote = ref_exists(remote)
    visible_refs = [remote] if has_remote else []
    merged_unknown_head = False
    for p in prs:
        oid = p.get("headRefOid") or ""
        if oid and ref_exists(oid):
            visible_refs.append(oid)
        elif p.get("state") == "MERGED":
            merged_unknown_head = True

    if merged_unknown_head and not visible_refs:
        # The PR merged and its head is no longer in this clone, so there is
        # nothing left to compare the local commits against. Call it covered:
        # a false positive on every merged-and-deleted branch would bury the
        # real signal, and the merge is decent evidence the work landed.
        return None

    invisible = rev_count_excluding(base, branch, visible_refs)

    if invisible > 0:
        kind = "no-remote-no-pr" if not visible_refs and not prs else "unpushed-commits"
    elif not prs:
        # Pushed, but nothing links it to an issue. A remote branch among
        # thousands is not meaningfully more discoverable than a local one.
        kind, invisible = "pushed-no-pr", ahead
    else:
        return None

    return {
        "branch": branch,
        "kind": kind,
        "tip": git("rev-parse", "--short", branch),
        "commits_ahead_of_base": ahead,
        "invisible_commits": invisible,
        "has_remote": has_remote,
        "prs": [{"number": p["number"], "state": p["state"]} for p in prs],
        "subjects": git(
            "log", "--format=%h %s", "-20", f"{base}..{branch}"
        ).splitlines(),
    }


def referenced_issues(record: dict) -> list[int]:
    """Issue numbers cited by the stranded commits, most-cited first."""
    counts: dict[int, int] = {}
    for line in record["subjects"]:
        for n in ISSUE_REF_RE.findall(line):
            counts[int(n)] = counts.get(int(n), 0) + 1
    return sorted(counts, key=lambda n: (-counts[n], n))


def recovery_comment(record: dict, base: str) -> str:
    branch = record["branch"]
    return (
        f"Stranded-branch recovery: `{branch}` (tip `{record['tip']}`) carries "
        f"{record['invisible_commits']} commit(s) that were not visible anywhere "
        f"({record['kind']}). The owning session is gone. The branch has now been "
        f"pushed to `origin/{branch}`.\n\n"
        f"Commits ahead of `{base}`:\n\n```\n"
        + "\n".join(record["subjects"]) +
        "\n```\n\nBefore redoing this work, check it out and see what is already "
        f"finished:\n\n```bash\ngit fetch origin {branch}\n"
        f"git log --oneline {base}..origin/{branch}\n```\n\n"
        "Posted by `scripts/list_stranded_branches.py --recover`."
    )


def recover(record: dict, base: str) -> list[str]:
    """Push the branch, then point its issue at it. Returns log lines.

    Pushing is the whole point: a local branch is invisible to every other
    worktree. This deliberately stops short of opening a PR — an unreviewed PR
    from a dead session lands in the repair queue and displaces live work,
    whereas a comment puts the branch in front of the next worker to read the
    issue, who has the context to judge whether the commits are worth keeping.
    """
    log: list[str] = []
    branch = record["branch"]

    # Plain push, never forced: if the remote diverged, a human or a later
    # worker should reconcile the two, not have one silently overwrite the other.
    r = subprocess.run(
        ["git", "push", "origin", f"{branch}:{branch}"],
        capture_output=True, text=True, timeout=120,
    )
    if r.returncode != 0:
        log.append(f"  push FAILED (left local): {r.stderr.strip().splitlines()[-1:]}")
        return log
    log.append(f"  pushed to origin/{branch}")

    issues = referenced_issues(record)
    if not issues:
        log.append("  no issue reference in commit subjects — branch pushed, "
                   "not linked; needs manual triage")
        return log

    issue = issues[0]
    r = subprocess.run(
        ["gh", "issue", "comment", str(issue), "--body",
         recovery_comment(record, base)],
        capture_output=True, text=True, timeout=60,
    )
    if r.returncode != 0:
        log.append(f"  comment on #{issue} FAILED: {r.stderr.strip()}")
    else:
        log.append(f"  commented on #{issue}")
    return log


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--base", default=DEFAULT_BASE,
                   help=f"base ref to measure against (default {DEFAULT_BASE})")
    p.add_argument("--json", action="store_true", dest="as_json",
                   help="emit the records as JSON")
    p.add_argument("--verbose", action="store_true",
                   help="list each stranded commit")
    p.add_argument("--recover", action="store_true",
                   help="push each stranded branch and comment on its issue")
    p.add_argument("--include-live", action="store_true",
                   help="also report branches whose session is still running "
                        "(they are expected to be ahead; useful for debugging)")
    return p.parse_args(argv)


def run(args: argparse.Namespace) -> int:
    root = main_repo_root()
    live = live_session_uuids(root)

    if not ref_exists(args.base):
        raise CheckFailed(f"base ref {args.base} does not exist — run `git fetch origin`")

    current = git("rev-parse", "--abbrev-ref", "HEAD")
    branches = git(
        "for-each-ref", "--format=%(refname:short)", f"refs/heads/{BRANCH_GLOB}"
    ).splitlines()

    records = []
    for branch in branches:
        owner_live = branch_owner_is_live(branch, live)
        if owner_live and not args.include_live:
            continue
        if branch == current and not args.include_live:
            # Our own in-progress work is not stranded.
            continue
        rec = classify(branch, args.base)
        if rec is None:
            continue
        rec["owner"] = ("live" if owner_live else
                        "dead" if owner_live is False else "unknown")
        records.append(rec)

    records.sort(key=lambda r: -r["invisible_commits"])

    if args.as_json:
        print(json.dumps(records, indent=2))
    elif not records:
        print("No stranded agent branches.")
    else:
        print(f"{len(records)} stranded agent branch(es) "
              f"(ahead of {args.base}, invisible, owning session gone):\n")
        for r in records:
            pr_note = (", ".join(f"#{p['number']} {p['state'].lower()}"
                                 for p in r["prs"]) or "no PR")
            print(f"  {r['branch']}  [{r['kind']}]  tip {r['tip']}  "
                  f"{r['invisible_commits']} invisible commit(s)  "
                  f"({pr_note}; session {r['owner']})")
            if args.verbose:
                for line in r["subjects"]:
                    print(f"      {line}")

    if args.recover:
        if not records:
            print("\nNothing to recover.")
        for r in records:
            print(f"\nRecovering {r['branch']}:")
            for line in recover(r, args.base):
                print(line)

    return 0


def main(argv: list[str]) -> int:
    try:
        return run(parse_args(argv))
    except CheckFailed as e:
        print(f"list-stranded-branches: {e}", file=sys.stderr)
        return 2
    except BrokenPipeError:
        # Piping into `head` is the normal way to read this; don't spray a
        # traceback that looks like the check itself failed.
        try:
            sys.stdout.close()
        except BrokenPipeError:
            pass
        return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

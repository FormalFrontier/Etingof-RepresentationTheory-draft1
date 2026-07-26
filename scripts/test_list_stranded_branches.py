#!/usr/bin/env python3
"""Self-test for `scripts/list_stranded_branches.py`.

Builds the four stranding shapes as real git refs in a throwaway repository —
including a fake `refs/remotes/origin/...` so "pushed but never PR'd" can be
exercised without pushing anything anywhere — and checks that each is
classified correctly. `gh` is stubbed, so this runs offline.

    python3 scripts/test_list_stranded_branches.py
"""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

spec = importlib.util.spec_from_file_location(
    "list_stranded_branches", HERE / "list_stranded_branches.py")
L = importlib.util.module_from_spec(spec)
spec.loader.exec_module(L)

FAILURES: list[str] = []


def check(label: str, got, want) -> None:
    if got == want:
        print(f"  ok   {label}")
    else:
        print(f"  FAIL {label}: got {got!r}, want {want!r}")
        FAILURES.append(label)


def git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git", "-C", str(repo), *args],
                       capture_output=True, text=True, check=True)
    return r.stdout.strip()


def commit_on(repo: Path, parent: str, msg: str) -> str:
    tree = git(repo, "rev-parse", f"{parent}^{{tree}}")
    return git(repo, "commit-tree", tree, "-p", parent, "-m", msg)


def build_repo(root: Path) -> None:
    """A repo with one branch per stranding shape, plus two that are fine."""
    git(root, "init", "-q", "-b", "main")
    git(root, "config", "user.email", "t@t")
    git(root, "config", "user.name", "t")
    (root / "f").write_text("x\n")
    git(root, "add", "f")
    git(root, "commit", "-qm", "base")
    base = git(root, "rev-parse", "main")
    git(root, "update-ref", "refs/remotes/origin/main", base)

    # Never pushed, no PR — the issue #7891 case.
    git(root, "branch", "agent/11111111",
        commit_on(root, base, "feat(Ch8 #4242): finished but never pushed"))

    # Pushed, PR merged, then the session committed more and died.
    pushed = commit_on(root, base, "feat(Ch3 #77): landed work")
    git(root, "update-ref", "refs/remotes/origin/agent/22222222", pushed)
    git(root, "branch", "agent/22222222",
        commit_on(root, pushed, "feat(Ch3 #77): follow-up never pushed"))

    # Pushed, but no PR was ever opened against it.
    pushed2 = commit_on(root, base, "chore: pushed, no PR")
    git(root, "update-ref", "refs/remotes/origin/agent/33333333", pushed2)
    git(root, "branch", "agent/33333333", pushed2)

    # Hand-named branch with no owning session in its name.
    git(root, "branch", "agent/hand-named",
        commit_on(root, base, "chore: hand-named branch"))

    # Squash-merged and then `--delete-branch`ed, so there is no
    # `origin/agent/44444444` left: still ahead of main forever, but the
    # content landed. This is the ordinary end state of every merged PR in the
    # repository, and the regression it guards against is deciding by commit
    # count or by remote-ref existence, either of which flags all ~2700 of them.
    merged_head = commit_on(root, base, "feat(Ch5 #99): squash-merged")
    git(root, "branch", "agent/44444444", merged_head)
    PR_TABLE["agent/44444444"][0]["headRefOid"] = merged_head

    # Merged, branch deleted, and the head commit was never fetched into this
    # clone — nothing local to compare against, so it must not be reported.
    git(root, "branch", "agent/66666666",
        commit_on(root, base, "feat(Ch6 #101): merged, head not in this clone"))

    # A live session's branch: ahead, unpushed, but still being worked on.
    git(root, "branch", "agent/55555555",
        commit_on(root, base, "feat: work in progress"))

    agents = root / ".pod" / "agents"
    agents.mkdir(parents=True)
    (agents / "unrelated-filename.json").write_text(json.dumps(
        # Filename deliberately unlike the UUID: pod names these files by
        # something other than the session UUID, so a check that matched on
        # filenames would call every live session dead.
        {"uuid": "55555555-aaaa-bbbb-cccc-dddddddddddd", "status": "running"}))
    (agents / "corpse.json").write_text(json.dumps(
        {"uuid": "11111111-aaaa-bbbb-cccc-dddddddddddd", "status": "dead"}))


PR_TABLE: dict[str, list[dict]] = {
    "agent/22222222": [{"number": 77, "state": "MERGED", "headRefOid": ""}],
    # headRefOid filled in by build_repo once the commit exists.
    "agent/44444444": [{"number": 99, "state": "MERGED", "headRefOid": ""}],
    # A merged PR whose head this clone never fetched.
    "agent/66666666": [{"number": 101, "state": "MERGED",
                        "headRefOid": "0" * 40}],
}


def main() -> int:
    with tempfile.TemporaryDirectory() as td:
        root = Path(td) / "repo"
        root.mkdir()
        build_repo(root)
        os.chdir(root)

        L.prs_for_branch = lambda branch: PR_TABLE.get(branch, [])

        print("liveness")
        live = L.live_session_uuids(root)
        check("running session is live",
              L.branch_owner_is_live("agent/55555555", live), True)
        check("dead session is not live",
              L.branch_owner_is_live("agent/11111111", live), False)
        check("hand-named branch has no owner",
              L.branch_owner_is_live("agent/hand-named", live), None)

        print("classification")
        got = {r["branch"]: (r["kind"], r["invisible_commits"])
               for r in [L.classify(b, "origin/main")
                         for b in ("agent/11111111", "agent/22222222",
                                   "agent/33333333", "agent/44444444")]
               if r}
        check("never pushed, no PR", got.get("agent/11111111"),
              ("no-remote-no-pr", 1))
        check("commits past a merged PR", got.get("agent/22222222"),
              ("unpushed-commits", 1))
        check("pushed, never PR'd", got.get("agent/33333333"),
              ("pushed-no-pr", 1))
        check("squash-merged then branch-deleted is not stranded",
              L.classify("agent/44444444", "origin/main"), None)
        check("merged with head absent from clone is not stranded",
              L.classify("agent/66666666", "origin/main"), None)
        check("branch level with main is not stranded",
              L.classify("main", "origin/main"), None)

        print("reporting")
        args = L.parse_args([])
        rc = L.run(args)
        check("exit status", rc, 0)
        args.as_json = True
        reported = {r["branch"]: r["owner"]
                    for r in json.loads(_capture(lambda: L.run(args)))}
        check("live session suppressed", "agent/55555555" in reported, False)
        check("dead session reported", reported.get("agent/11111111"), "dead")
        check("unowned branch reported", reported.get("agent/hand-named"),
              "unknown")
        args.include_live = True
        with_live = {r["branch"]
                     for r in json.loads(_capture(lambda: L.run(args)))}
        check("--include-live shows it", "agent/55555555" in with_live, True)

        print("recovery comment")
        rec = L.classify("agent/11111111", "origin/main")
        check("issue inferred from commit subject", L.referenced_issues(rec),
              [4242])
        body = L.recovery_comment(rec, "origin/main")
        check("names the branch", "agent/11111111" in body, True)
        check("gives a fetch command", "git fetch origin agent/11111111" in body,
              True)

    if FAILURES:
        print(f"\n{len(FAILURES)} failure(s): {', '.join(FAILURES)}")
        return 1
    print("\nall checks passed")
    return 0


def _capture(fn) -> str:
    import io
    import contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        fn()
    return buf.getvalue()


if __name__ == "__main__":
    sys.exit(main())

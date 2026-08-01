#!/usr/bin/env python3
"""Create the PLAN Stage 3.5 per-provider-item GitHub issues in batches.

The command is restart-safe: existing `proof-polish` issue titles are reused,
and `--apply` is required for both GitHub creation and items.json updates.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

import finalize_proof_dependencies as dependency_review


ROOT = Path(__file__).resolve().parent.parent
ITEMS = ROOT / "progress/items.json"
OWNER_REPO = "FormalFrontier/Etingof-RepresentationTheory-draft1"


def gh(*args: str) -> str:
    process = subprocess.run(
        ["gh", *args], cwd=ROOT, text=True, capture_output=True, check=False
    )
    if process.returncode:
        raise SystemExit(process.stderr or process.stdout)
    return process.stdout


def graphql(query: str, variables: dict) -> dict:
    args = ["api", "graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        args.extend(["-F", f"{key}={value}"])
    response = json.loads(gh(*args))
    if response.get("errors"):
        raise SystemExit("GraphQL errors: " + json.dumps(response["errors"], indent=2))
    return response["data"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    items = json.loads(ITEMS.read_text(encoding="utf-8"))
    base = [item for item in items if item.get("type") != "derived"]
    providers, _ = dependency_review.provider_maps(base)
    applicable = [item for item in base if providers[item["id"]]]

    existing_raw = gh(
        "issue", "list", "--repo", OWNER_REPO, "--state", "all",
        "--label", "proof-polish", "--limit", "1000", "--json", "number,title,url",
    ) if "proof-polish" in gh("label", "list", "--repo", OWNER_REPO, "--limit", "200") else "[]"
    existing = {entry["title"]: entry for entry in json.loads(existing_raw)}
    missing = [item for item in applicable if f"Polish {item['id']}" not in existing]
    print(f"{len(applicable)} applicable items; {len(existing)} existing; {len(missing)} missing")
    if not args.apply:
        return

    gh(
        "label", "create", "proof-polish", "--repo", OWNER_REPO,
        "--color", "c5def5", "--description", "Stage 3.5 proof-polishing work item",
        "--force",
    )
    identity = graphql(
        "query($owner:String!,$name:String!){repository(owner:$owner,name:$name){id label(name:\"proof-polish\"){id}}}",
        {"owner": OWNER_REPO.split("/")[0], "name": OWNER_REPO.split("/")[1]},
    )["repository"]

    batch_size = 10
    for start in range(0, len(missing), batch_size):
        batch = missing[start : start + batch_size]
        declarations = ["$repo:ID!", "$label:ID!"]
        fields = []
        variables = {"repo": identity["id"], "label": identity["label"]["id"]}
        for position, item in enumerate(batch):
            declarations.extend([f"$title{position}:String!", f"$body{position}:String!"])
            fields.append(
                f"i{position}:createIssue(input:{{repositoryId:$repo,labelIds:[$label],"
                f"title:$title{position},body:$body{position}}}){{issue{{id number title url}}}}"
            )
            variables[f"title{position}"] = f"Polish {item['id']}"
            variables[f"body{position}"] = (
                f"Stage 3.5 proof-polishing tracker for `{item['id']}`.\n\n"
                "Review evidence is recorded in "
                "`progress/reviews/2026-08-01-stage3-5-proof-polishing.json`. "
                "The completion PR must preserve a successful full build and the "
                "source-bound per-declaration diagnostic dispositions."
            )
        data = graphql(f"mutation({','.join(declarations)}){{{''.join(fields)}}}", variables)
        for value in data.values():
            issue = value.get("issue")
            if issue is None:
                raise SystemExit("GitHub returned a null issue; rerun after the secondary-rate-limit window")
            existing[issue["title"]] = issue
        print(f"created {min(start + batch_size, len(missing))}/{len(missing)}")

    for item in applicable:
        item.setdefault("stage3_5", {})["proof_polish_issue"] = existing[
            f"Polish {item['id']}"
        ]["number"]
    ITEMS.write_text(json.dumps(items, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"recorded {len(applicable)} proof-polish issue numbers in {ITEMS.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

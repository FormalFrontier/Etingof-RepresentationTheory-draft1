#!/usr/bin/env python3
"""Check built ``source_ref`` metadata against the adjudicated alignment ledger."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def module_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def canonical_reference(source_node: dict, derived_ordinal: int | None = None) -> str:
    """Return the stable public reference for one private source claim.

    Partition nodes cite their item directly, while standalone derived nodes use
    the stable ``DerivedNN`` overlay identity within their parent item.  Claims
    classified as covered elsewhere retain their within-item identity with
    ``DerivedN`` when they are not the first claim.  This convention prevents
    distinct proof claims from collapsing to one attribute with conflicting
    roles.
    """

    kind = source_node["kind"]
    if kind == "partition":
        return source_node["item_id"]
    if kind == "derived":
        if derived_ordinal is None:
            raise ValueError("derived source node requires an ordinal")
        return f"{source_node['parent_item_id']}/Derived{derived_ordinal:02d}"

    reference = source_node["item_id"]
    if source_node["verdict"] != "formalized" and source_node["ordinal"] > 1:
        reference += f"/Derived{source_node['ordinal']}"
    return reference


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("release", type=Path)
    parser.add_argument("proposals", type=Path)
    parser.add_argument("adjudicated_edges", type=Path)
    parser.add_argument("source_nodes", type=Path)
    args = parser.parse_args()

    release = args.release.resolve()
    proposals = {
        row["old_fqn"]: row
        for row in read_jsonl(args.proposals)
        if row.get("new_fqn")
    }
    source_node_rows = read_jsonl(args.source_nodes)
    source_nodes = {row["source_node"]: row for row in source_node_rows}
    source_references: dict[str, str] = {}
    derived_counts: dict[str, int] = {}
    for row in source_node_rows:
        derived_ordinal = None
        if row["kind"] == "derived":
            parent = row["parent_item_id"]
            derived_counts[parent] = derived_counts.get(parent, 0) + 1
            derived_ordinal = derived_counts[parent]
        source_references[row["source_node"]] = canonical_reference(
            row, derived_ordinal
        )

    errors: list[str] = []
    # Multiple private source claims can intentionally project to the same
    # public item reference.  A Lean declaration may carry that reference only
    # once, so collapse by (declaration, reference), with the stronger primary
    # role taking precedence.  This matches the Verso panel synchronizer.
    expected_by_reference: dict[tuple[str, str], str] = {}
    for edge in read_jsonl(args.adjudicated_edges):
        if edge.get("adjudication_status") != "adjudicated":
            continue
        proposal = proposals.get(edge["old_fqn"])
        if proposal is None or not module_path(release, proposal["new_module"]).exists():
            continue
        source_node = source_nodes.get(edge["source_node"])
        if source_node is None:
            errors.append(f"missing source node {edge['source_node']}")
            continue
        key = (proposal["new_fqn"], source_references[edge["source_node"]])
        role = edge["role"]
        if role == "primary" or key not in expected_by_reference:
            expected_by_reference[key] = role

    expected = {
        (declaration, reference, role)
        for (declaration, reference), role in expected_by_reference.items()
    }

    command = ["lake", "env", "lean", "--run", "AlignmentExport.lean"]
    completed = subprocess.run(
        command,
        cwd=release,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        raise SystemExit(
            "alignment export failed:\n" + completed.stdout + completed.stderr
        )
    try:
        exported = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise SystemExit(f"alignment export did not emit JSON: {error}") from error

    actual_rows = [
        (row["declaration"], row["reference"], row["role"])
        for row in exported
    ]
    actual = set(actual_rows)
    if len(actual) != len(actual_rows):
        errors.append("alignment export contains duplicate entries")

    for row in sorted(expected - actual):
        errors.append("missing source_ref: " + " | ".join(row))
    for row in sorted(actual - expected):
        errors.append("unexpected source_ref: " + " | ".join(row))

    result = {
        "actual": len(actual),
        "declarations": len({row[0] for row in actual}),
        "errors": len(errors),
        "expected": len(expected),
    }
    print(json.dumps(result, sort_keys=True))
    if errors:
        raise SystemExit("\n".join(errors[:100]))


if __name__ == "__main__":
    main()

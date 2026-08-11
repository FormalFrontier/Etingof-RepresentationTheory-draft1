#!/usr/bin/env python3
"""Merge validated adjudication responses into a derived alignment ledger."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("packets", type=Path)
    parser.add_argument("edges", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    decisions: dict[tuple[str, str], dict] = {}
    for packet_path in sorted(args.packets.glob("*/align-*/packet.json")):
        response_path = packet_path.with_name("response.json")
        if not response_path.exists():
            continue
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        response = json.loads(response_path.read_text(encoding="utf-8"))
        candidate_by_id = {row["association_id"]: row for row in packet["candidates"]}
        for row in response["associations"]:
            candidate = candidate_by_id[row["association_id"]]
            decisions[(packet["source_node"], candidate["declaration"])] = {
                "association_id": row["association_id"],
                "adjudication_packet": packet["packet_id"],
                "adjudication_rationale": row["rationale"],
                "role": row["role"],
            }

    output_rows = []
    adjudicated = 0
    for edge in read_jsonl(args.edges):
        decision = decisions.get((edge["source_node"], edge["old_fqn"]))
        row = dict(edge)
        if decision is not None:
            row.update(decision)
            row["adjudication_status"] = "adjudicated"
            adjudicated += 1
        output_rows.append(row)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as stream:
        for row in output_rows:
            stream.write(json.dumps(row, sort_keys=True) + "\n")
    print(json.dumps({
        "edges": len(output_rows),
        "adjudicated_edges": adjudicated,
        "pending_edges": len(output_rows) - adjudicated,
        "unique_decisions": len(decisions),
    }, sort_keys=True))


if __name__ == "__main__":
    main()

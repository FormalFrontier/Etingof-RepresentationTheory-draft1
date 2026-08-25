#!/usr/bin/env python3
"""Maintain the explicit gate between converted and independently reviewed Verso items."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("metadata", type=Path)
    parser.add_argument("packets", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--add", action="append", default=[], metavar="ITEM_ID")
    parser.add_argument("--approve-all-existing", action="store_true")
    parser.add_argument("--exclude", action="append", default=[], metavar="ITEM_ID")
    args = parser.parse_args()

    ordered_items = [
        row["id"]
        for row in json.loads((args.metadata / "items.json").read_text(encoding="utf-8"))["items"]
    ]
    known = set(ordered_items)
    converted: set[str] = set()
    for content in args.packets.rglob("Content.lean"):
        packet = json.loads(content.with_name("packet.json").read_text(encoding="utf-8"))
        converted.add(packet["item"]["id"])

    approved: set[str] = set()
    if args.output.exists():
        current = json.loads(args.output.read_text(encoding="utf-8"))
        if current.get("schema_version") != "verso-approved-items/v1":
            raise SystemExit(f"{args.output}: unsupported approval schema")
        approved.update(current.get("items", []))
    if args.approve_all_existing:
        approved.update(converted)
    approved.update(args.add)
    approved.difference_update(args.exclude)

    unknown = approved - known
    missing = approved - converted
    if unknown:
        raise SystemExit(f"unknown item IDs: {sorted(unknown)}")
    if missing:
        raise SystemExit(f"approved items without Content.lean: {sorted(missing)}")

    payload = {
        "schema_version": "verso-approved-items/v1",
        "items": [item_id for item_id in ordered_items if item_id in approved],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"approved_items": len(payload["items"]), "converted_items": len(converted)}))


if __name__ == "__main__":
    main()

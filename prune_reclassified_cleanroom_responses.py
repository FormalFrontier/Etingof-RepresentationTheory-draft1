#!/usr/bin/env python3
"""Remove response rows that a stricter generated-declaration classifier retired."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("packets", type=Path)
    args = parser.parse_args()
    changed = removed = 0
    for response_path in sorted(args.packets.glob("*/module-*/response.json")):
        packet_path = response_path.with_name("packet.json")
        if not packet_path.exists():
            continue
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        response = json.loads(response_path.read_text(encoding="utf-8"))
        expected = {row["temporary_id"] for row in packet["declarations"]}
        rows = response.get("declarations", [])
        missing = expected - {row["temporary_id"] for row in rows}
        if missing:
            raise SystemExit(f"{response_path}: missing non-generated declarations {sorted(missing)}")
        kept = [row for row in rows if row["temporary_id"] in expected]
        if len(kept) != len(rows):
            response["declarations"] = kept
            response_path.write_text(
                json.dumps(response, indent=2, sort_keys=False) + "\n", encoding="utf-8"
            )
            changed += 1
            removed += len(rows) - len(kept)
    print(json.dumps({"responses_changed": changed, "retired_rows_removed": removed}))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Create disjoint, item-shaped native-Verso conversion packets."""

from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path


def write_json_if_changed(path: Path, payload: object) -> None:
    rendered = json.dumps(payload, indent=2) + "\n"
    if path.exists() and path.read_text(encoding="utf-8") == rendered:
        return
    path.write_text(rendered, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("draft", type=Path)
    parser.add_argument("items_manifest", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--preserve-existing-sources",
        action="store_true",
        help="leave existing source.md files untouched when refreshing packet metadata",
    )
    parser.add_argument(
        "--preserve-existing-packet-metadata",
        action="store_true",
        help="retain packet-level fields such as workflow status while refreshing item metadata",
    )
    args = parser.parse_args()

    manifest = json.loads(args.items_manifest.read_text(encoding="utf-8"))
    args.output.mkdir(parents=True, exist_ok=True)

    batch_index: dict[str, list[dict[str, object]]] = {"sol": [], "terra": []}
    for item in manifest["items"]:
        route = item["conversion_route"]
        item_id = item["id"]
        packet_dir = args.output / route / Path(*item_id.split("/"))
        packet_dir.mkdir(parents=True, exist_ok=True)
        source = args.draft / "blobs" / f"{item_id}.md"
        if not source.exists():
            raise SystemExit(f"missing item source: {source}")
        packet_source = packet_dir / "source.md"
        if not (args.preserve_existing_sources and packet_source.exists()):
            shutil.copyfile(source, packet_source)
        packet_path = packet_dir / "packet.json"
        existing_packet = {}
        if args.preserve_existing_packet_metadata and packet_path.exists():
            existing_packet = json.loads(packet_path.read_text(encoding="utf-8"))
        packet = existing_packet | {
            "schema_version": 1,
            "item": item,
            "source_file": "source.md",
            "allowed_output": "Content.lean",
        }
        packet.setdefault("status", "unconverted")
        write_json_if_changed(packet_path, packet)
        batch_index[route].append(
            {
                "id": item_id,
                "node_id": item["node_id"],
                "packet": str(packet_dir.relative_to(args.output)),
            }
        )

    write_json_if_changed(
        args.output / "index.json",
        {"schema_version": 1, "routes": batch_index},
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Validate primary/supporting alignment adjudication responses."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("packets", type=Path)
    parser.add_argument("--require-all", action="store_true")
    args = parser.parse_args()

    errors: list[str] = []
    packet_count = association_count = primary_count = supporting_count = 0
    missing = 0
    for packet_path in sorted(args.packets.glob("*/align-*/packet.json")):
        response_path = packet_path.with_name("response.json")
        if not response_path.exists():
            missing += 1
            if args.require_all:
                errors.append(f"{response_path}: missing")
            continue
        try:
            packet = json.loads(packet_path.read_text(encoding="utf-8"))
            response = json.loads(response_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"{response_path}: {exc}")
            continue
        packet_count += 1
        if not isinstance(response, dict) or set(response) != {"packet_id", "associations"}:
            errors.append(f"{response_path}: expected only packet_id and associations")
            continue
        if response["packet_id"] != packet["packet_id"]:
            errors.append(f"{response_path}: packet_id mismatch")
        rows = response["associations"]
        if not isinstance(rows, list):
            errors.append(f"{response_path}: associations must be a list")
            continue
        expected = {row["association_id"] for row in packet["candidates"]}
        actual: list[str] = []
        for index, row in enumerate(rows):
            location = f"{response_path}: associations[{index}]"
            if not isinstance(row, dict) or set(row) != {"association_id", "role", "rationale"}:
                errors.append(f"{location}: invalid fields")
                continue
            actual.append(row["association_id"])
            if row["role"] not in {"primary", "supporting"}:
                errors.append(f"{location}: invalid role {row['role']!r}")
            elif row["role"] == "primary":
                primary_count += 1
            else:
                supporting_count += 1
            if not isinstance(row["rationale"], str) or len(row["rationale"].strip()) < 12:
                errors.append(f"{location}: rationale is too short")
        if len(actual) != len(set(actual)):
            errors.append(f"{response_path}: duplicate association IDs")
        if set(actual) != expected:
            errors.append(
                f"{response_path}: association coverage mismatch; "
                f"missing={sorted(expected - set(actual))}, extra={sorted(set(actual) - expected)}"
            )
        association_count += len(rows)

    if errors:
        for error in errors:
            print(error)
        raise SystemExit(1)
    print(json.dumps({
        "validated_packets": packet_count,
        "validated_associations": association_count,
        "primary": primary_count,
        "supporting": supporting_count,
        "missing_responses": missing,
    }, sort_keys=True))


if __name__ == "__main__":
    main()

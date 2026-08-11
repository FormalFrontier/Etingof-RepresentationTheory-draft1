#!/usr/bin/env python3
"""Build blind declaration naming/docstring packets from the frozen Lean environment.

The packets deliberately contain no source item identifiers, old declaration names,
old module names, filenames, book titles, or prose.  The private mapping stays in the
migration staging area and is never copied to either release repository.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
from collections import defaultdict
from pathlib import Path
from typing import Any


INCLUDED_DISPOSITIONS = {"include", "split_review"}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def sha256_json(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def blind_type(pretty: str, dependencies: list[str], ids: dict[str, str]) -> str:
    result = pretty
    # Full-name pretty printing makes dependency replacement exact.  Boundaries
    # prevent a short global name from changing a binder or a longer identifier.
    replacements: list[tuple[str, str]] = []
    for old_name in dependencies:
        temp_id = ids.get(old_name)
        if temp_id is None:
            continue
        replacements.append((old_name, temp_id))
        # Lean pretty-prints a private constant by its source-facing suffix and
        # may add one or more daggers to disambiguate it.  That alias must also
        # be blinded even though the environment dependency is the mangled FQN.
        if old_name.startswith("_private.") and ".0." in old_name:
            replacements.append((old_name.split(".0.", 1)[1], temp_id))
    for old_name, temp_id in sorted(replacements, key=lambda pair: len(pair[0]), reverse=True):
        pattern = rf"(?<![A-Za-z0-9_']){re.escape(old_name)}(?:[✝†]+)?(?![A-Za-z0-9_'])"
        result = re.sub(pattern, temp_id, result)
    return result


def route(records: list[dict[str, Any]]) -> str:
    type_chars = sum(len(record["pretty_type"]) for record in records)
    dependency_edges = sum(len(record["type_dependencies"]) for record in records)
    if len(records) > 25 or type_chars > 15_000 or dependency_edges > 80:
        return "sol"
    return "terra"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("declarations", type=Path)
    parser.add_argument("types", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("private_mapping", type=Path)
    args = parser.parse_args()

    declarations = read_jsonl(args.declarations)
    type_records = read_jsonl(args.types)
    by_name = {record["old_fqn"]: record for record in declarations}
    types_by_name = {record["old_fqn"]: record for record in type_records}
    if len(types_by_name) != len(type_records):
        raise SystemExit("duplicate declaration in type export")
    missing = sorted(set(by_name) - set(types_by_name))
    extra = sorted(set(types_by_name) - set(by_name))
    if missing or extra:
        raise SystemExit(f"type/declaration mismatch: missing={len(missing)} extra={len(extra)}")

    ids = {record["old_fqn"]: record["declaration_id"] for record in declarations}
    eligible: list[dict[str, Any]] = []
    for declaration in declarations:
        type_record = types_by_name[declaration["old_fqn"]]
        if declaration["visibility"] != "public" or declaration["compiler_generated"]:
            continue
        if declaration["module_disposition"] not in INCLUDED_DISPOSITIONS:
            continue
        if type_record["pretty_type"] is None:
            continue
        eligible.append({**declaration, **type_record})

    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for record in eligible:
        grouped[record["provider_module"]].append(record)
    eligible_names = {record["old_fqn"] for record in eligible}

    def owner_of(old_fqn: str) -> str | None:
        parts = old_fqn.split(".")
        for length in range(len(parts) - 1, 0, -1):
            candidate = ".".join(parts[:length])
            if candidate in eligible_names:
                return candidate
        return None

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    mapping_path = args.private_mapping.resolve()
    mapping_path.parent.mkdir(parents=True, exist_ok=True)
    prior_module_ids: dict[str, str] = {}
    if mapping_path.exists():
        for record in read_jsonl(mapping_path):
            module = record["old_module"]
            module_id = record["module_temporary_id"]
            previous = prior_module_ids.setdefault(module, module_id)
            if previous != module_id:
                raise SystemExit(f"inconsistent prior module ID for {module}")
    prior_modules_by_id: dict[str, str] = {}
    for module, module_id in prior_module_ids.items():
        previous = prior_modules_by_id.setdefault(module_id, module)
        if previous != module:
            raise SystemExit(
                f"prior module ID {module_id} is shared by {previous} and {module}"
            )
    used_ordinals = [
        int(module_id.removeprefix("module-"))
        for module_id in prior_module_ids.values()
        if module_id.startswith("module-") and module_id.removeprefix("module-").isdigit()
    ]
    next_module_ordinal = max(used_ordinals, default=0) + 1
    index_records: list[dict[str, Any]] = []
    mapping_records: list[dict[str, Any]] = []

    for module in sorted(grouped):
        module_id = prior_module_ids.get(module)
        if module_id is None:
            module_id = f"module-{next_module_ordinal:04d}"
            next_module_ordinal += 1
        records = sorted(grouped[module], key=lambda record: record["declaration_id"])
        packet_declarations = []
        for record in records:
            owner = owner_of(record["old_fqn"])
            dependencies = [
                ids[name] for name in record["type_dependencies"] if name in ids
            ]
            packet_declarations.append(
                {
                    "temporary_id": record["declaration_id"],
                    "kind": record["kind"],
                    "formal_type": blind_type(
                        record["pretty_type"], record["type_dependencies"], ids
                    ),
                    "structural_type_hash": record["structural_type_hash"],
                    "project_type_dependencies": dependencies,
                    "owner_temporary_id": ids[owner] if owner is not None else None,
                }
            )
            mapping_records.append(
                {
                    "module_temporary_id": module_id,
                    "temporary_id": record["declaration_id"],
                    "old_fqn": record["old_fqn"],
                    "old_module": module,
                    "owner_temporary_id": ids[owner] if owner is not None else None,
                }
            )
        suggested_model = route(records)
        packet = {
            "schema_version": "etingof-cleanroom-packet/v1",
            "module_temporary_id": module_id,
            "suggested_model": suggested_model,
            "declarations": packet_declarations,
            "required_response": {
                "module_name": "neutral semantic Lean module name",
                "declarations": [
                    {
                        "temporary_id": "decl-NNNNNN",
                        "new_name": "neutral semantic Lean identifier",
                        "docstring": "new description derived only from the displayed formal type",
                    }
                ],
            },
            "constraints": [
                "Use only this packet; do not inspect the source or private mapping.",
                "Do not mention any book, author, chapter, section, theorem, problem, or item number.",
                "Do not infer or reproduce an old name.",
                "Names must describe mathematical content and follow Mathlib conventions.",
                "When owner_temporary_id is present, new_name is relative to that renamed owner.",
                "Docstrings must be independently worded from the formal type only.",
                "Do not add the bibliographic alignment line; the migration tool appends it later.",
            ],
        }
        packet_dir = output / suggested_model / module_id
        packet_dir.mkdir(parents=True, exist_ok=True)
        packet_path = packet_dir / "packet.json"
        write_json(packet_path, packet)
        index_records.append(
            {
                "module_temporary_id": module_id,
                "route": suggested_model,
                "declaration_count": len(records),
                "packet": str(packet_path.relative_to(output)),
                "packet_sha256": sha256_json(packet),
            }
        )

    with mapping_path.open("w", encoding="utf-8") as stream:
        for record in mapping_records:
            stream.write(json.dumps(record, sort_keys=True) + "\n")
    index = {
        "schema_version": "etingof-cleanroom-index/v1",
        "module_count": len(index_records),
        "declaration_count": len(mapping_records),
        "routes": {
            "sol": sum(record["route"] == "sol" for record in index_records),
            "terra": sum(record["route"] == "terra" for record in index_records),
        },
        "packets": index_records,
    }
    active_packet_dirs = {
        (output / record["packet"]).parent.resolve() for record in index_records
    }
    for model in ("sol", "terra"):
        route_root = output / model
        if not route_root.exists():
            continue
        for packet_dir in sorted(route_root.glob("module-*")):
            if not packet_dir.is_dir() or packet_dir.resolve() in active_packet_dirs:
                continue
            retained_work = sorted(
                path.name for path in packet_dir.iterdir() if path.name != "packet.json"
            )
            if retained_work:
                raise SystemExit(
                    f"refusing to prune stale packet with response/work files: "
                    f"{packet_dir} ({retained_work})"
                )
            shutil.rmtree(packet_dir)
    write_json(output / "index.json", index)
    print(json.dumps({key: index[key] for key in ("module_count", "declaration_count", "routes")}))


if __name__ == "__main__":
    main()

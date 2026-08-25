#!/usr/bin/env python3
"""Join the frozen environment type export into the alignment declaration ledger."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("alignment_dir", type=Path)
    args = parser.parse_args()
    root = args.alignment_dir.resolve()
    declarations_path = root / "declarations.jsonl"
    types_path = root / "declaration-types.jsonl"
    manifest_path = root / "manifest.json"

    declarations = read_jsonl(declarations_path)
    type_records = read_jsonl(types_path)
    types_by_name = {record["old_fqn"]: record for record in type_records}
    if len(types_by_name) != len(type_records):
        raise SystemExit("duplicate old_fqn in declaration type export")
    declaration_names = {record["old_fqn"] for record in declarations}
    if declaration_names != set(types_by_name):
        raise SystemExit(
            f"type/declaration name mismatch: declarations={len(declaration_names)} "
            f"types={len(types_by_name)}"
        )

    pretty_count = 0
    provider_mismatch_count = 0
    for declaration in declarations:
        type_record = types_by_name[declaration["old_fqn"]]
        declaration["environment_provider_module"] = type_record["provider_module"]
        declaration["provider_reconciliation"] = (
            "match"
            if declaration["provider_module"] == type_record["provider_module"]
            else "equivalent_declaration_from_different_imported_module"
        )
        provider_mismatch_count += declaration["provider_reconciliation"] != "match"
        declaration["structural_type_hash"] = type_record["structural_type_hash"]
        declaration["pretty_type_available"] = type_record["pretty_type"] is not None
        pretty_count += declaration["pretty_type_available"]

    temp_path = declarations_path.with_suffix(".jsonl.tmp")
    with temp_path.open("w", encoding="utf-8") as stream:
        for record in declarations:
            stream.write(json.dumps(record, sort_keys=True) + "\n")
    temp_path.replace(declarations_path)

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["files"]["declaration_types"] = types_path.name
    manifest["counts"]["declaration_types"] = len(type_records)
    manifest["counts"]["pretty_declaration_types"] = pretty_count
    manifest["counts"]["environment_provider_mismatches"] = provider_mismatch_count
    manifest["snapshot"]["declaration_types_sha256"] = sha256_file(types_path)
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "declaration_types": len(type_records),
        "pretty_types": pretty_count,
        "environment_provider_mismatches": provider_mismatch_count,
    }))


if __name__ == "__main__":
    main()

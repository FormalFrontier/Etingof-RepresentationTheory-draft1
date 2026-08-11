#!/usr/bin/env python3
"""Build private primary/supporting-role adjudication packets."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from collections import defaultdict
from pathlib import Path


def load_ledger_module(path: Path):
    spec = importlib.util.spec_from_file_location("alignment_ledger_helpers", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def association_id(source_node: str, old_fqn: str) -> str:
    digest = hashlib.sha256(f"{source_node}\x1f{old_fqn}".encode()).hexdigest()[:20]
    return f"association:{digest}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("staging", type=Path)
    parser.add_argument("draft", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    staging = args.staging.resolve()
    draft = args.draft.resolve()
    alignment = staging / "manifests/alignment"
    helpers = load_ledger_module(staging / "build_alignment_ledger.py")

    nodes = {record["source_node"]: record for record in read_jsonl(alignment / "source-nodes.jsonl")}
    edges = read_jsonl(alignment / "alignment-edges.jsonl")
    types = {record["old_fqn"]: record for record in read_jsonl(alignment / "declaration-types.jsonl")}
    progress_items = json.loads((draft / "progress/items.json").read_text(encoding="utf-8"))
    overlays = json.loads((staging / "verso/metadata/overlays.json").read_text(encoding="utf-8"))["overlays"]

    source_text: dict[str, str] = {}
    derived_keys: dict[tuple[str, str, str], str] = {}
    for overlay in overlays:
        derived_keys[(overlay["parent_item_id"], overlay["source_span"], overlay["claim"])] = overlay["id"]
    canonical_ref: dict[str, str] = {}
    for item in progress_items:
        item_node, parent = helpers.item_identity(item)
        if item.get("id"):
            item_id = item["id"]
            blob = draft / "blobs" / f"{item_id}.md"
            source_text[item_node] = blob.read_text(encoding="utf-8") if blob.exists() else ""
            canonical_ref[item_node] = item_id
        else:
            text = str(item.get("claim") or item.get("source_span") or "")
            source_text[item_node] = text
            canonical_ref[item_node] = derived_keys[(parent, str(item.get("source_span", "")), str(item.get("claim", "")))]
        claims = ((item.get("claim_coverage") or {}).get("claims") or [])
        for ordinal, claim in enumerate(claims, start=1):
            if not isinstance(claim, dict):
                continue
            claim_node = helpers.claim_identity(item_node, claim, ordinal)
            source_text[claim_node] = str(
                claim.get("claim") or claim.get("text") or claim.get("description") or ""
            )
            canonical_ref[claim_node] = canonical_ref[item_node]

    grouped: dict[str, dict[str, list[dict]]] = defaultdict(lambda: defaultdict(list))
    for edge in edges:
        grouped[edge["source_node"]][edge["old_fqn"]].append(edge)

    output = args.output.resolve()
    index_records = []
    association_count = 0
    for ordinal, source_node in enumerate(sorted(grouped), start=1):
        candidates = []
        for old_fqn, duplicate_edges in sorted(grouped[source_node].items()):
            type_record = types.get(old_fqn)
            candidates.append({
                "association_id": association_id(source_node, old_fqn),
                "declaration": old_fqn,
                "provider_module": duplicate_edges[0].get("provider_module"),
                "formal_type": type_record.get("pretty_type") if type_record else None,
                "evidence": [
                    {
                        "authority": edge["authority"],
                        "pointer": edge["evidence_pointer"],
                        "verdict": edge.get("verdict"),
                    }
                    for edge in duplicate_edges
                ],
            })
        text = source_text.get(source_node, "")
        route = "sol" if len(candidates) > 3 or len(text) > 1200 else "terra"
        packet_id = f"align-{ordinal:04d}"
        packet = {
            "schema_version": "etingof-alignment-adjudication/v1",
            "packet_id": packet_id,
            "source_node": source_node,
            "canonical_reference": canonical_ref.get(source_node),
            "source_text": text,
            "candidates": candidates,
            "required_response": {
                "packet_id": packet_id,
                "associations": [
                    {
                        "association_id": "association:<hash>",
                        "role": "primary | supporting",
                        "rationale": "brief comparison of formal type with source text",
                    }
                ],
            },
            "rule": (
                "Use primary exactly when the declaration itself states or defines the source claim. "
                "Use supporting for prerequisites, constructions, helper lemmas, instances, or consequences "
                "that help formalize the item but do not themselves state it."
            ),
        }
        path = output / route / packet_id / "packet.json"
        write_json(path, packet)
        index_records.append({
            "packet_id": packet_id,
            "route": route,
            "packet": str(path.relative_to(output)),
            "association_count": len(candidates),
        })
        association_count += len(candidates)
    index = {
        "schema_version": "etingof-alignment-adjudication-index/v1",
        "packet_count": len(index_records),
        "association_count": association_count,
        "routes": {
            "sol": sum(record["route"] == "sol" for record in index_records),
            "terra": sum(record["route"] == "terra" for record in index_records),
        },
        "packets": index_records,
    }
    write_json(output / "index.json", index)
    print(json.dumps({key: index[key] for key in ("packet_count", "association_count", "routes")}))


if __name__ == "__main__":
    main()

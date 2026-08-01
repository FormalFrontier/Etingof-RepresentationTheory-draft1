#!/usr/bin/env python3
"""Validate the checked Stage 3.4/3.5 review certificates against the tree."""

from __future__ import annotations

import hashlib
import gzip
import json
from pathlib import Path
import argparse
import sys


ROOT = Path(__file__).resolve().parent.parent
STAGE34 = ROOT / "progress/reviews/2026-08-01-stage3-4-proof-terms.json"
STAGE35 = ROOT / "progress/reviews/2026-08-01-stage3-5-proof-polishing.json"
ITEMS = ROOT / "progress/items.json"
DEPENDENCIES = ROOT / "dependencies/internal.json"
EXTRACTOR = ROOT / "scripts/extract_proof_dependencies.lean"


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--strict-source-hashes", action="store_true",
        help="fail on Lean source drift; CI defaults to an informational notice so future Lean PRs are not frozen",
    )
    args = parser.parse_args()
    errors: list[str] = []
    source_drift: list[str] = []
    stage34 = json.loads(STAGE34.read_text(encoding="utf-8"))
    stage35 = json.loads(STAGE35.read_text(encoding="utf-8"))
    items = json.loads(ITEMS.read_text(encoding="utf-8"))
    dependencies = json.loads(DEPENDENCIES.read_text(encoding="utf-8"))

    if stage34["extractor_sha256"] != digest(EXTRACTOR):
        errors.append("Stage 3.4 extractor hash does not match the checked extractor")
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if stage34["lean_toolchain"] != toolchain:
        errors.append("Stage 3.4 Lean toolchain identity is stale")
    import_baseline = ROOT / stage34["import_dag_baseline"]
    if not import_baseline.exists() or digest(import_baseline) != stage34["import_dag_baseline_sha256"]:
        errors.append("Stage 3.4 import-DAG baseline is missing or hash-mismatched")
    raw_archive = ROOT / stage34["raw_extraction_archive"]
    if not raw_archive.exists() or hashlib.sha256(gzip.decompress(raw_archive.read_bytes())).hexdigest() != stage34["raw_extraction_sha256"]:
        errors.append("Stage 3.4 raw extraction archive is missing or hash-mismatched")
    for module, evidence in stage34["modules"].items():
        source = ROOT / evidence["source"]
        if not source.exists():
            source_drift.append(f"{module}: reviewed source no longer exists")
        elif digest(source) != evidence["source_sha256"]:
            source_drift.append(f"{module}: reviewed source hash is stale")
    if stage34["stale_imported_modules_without_source"]:
        errors.append("Stage 3.4 contains stale imported modules without current sources")
    if len(dependencies) != len([item for item in items if item.get("type") != "derived"]):
        errors.append("dependency graph key count differs from the partition ledger")
    if sum(map(len, dependencies.values())) != stage34["shipped_item_edge_count"]:
        errors.append("dependency graph edge count differs from the Stage 3.4 certificate")
    for item in items:
        if item.get("type") == "derived":
            continue
        recorded = (item.get("stage3_4") or {}).get("actual_internal_dependencies")
        if recorded != dependencies.get(item["id"]):
            errors.append(f"{item['id']}: Stage 3.4 dependencies differ from the shipped graph")

    if stage35["dependency_evidence_sha256"] != digest(STAGE34):
        errors.append("Stage 3.5 is not bound to the current Stage 3.4 certificate")
    build_archive = ROOT / stage35["build_log_archive"]
    if not build_archive.exists() or hashlib.sha256(gzip.decompress(build_archive.read_bytes())).hexdigest() != stage35["build_log_sha256"]:
        errors.append("Stage 3.5 build-log archive is missing or hash-mismatched")
    if stage35["blocking_proof_diagnostic_count"] != 0:
        errors.append("Stage 3.5 records blocking proof diagnostics")
    if stage35["provider_item_count"] != len(stage35["items"]):
        errors.append("Stage 3.5 provider-item count disagrees with its item map")
    if stage35["source_level_proof_declaration_count"] != stage34["proof_declaration_count"]:
        errors.append("Stage 3.5 proof inventory count differs from Stage 3.4")
    for module, evidence in stage35["modules"].items():
        source = ROOT / evidence["source"]
        if not source.exists():
            source_drift.append(f"{module}: Stage 3.5 source no longer exists")
        elif digest(source) != evidence["source_sha256"]:
            source_drift.append(f"{module}: Stage 3.5 source hash is stale")

    if any((item.get("stage3_4") or {}).get("status") != "complete" for item in items):
        errors.append("not every item has complete Stage 3.4 evidence")
    applicable = [
        item for item in items
        if (item.get("stage3_5") or {}).get("status") != "not_applicable"
    ]
    expected_applicable = stage35["provider_item_count"] + len(stage35["derived_items"])
    if len(applicable) != expected_applicable or any(
        (item.get("stage3_5") or {}).get("status") != "complete" for item in applicable
    ):
        errors.append("Stage 3.5 applicable partition disagrees with the certificate")

    if source_drift:
        if args.strict_source_hashes:
            errors.extend(source_drift)
        else:
            print(
                f"NOTICE: {len(source_drift)} reviewed source hash(es) drifted; "
                "regenerate the review certificates when the next release audit closes."
            )

    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print(
        f"VALIDATION PASSED: {len(items)} Stage 3.4 records, {len(applicable)} applicable Stage 3.5 records, "
        f"{stage34['proof_declaration_count']} source-level proofs, "
        f"{len(source_drift)} source-hash drift notice(s)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

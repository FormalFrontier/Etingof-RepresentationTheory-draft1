#!/usr/bin/env python3
"""Build the private module-disposition ledger for the clean export."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


SCHEMA_VERSION = 1
PACKAGE = "EtingofRepresentationTheory"
COVERAGE_CHECKERS = {
    f"{PACKAGE}/ExerciseCoverageDeclarations.lean",
    f"{PACKAGE}/MathlibCoverageDeclarations.lean",
}
SPECIAL_REVIEW = f"{PACKAGE}/Chapter2/Remark2_9_3.lean"


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=root, text=True, encoding="utf-8"
    ).strip()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def module_name(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def internal_imports(text: str) -> list[str]:
    imports = []
    for line in text.splitlines():
        match = re.match(rf"\s*(?:public\s+)?import\s+({PACKAGE}(?:\.[A-Za-z0-9_']+)*)\s*$", line)
        if match:
            imports.append(match.group(1))
    return sorted(set(imports))


def classify(path: str) -> tuple[str, str, list[str]]:
    if path.endswith("_Test.lean"):
        return "test", "exclude", ["downstream_api_test"]
    if path.startswith(f"{PACKAGE}/ClaimCoverageDeclarations/") or path in COVERAGE_CHECKERS:
        return "checker", "exclude", ["generated_coverage_checker"]
    if path == f"{PACKAGE}.lean" or re.fullmatch(rf"{PACKAGE}/Chapter[2-9]\.lean", path):
        return "aggregator", "regenerate", ["book_derived_aggregate"]
    if path == SPECIAL_REVIEW:
        return "scope_exception", "split_review", ["approved_proof_wanted_marker"]
    if path.startswith(f"{PACKAGE}/Infrastructure/"):
        return "infrastructure", "include", ["substantive_local_support"]
    return "substantive", "include", ["formalization_source"]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("repository", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = args.repository.resolve()

    tracked = git(root, "ls-files", "*.lean").splitlines()
    source_paths = [
        path
        for path in tracked
        if path == f"{PACKAGE}.lean" or path.startswith(f"{PACKAGE}/")
    ]
    records = []
    for relative in sorted(source_paths):
        path = root / relative
        text = path.read_text(encoding="utf-8")
        kind, disposition, reasons = classify(relative)
        records.append(
            {
                "path": relative,
                "module": module_name(relative),
                "kind": kind,
                "disposition": disposition,
                "reasons": reasons,
                "sha256": sha256(path),
                "internal_imports": internal_imports(text),
                "new_path": None,
                "new_module": None,
                "review_status": "pending",
            }
        )

    counts: dict[str, int] = {}
    for record in records:
        key = f"{record['disposition']}:{record['kind']}"
        counts[key] = counts.get(key, 0) + 1

    payload = {
        "schema_version": SCHEMA_VERSION,
        "source_repository": str(root),
        "source_commit": git(root, "rev-parse", "HEAD"),
        "source_tree": git(root, "rev-parse", "HEAD^{tree}"),
        "package": PACKAGE,
        "record_count": len(records),
        "counts": dict(sorted(counts.items())),
        "records": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

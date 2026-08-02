#!/usr/bin/env python3
"""Validate the final exercise/problem claim ledger.

Unlike ``validate_items.py``, which checks the page partition, this validator
checks the semantic coverage ratchet required by issue #8111.  In particular,
``covered_partial`` is not a generic work-in-progress state: it is permitted
only for the exact project-wide scope decisions and documented source
corrections listed in ``skipped-exercises.md``.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote

from reconcile_exercise_coverage import PARTIAL_SCOPE_REFS
from scope_refs import github_heading_slug


REPO_ROOT = Path(__file__).resolve().parent.parent
ITEMS_PATH = REPO_ROOT / "progress" / "items.json"

EXERCISE_COUNT = 102
CLAIM_COUNT = 407
ALLOWED_VERDICTS = {
    "formalized",
    "covered_elsewhere",
    "non_formalizable",
    "intentional_omission",
    "source_correction",
}
EXCEPTION_VERDICTS = {"intentional_omission", "source_correction"}
ALLOWED_PARTIALS = PARTIAL_SCOPE_REFS


def as_list(value: object) -> list[object]:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    return [value]


def file_paths(value: object) -> list[str]:
    result: list[str] = []
    for entry in as_list(value):
        result.extend(
            part.strip() for part in re.split(r"[;,]", str(entry)) if part.strip()
        )
    return result


def declaration_names(value: object) -> list[str]:
    """Expand the legacy semicolon-separated form into exact Lean names."""
    result: list[str] = []
    for entry in as_list(value):
        result.extend(part.strip() for part in str(entry).split(";") if part.strip())
    return result


def validate_scope_anchors(errors: list[str]) -> None:
    for item_id, scope_ref in ALLOWED_PARTIALS.items():
        path_text, separator, fragment = scope_ref.partition("#")
        scope_path = REPO_ROOT / path_text
        if not separator or not scope_path.is_file():
            errors.append(f"{item_id}: invalid scope document reference {scope_ref!r}")
            continue
        slugs = {
            github_heading_slug(line.lstrip("#").strip())
            for line in scope_path.read_text().splitlines()
            if line.startswith("#")
        }
        if unquote(fragment) not in slugs:
            errors.append(f"{item_id}: scope anchor does not resolve: {scope_ref!r}")


def main() -> int:
    items = json.loads(ITEMS_PATH.read_text())
    exercises = [item for item in items if item.get("type") == "exercise"]
    errors: list[str] = []
    validate_scope_anchors(errors)

    if len(exercises) != EXERCISE_COUNT:
        errors.append(f"expected {EXERCISE_COUNT} exercise/problem items, found {len(exercises)}")

    partial_ids = {item["id"] for item in exercises if item.get("coverage") == "covered_partial"}
    if partial_ids != set(ALLOWED_PARTIALS):
        errors.append(
            "covered_partial ids differ from the documented exception set:\n"
            f"  unexpected: {sorted(partial_ids - set(ALLOWED_PARTIALS))}\n"
            f"  missing: {sorted(set(ALLOWED_PARTIALS) - partial_ids)}"
        )

    verdict_counts: dict[str, int] = {verdict: 0 for verdict in ALLOWED_VERDICTS}
    total_claims = 0

    for item in exercises:
        item_id = item.get("id", "<missing id>")
        coverage = item.get("coverage")
        if coverage not in {"covered_full", "covered_partial"}:
            errors.append(f"{item_id}: terminal ledger has invalid coverage {coverage!r}")
        if item.get("fidelity") != "verified":
            errors.append(f"{item_id}: final source-claim audit is not projected to fidelity")
        for lean_file in file_paths(item.get("lean_file")):
            if not (REPO_ROOT / lean_file).is_file():
                errors.append(f"{item_id}: provider file does not exist: {lean_file}")

        claim_coverage = item.get("claim_coverage")
        if not isinstance(claim_coverage, dict):
            errors.append(f"{item_id}: missing claim_coverage object")
            continue
        if claim_coverage.get("status") != "complete":
            errors.append(f"{item_id}: claim_coverage audit is not complete")
        for field in ("definition_integrity", "statement_fidelity", "nonvacuity"):
            if claim_coverage.get(field) != "verified":
                errors.append(f"{item_id}: claim_coverage.{field} is not verified")
        claims = claim_coverage.get("claims")
        if not isinstance(claims, list) or not claims:
            errors.append(f"{item_id}: claim_coverage.claims must be a nonempty array")
            continue

        units: set[str] = set()
        has_exception = False
        declaration_usage: dict[tuple[str, ...], list[tuple[str, bool]]] = {}
        for index, claim in enumerate(claims, 1):
            where = f"{item_id} claim {index}"
            if not isinstance(claim, dict):
                errors.append(f"{where}: claim must be an object")
                continue
            unit = claim.get("unit")
            if not isinstance(unit, str) or not unit:
                errors.append(f"{where}: missing durable unit id")
            elif unit in units:
                errors.append(f"{where}: duplicate unit id {unit!r}")
            else:
                units.add(unit)

            if not isinstance(claim.get("claim"), str) or not claim["claim"].strip():
                errors.append(f"{where}: missing claim text/source-unit description")

            expected_source = f"blobs/{item_id}.md"
            if claim.get("source_ref") != expected_source:
                errors.append(f"{where}: source_ref must be {expected_source!r}")
            elif not (REPO_ROOT / expected_source).is_file():
                errors.append(f"{where}: source blob does not exist")

            verdict = claim.get("verdict")
            if verdict not in ALLOWED_VERDICTS:
                errors.append(f"{where}: unsupported verdict {verdict!r}")
                continue
            verdict_counts[verdict] += 1
            total_claims += 1

            if verdict in {"formalized", "covered_elsewhere", "source_correction"}:
                declarations = declaration_names(claim.get("lean_decl"))
                if not declarations:
                    errors.append(f"{where}: {verdict} unit has no exact Lean declaration pointer")
                for declaration in declarations:
                    if not re.fullmatch(r"[^\s,()/]+", declaration):
                        errors.append(
                            f"{where}: Lean declaration pointer is not an exact name: "
                            f"{declaration!r}"
                        )
                if declarations:
                    declaration_usage.setdefault(tuple(sorted(declarations)), []).append(
                        (str(unit), claim.get("shared_decl") is True)
                    )
                for lean_file in file_paths(claim.get("lean_file")):
                    if not (REPO_ROOT / lean_file).is_file():
                        errors.append(f"{where}: provider file does not exist: {lean_file}")

            if verdict in EXCEPTION_VERDICTS:
                has_exception = True
                expected_ref = ALLOWED_PARTIALS.get(item_id)
                if expected_ref is None:
                    errors.append(f"{where}: exception verdict is not allowed for this item")
                elif claim.get("scope_ref") != expected_ref:
                    errors.append(
                        f"{where}: scope_ref must be the exact documented entry {expected_ref!r}"
                    )

            if verdict == "non_formalizable":
                reason = claim.get("reason")
                if not isinstance(reason, str) or not reason.strip():
                    errors.append(f"{where}: non_formalizable unit has no explicit reason")

        for declarations, uses in declaration_usage.items():
            if len(uses) < 2:
                continue
            missing_opt_in = [unit for unit, shared in uses if not shared]
            if missing_opt_in:
                errors.append(
                    f"{item_id}: sibling units reuse the same declaration set without "
                    f"shared_decl opt-in: {missing_opt_in}; declarations={list(declarations)}"
                )

        if coverage == "covered_full" and has_exception:
            errors.append(f"{item_id}: covered_full item contains an exception verdict")
        if coverage == "covered_partial" and not has_exception:
            errors.append(f"{item_id}: covered_partial item has no scope/correction-justified unit")

    if total_claims != CLAIM_COUNT:
        errors.append(f"expected {CLAIM_COUNT} audited claim units, found {total_claims}")

    if errors:
        print("EXERCISE COVERAGE VALIDATION FAILED", file=sys.stderr)
        for error in errors:
            print(f"  ERROR: {error}", file=sys.stderr)
        return 1

    print("EXERCISE COVERAGE VALIDATION PASSED")
    print(f"  items: {len(exercises)}")
    print(f"  claim units: {total_claims}")
    print(f"  covered_full: {len(exercises) - len(partial_ids)}")
    print(f"  scope/correction partial: {len(partial_ids)}")
    print("  untracked gaps: 0")
    for verdict in sorted(verdict_counts):
        print(f"  {verdict}: {verdict_counts[verdict]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

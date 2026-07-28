#!/usr/bin/env python3
"""Classify Lean proof placeholders and enforce reviewed `proof_wanted` approvals.

The default mode is suitable while formalization is still in progress: it reports
ordinary `sorry` gaps as blocking completion, and fails for metadata errors, an
unapproved `proof_wanted`, any `admit`, or any project `axiom`/`constant`
declaration. `--enforce-completion` additionally fails while a `sorry` remains.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


APPROVED_STATUS = "scope_approved_proof_wanted"
APPROVAL_FIELD = "proof_wanted_approval"
APPROVAL_CLASSIFICATION = "approved_nonblocking"
APPROVAL_REQUIRED_FIELDS = {
    "classification",
    "declaration",
    "source",
    "scope_document",
    "scope_heading",
    "reason",
    "approved_by_issue",
}

TOKEN_RE = re.compile(r"\b(sorry|admit|proof_wanted)\b")
PROOF_WANTED_RE = re.compile(r"\bproof_wanted\s+([A-Za-z_][A-Za-z0-9_'.]*)")
AXIOM_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected)\s+)*(axiom|constant)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)


@dataclass(frozen=True)
class Marker:
    kind: str
    source: str
    line: int
    declaration: str | None = None

    def render(self) -> str:
        suffix = f" ({self.declaration})" if self.declaration else ""
        return f"{self.source}:{self.line}: {self.kind}{suffix}"


def code_without_comments_or_strings(source: str) -> str:
    """Replace Lean comments and strings with spaces while preserving newlines."""
    output = list(source)
    index = 0
    block_depth = 0
    in_string = False
    in_line_comment = False

    def blank(position: int) -> None:
        if output[position] != "\n":
            output[position] = " "

    while index < len(source):
        if in_line_comment:
            if source[index] == "\n":
                in_line_comment = False
            else:
                blank(index)
            index += 1
            continue

        if block_depth:
            if source.startswith("/-", index):
                blank(index)
                blank(index + 1)
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                blank(index)
                blank(index + 1)
                block_depth -= 1
                index += 2
            else:
                blank(index)
                index += 1
            continue

        if in_string:
            if source[index] == "\\" and index + 1 < len(source):
                blank(index)
                blank(index + 1)
                index += 2
            else:
                if source[index] == '"':
                    in_string = False
                blank(index)
                index += 1
            continue

        if source.startswith("--", index):
            blank(index)
            blank(index + 1)
            in_line_comment = True
            index += 2
        elif source.startswith("/-", index):
            blank(index)
            blank(index + 1)
            block_depth = 1
            index += 2
        elif source[index] == '"':
            blank(index)
            in_string = True
            index += 1
        else:
            index += 1

    return "".join(output)


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def scan_lean_file(root: Path, path: Path) -> list[Marker]:
    relative = path.relative_to(root).as_posix()
    code = code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    markers: list[Marker] = []

    for match in TOKEN_RE.finditer(code):
        kind = match.group(1)
        if kind == "proof_wanted":
            continue
        markers.append(Marker(kind, relative, line_number(code, match.start())))

    for match in AXIOM_RE.finditer(code):
        markers.append(
            Marker(
                f"project_{match.group(1)}",
                relative,
                line_number(code, match.start()),
                match.group(2),
            )
        )

    for match in PROOF_WANTED_RE.finditer(code):
        markers.append(
            Marker(
                "proof_wanted",
                relative,
                line_number(code, match.start()),
                match.group(1),
            )
        )

    return sorted(markers, key=lambda marker: (marker.line, marker.kind))


def load_approvals(root: Path, items_path: Path) -> tuple[dict[tuple[str, str], dict], list[str]]:
    errors: list[str] = []
    try:
        items = json.loads(items_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        return {}, [f"cannot read {items_path}: {error}"]

    if not isinstance(items, list):
        return {}, [f"{items_path} must contain a JSON array"]

    approvals: dict[tuple[str, str], dict] = {}
    for item in items:
        if not isinstance(item, dict):
            continue
        item_id = item.get("id", "<unknown item>")
        approval = item.get(APPROVAL_FIELD)
        if item.get("status") != APPROVED_STATUS:
            if approval is not None:
                errors.append(
                    f"{item_id}: {APPROVAL_FIELD} requires status {APPROVED_STATUS!r}"
                )
            continue
        if not isinstance(approval, dict):
            errors.append(f"{item_id}: missing object field {APPROVAL_FIELD}")
            continue

        missing = APPROVAL_REQUIRED_FIELDS - approval.keys()
        if missing:
            errors.append(f"{item_id}: approval is missing {sorted(missing)}")
            continue
        if approval["classification"] != APPROVAL_CLASSIFICATION:
            errors.append(
                f"{item_id}: approval classification must be {APPROVAL_CLASSIFICATION!r}"
            )
        for field in (
            "declaration",
            "source",
            "scope_document",
            "scope_heading",
            "reason",
        ):
            if not isinstance(approval[field], str) or not approval[field].strip():
                errors.append(f"{item_id}: approval field {field!r} must be nonempty text")
        if not isinstance(approval["approved_by_issue"], int) or approval["approved_by_issue"] <= 0:
            errors.append(f"{item_id}: approved_by_issue must be a positive issue number")
        if errors and any(error.startswith(f"{item_id}:") for error in errors):
            continue

        source = approval["source"]
        declaration = approval["declaration"]
        local_declaration = declaration.rsplit(".", 1)[-1]
        key = (source, local_declaration)
        if key in approvals:
            errors.append(f"{item_id}: duplicate approval for {source} ({declaration})")
            continue

        source_path = root / source
        if not source_path.is_file() or source_path.suffix != ".lean":
            errors.append(f"{item_id}: approved source does not exist as a Lean file: {source}")

        scope_path = root / approval["scope_document"]
        try:
            scope_text = scope_path.read_text(encoding="utf-8")
        except OSError as error:
            errors.append(f"{item_id}: cannot read scope document {scope_path}: {error}")
        else:
            for expected, label in (
                (item_id, "item id"),
                (declaration, "declaration"),
                (approval["scope_heading"], "scope heading"),
            ):
                if expected not in scope_text:
                    errors.append(
                        f"{item_id}: {label} {expected!r} is absent from "
                        f"{approval['scope_document']}"
                    )

        approvals[key] = {"item_id": item_id, **approval}

    return approvals, errors


def report_group(title: str, markers: list[Marker]) -> None:
    print(f"{title}: {len(markers)}")
    for marker in markers:
        print(f"  {marker.render()}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (default: parent of scripts/)",
    )
    parser.add_argument(
        "--items",
        type=Path,
        help="progress metadata (default: ROOT/progress/items.json)",
    )
    parser.add_argument(
        "--enforce-completion",
        action="store_true",
        help="fail if any blocking proof placeholder remains",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    items_path = args.items or root / "progress" / "items.json"
    approvals, metadata_errors = load_approvals(root, items_path)

    source_root = root / "EtingofRepresentationTheory"
    markers = [
        marker
        for path in sorted(source_root.rglob("*.lean"))
        for marker in scan_lean_file(root, path)
    ]
    proof_wanted = [marker for marker in markers if marker.kind == "proof_wanted"]
    blocking = [marker for marker in markers if marker.kind != "proof_wanted"]
    approved: list[Marker] = []
    unapproved: list[Marker] = []

    matched_approvals: set[tuple[str, str]] = set()
    for marker in proof_wanted:
        key = (marker.source, marker.declaration or "")
        if key in approvals:
            approved.append(marker)
            matched_approvals.add(key)
        else:
            unapproved.append(marker)

    for key, approval in approvals.items():
        if key not in matched_approvals:
            metadata_errors.append(
                f"{approval['item_id']}: approval has no matching proof_wanted marker "
                f"at {key[0]} ({approval['declaration']})"
            )

    report_group("Blocking proof placeholders", blocking)
    report_group("Approved non-blocking proof_wanted markers", approved)
    report_group("Unapproved proof_wanted markers (blocking)", unapproved)

    if metadata_errors:
        print(f"Approval metadata errors: {len(metadata_errors)}", file=sys.stderr)
        for error in metadata_errors:
            print(f"  {error}", file=sys.stderr)
    else:
        print(f"Approval metadata errors: 0")

    always_forbidden = [
        marker
        for marker in blocking
        if marker.kind == "admit" or marker.kind.startswith("project_")
    ]
    if metadata_errors or unapproved or always_forbidden:
        return 1
    if args.enforce_completion and blocking:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

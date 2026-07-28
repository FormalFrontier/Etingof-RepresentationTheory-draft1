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

from proof_wanted_policy import (
    APPROVAL_CLASSIFICATION,
    APPROVAL_FIELD,
    APPROVED_STATUS,
    approval_identity,
    validate_item_approval,
)

THEOREM_WANTED_KINDS = {"proof_wanted", "theorem_wanted"}
DATA_WANTED_KINDS = {"def_wanted", "instance_wanted"}
WANTED_KINDS = THEOREM_WANTED_KINDS | DATA_WANTED_KINDS
TOKEN_RE = re.compile(
    r"\b(sorryAx|sorry|admit|proof_wanted|theorem_wanted|def_wanted|instance_wanted)\b"
)
WANTED_RE = re.compile(
    r"\b(proof_wanted|theorem_wanted|def_wanted|instance_wanted)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
AXIOM_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])(axiom|constant)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
CHAR_RE = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|.)|[^\\'\n])'")


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
    raw_string_end: str | None = None
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

        if raw_string_end is not None:
            if source.startswith(raw_string_end, index):
                for position in range(index, index + len(raw_string_end)):
                    blank(position)
                index += len(raw_string_end)
                raw_string_end = None
            else:
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
        elif (
            source[index] == "r"
            and (index == 0 or not (source[index - 1].isalnum() or source[index - 1] in "_'."))
            and (raw_match := re.match(r'r(?P<hashes>#{0,16})"', source[index:]))
        ):
            hashes = raw_match.group("hashes")
            opening_length = len(hashes) + 2
            for position in range(index, index + opening_length):
                blank(position)
            index += opening_length
            raw_string_end = '"' + hashes
        elif char_match := CHAR_RE.match(source, index):
            for position in range(index, char_match.end()):
                blank(position)
            index = char_match.end()
        elif source[index] == '"':
            blank(index)
            in_string = True
            index += 1
        else:
            index += 1

    if block_depth:
        raise ValueError("unterminated block comment")
    if in_string or raw_string_end is not None:
        raise ValueError("unterminated string literal")
    return "".join(output)


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def scan_lean_file(root: Path, path: Path) -> list[Marker]:
    relative = path.relative_to(root).as_posix()
    code = code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    markers: list[Marker] = []

    for match in TOKEN_RE.finditer(code):
        kind = match.group(1)
        if kind in WANTED_KINDS:
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

    for match in WANTED_RE.finditer(code):
        markers.append(
            Marker(
                match.group(1),
                relative,
                line_number(code, match.start()),
                match.group(2),
            )
        )

    return sorted(markers, key=lambda marker: (marker.line, marker.kind))


def markdown_section(text: str, heading: str) -> str | None:
    """Return the Markdown section under an exact heading, including subsections."""
    heading_match = re.search(
        rf"(?m)^(?P<marks>#{{1,6}})[ \t]+{re.escape(heading)}[ \t]*$", text
    )
    if heading_match is None:
        return None
    level = len(heading_match.group("marks"))
    next_heading = re.search(
        rf"(?m)^#{{1,{level}}}[ \t]+", text[heading_match.end() :]
    )
    end = len(text) if next_heading is None else heading_match.end() + next_heading.start()
    return text[heading_match.end() : end]


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
        item_errors = validate_item_approval(item)
        errors.extend(item_errors)
        approval = item.get(APPROVAL_FIELD)
        if item.get("status") != APPROVED_STATUS:
            continue
        if item_errors or not isinstance(approval, dict):
            continue

        source = approval["source"]
        declaration = approval["declaration"]
        local_declaration = declaration.rsplit(".", 1)[-1]
        key = (source, local_declaration)
        if key in approvals:
            errors.append(f"{item_id}: duplicate approval for {source} ({declaration})")
            continue

        source_path = (root / source).resolve()
        if (
            not source_path.is_relative_to(root)
            or not source_path.is_file()
            or source_path.suffix != ".lean"
        ):
            errors.append(f"{item_id}: approved source does not exist as a Lean file: {source}")

        scope_path = root / approval["scope_document"]
        try:
            scope_text = scope_path.read_text(encoding="utf-8")
        except OSError as error:
            errors.append(f"{item_id}: cannot read scope document {scope_path}: {error}")
        else:
            section = markdown_section(scope_text, approval["scope_heading"])
            if section is None:
                errors.append(
                    f"{item_id}: scope heading {approval['scope_heading']!r} is absent "
                    f"from {approval['scope_document']}"
                )
                section = ""
            for expected, label in (
                (item_id, "item id"),
                (declaration, "declaration"),
            ):
                if expected not in section:
                    errors.append(
                        f"{item_id}: {label} {expected!r} is absent from "
                        f"{approval['scope_document']}"
                    )

        approvals[key] = {
            "item_id": item_id,
            "identity": approval_identity(item, approval),
            **approval,
        }

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
    source_paths = sorted(root.glob("*.lean")) + sorted(source_root.rglob("*.lean"))
    markers: list[Marker] = []
    for path in source_paths:
        try:
            markers.extend(scan_lean_file(root, path))
        except (OSError, ValueError) as error:
            metadata_errors.append(f"{path.relative_to(root)}: lexical scan failed: {error}")
    proof_wanted = [marker for marker in markers if marker.kind in THEOREM_WANTED_KINDS]
    blocking = [marker for marker in markers if marker.kind not in THEOREM_WANTED_KINDS]
    approved: list[Marker] = []
    unapproved: list[Marker] = []

    matched_approvals: set[tuple[str, str]] = set()
    for marker in proof_wanted:
        local_declaration = (marker.declaration or "").rsplit(".", 1)[-1]
        key = (marker.source, local_declaration)
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
    report_group("Approved non-blocking wanted-theorem markers", approved)
    report_group("Unapproved wanted-theorem markers (blocking)", unapproved)

    if metadata_errors:
        print(f"Approval metadata errors: {len(metadata_errors)}", file=sys.stderr)
        for error in metadata_errors:
            print(f"  {error}", file=sys.stderr)
    else:
        print("Approval metadata errors: 0")

    always_forbidden = [
        marker
        for marker in blocking
        if marker.kind in {"admit", "sorryAx", *DATA_WANTED_KINDS}
        or marker.kind.startswith("project_")
    ]
    if metadata_errors or unapproved or always_forbidden:
        return 1
    if args.enforce_completion and blocking:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

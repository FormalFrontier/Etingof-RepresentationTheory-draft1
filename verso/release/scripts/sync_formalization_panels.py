#!/usr/bin/env python3
# Copyright (c) 2026 American Mathematical Society. All rights reserved.
"""Regenerate Verso formalization panels from the pinned Lean release's attributes."""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path


PACKAGE = "IntroductionToRepresentationTheoryVerso"
PANEL_MARKER = "\n\n## Formalization\n"
REPRESENTATION_IMPORT = re.compile(r"^import RepresentationTheory(?:\.[A-Za-z0-9_'.]+)*\n", re.MULTILINE)

# The public export validator still requires the approved top-level docstring.
# Verso also expands inductive constructors, which are generated child declarations
# outside the clean-room proposal inventory. Permit missing child documentation only
# for the audited inductive whose constructors have no independently approved prose.
ALLOW_MISSING_SUBDOCSTRINGS = frozenset(
    {
        "RepresentationTheory.Algebra.ParameterizedComplexRelations.Relations",
    }
)


def docstring_directive(declaration: str) -> str:
    flag = " +allowMissing" if declaration in ALLOW_MISSING_SUBDOCSTRINGS else ""
    return f"{{Manual.docstring{flag} {declaration}}}"


def load_items(root: Path) -> list[dict]:
    payload = json.loads((root / "metadata/items.json").read_text(encoding="utf-8"))
    items = payload.get("items")
    if not isinstance(items, list):
        raise SystemExit("metadata/items.json does not contain an items array")
    return items


def load_rows(path: Path) -> list[dict]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, list):
        raise SystemExit("alignment export must be a JSON array")
    seen: set[tuple[str, str, str]] = set()
    rows = []
    for index, row in enumerate(payload):
        if not isinstance(row, dict) or set(row) != {"declaration", "reference", "role"}:
            raise SystemExit(f"alignment row {index} has the wrong schema")
        if row["role"] not in {"primary", "supporting"}:
            raise SystemExit(f"alignment row {index} has invalid role {row['role']!r}")
        if not all(isinstance(row[key], str) and row[key] for key in row):
            raise SystemExit(f"alignment row {index} contains a blank or non-string field")
        key = (row["declaration"], row["reference"], row["role"])
        if key in seen:
            raise SystemExit(f"duplicate alignment row: {key}")
        seen.add(key)
        rows.append(row)
    return rows


def resolve_item(reference: str, item_ids: set[str]) -> str:
    matches = [item_id for item_id in item_ids if reference == item_id or reference.startswith(item_id + "/")]
    if not matches:
        raise SystemExit(f"alignment reference does not resolve to a semantic item: {reference}")
    longest = max(len(item_id) for item_id in matches)
    winners = [item_id for item_id in matches if len(item_id) == longest]
    if len(winners) != 1:
        raise SystemExit(f"ambiguous semantic item for alignment reference {reference}: {winners}")
    return winners[0]


def panel(item_id: str, rows: list[dict]) -> str:
    # Multiple source nodes (including derived nodes) may map to the same
    # semantic item. Render each declaration once, with primary taking
    # precedence when those source-node edges have different roles.
    primary = {row["declaration"] for row in rows if row["role"] == "primary"}
    by_role = {
        "primary": primary,
        "supporting": {
            row["declaration"] for row in rows if row["role"] == "supporting"
        }
        - primary,
    }
    groups = []
    for role, title in (("primary", "Primary declarations"), ("supporting", "Supporting declarations")):
        declarations = sorted(by_role[role])
        if not declarations:
            continue
        body = [f"### {title}"]
        body.extend(docstring_directive(declaration) for declaration in declarations)
        groups.append("\n\n".join(body))
    return (
        PANEL_MARKER
        + "%%%\n"
        + f"tag := {json.dumps(item_id + '/formalization')}\n"
        + "number := false\n"
        + "%%%\n\n"
        + "\n\n".join(groups)
        + "\n"
    )


def content_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def update_content(source: str, item_id: str, rows: list[dict]) -> str:
    if source.count(PANEL_MARKER) > 1:
        raise SystemExit(f"multiple formalization panels in {item_id}")
    base = source.split(PANEL_MARKER, 1)[0].rstrip()
    base = REPRESENTATION_IMPORT.sub("", base)
    if rows:
        lines = base.splitlines(keepends=True)
        import_indices = [index for index, line in enumerate(lines) if line.startswith("import ")]
        if not import_indices:
            raise SystemExit(f"no import location in {item_id}")
        lines.insert(import_indices[-1] + 1, "import RepresentationTheory\n")
        base = "".join(lines).rstrip()
        return base + panel(item_id, rows)
    return base + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("alignment_json", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    root = Path(__file__).resolve().parent.parent
    items = load_items(root)
    by_id = {item["id"]: item for item in items}
    if len(by_id) != len(items):
        raise SystemExit("metadata/items.json contains duplicate item IDs")

    grouped: dict[str, list[dict]] = defaultdict(list)
    for row in load_rows(args.alignment_json):
        grouped[resolve_item(row["reference"], set(by_id))].append(row)

    changed = []
    checked = 0
    for item_id, item in by_id.items():
        path = content_path(root, item["verso_module"])
        if not path.exists():
            if grouped.get(item_id):
                raise SystemExit(f"aligned semantic item has no Content module: {item_id}")
            continue
        source = path.read_text(encoding="utf-8")
        updated = update_content(source, item_id, grouped.get(item_id, []))
        checked += 1
        if updated != source:
            changed.append(str(path.relative_to(root)))
            if not args.check:
                path.write_text(updated, encoding="utf-8")

    report = {"alignment_rows": sum(map(len, grouped.values())), "checked": checked, "changed": len(changed)}
    print(json.dumps(report, sort_keys=True))
    if args.check and changed:
        for path in changed[:20]:
            print(path)
        raise SystemExit("formalization panels are not synchronized")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Assemble converted item documents into the semantic Verso hierarchy."""

from __future__ import annotations

import argparse
import json
import re
import shutil
from collections import defaultdict
from pathlib import Path


PACKAGE = "IntroductionToRepresentationTheoryVerso"
AMS_COPYRIGHT_HEADER = """/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

"""


def module_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def node_module(node_id: str) -> str:
    parts = []
    for part in node_id.split("/"):
        words = part.replace("-", "_").split("_")
        parts.append("".join(word[:1].upper() + word[1:] for word in words))
    return PACKAGE + ".Structure." + ".".join(parts)


def write(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.suffix == ".lean" and not value.startswith(AMS_COPYRIGHT_HEADER):
        value = AMS_COPYRIGHT_HEADER + value
    path.write_text(value, encoding="utf-8")


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def add_formalization_panel(source: str, item: dict, declarations: list[dict]) -> str:
    if not declarations:
        return source
    lines = source.splitlines(keepends=True)
    last_import = max(i for i, line in enumerate(lines) if line.startswith("import "))
    existing_imports = {line.strip().removeprefix("import ") for line in lines if line.startswith("import ")}
    additions = [] if "RepresentationTheory" in existing_imports else ["import RepresentationTheory\n"]
    lines[last_import + 1 : last_import + 1] = additions
    source = "".join(lines)

    groups = []
    for role, title in (("primary", "Primary declarations"), ("supporting", "Supporting declarations")):
        rows = sorted(
            (row for row in declarations if row["role"] == role),
            key=lambda row: row["new_fqn"],
        )
        if not rows:
            continue
        body = [f"### {title}"]
        for row in rows:
            body.append(f"{{Manual.docstring {row['new_fqn']}}}")
        groups.append("\n\n".join(body))
    panel = (
        "\n\n## Formalization\n"
        "%%%\n"
        f"tag := {json.dumps(item['id'] + '/formalization')}\n"
        "number := false\n"
        "%%%\n\n"
        + "\n\n".join(groups)
        + "\n"
    )
    closing = re.compile(rf"\n+end\s+{re.escape(item['verso_module'])}\s*$")
    source = closing.sub("\n", source.rstrip())
    return source.rstrip() + panel


def projected_structure_body(source: str, item: dict) -> str:
    """Extract native blocks that belong directly to a semantic Structure node."""
    item_id = item["id"]
    lines = source.splitlines(keepends=True)
    marker = f"tag := {json.dumps(item_id)}"
    try:
        item_tag = next(index for index, line in enumerate(lines) if line.strip() == marker)
        metadata_end = next(
            index
            for index in range(item_tag + 1, len(lines))
            if lines[index].strip() == "%%%"
        )
    except StopIteration as error:
        raise SystemExit(f"cannot extract projected Structure body for {item_id}") from error
    body = "".join(lines[metadata_end + 1 :]).strip()
    if not body:
        raise SystemExit(f"empty projected Structure body for {item_id}")
    return body


def escape_inline(value: str) -> str:
    for old, new in (
        ("\\", r"\\"),
        ("`", r"\`"),
        ("[", r"\["),
        ("]", r"\]"),
        ("*", r"\*"),
        ("_", r"\_"),
        ("{", r"\{"),
        ("}", r"\}"),
    ):
        value = value.replace(old, new)
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("metadata", type=Path)
    parser.add_argument("packets", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--alignment-edges", type=Path)
    parser.add_argument("--source-nodes", type=Path)
    parser.add_argument("--cleanroom-proposals", type=Path)
    parser.add_argument("--available-declarations", type=Path)
    parser.add_argument("--approved-items", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    package_root = output / PACKAGE
    content_root = package_root / "Content"
    structure_root = package_root / "Structure"
    # These two trees are entirely generated.  Recreate them so removed or
    # renamed items cannot survive into a later release assembly.
    for generated_root in (content_root, structure_root):
        if generated_root.exists():
            shutil.rmtree(generated_root)
    content_root.mkdir(parents=True, exist_ok=True)
    structure_root.mkdir(parents=True, exist_ok=True)

    book = json.loads((args.metadata / "book.json").read_text(encoding="utf-8"))
    items = json.loads((args.metadata / "items.json").read_text(encoding="utf-8"))["items"]
    item_by_id = {item["id"]: item for item in items}
    approval = json.loads(args.approved_items.read_text(encoding="utf-8"))
    if approval.get("schema_version") != "verso-approved-items/v1":
        raise SystemExit(f"{args.approved_items}: unsupported approval schema")
    approved_rows = approval.get("items")
    if not isinstance(approved_rows, list) or not all(isinstance(value, str) for value in approved_rows):
        raise SystemExit(f"{args.approved_items}: items must be a list of item IDs")
    if len(approved_rows) != len(set(approved_rows)):
        raise SystemExit(f"{args.approved_items}: duplicate approved item IDs")
    approved = set(approved_rows)
    unknown_approvals = approved - set(item_by_id)
    if unknown_approvals:
        raise SystemExit(f"{args.approved_items}: unknown item IDs {sorted(unknown_approvals)}")
    panels: dict[str, list[dict]] = defaultdict(list)
    alignment_inputs = (
        args.alignment_edges,
        args.source_nodes,
        args.cleanroom_proposals,
        args.available_declarations,
    )
    if any(value is not None for value in alignment_inputs):
        if not all(value is not None for value in alignment_inputs):
            raise SystemExit(
                "alignment edges, source nodes, proposals, and available declarations "
                "must be supplied together"
            )
        nodes = {row["source_node"]: row for row in read_jsonl(args.source_nodes)}
        available_declarations = {
            row["declaration"]
            for row in json.loads(args.available_declarations.read_text(encoding="utf-8"))
        }
        proposals = {
            row["old_fqn"]: row
            for row in read_jsonl(args.cleanroom_proposals)
            if row.get("new_fqn") in available_declarations
        }
        combined: dict[tuple[str, str], dict] = {}
        for edge in read_jsonl(args.alignment_edges):
            if edge.get("adjudication_status") != "adjudicated":
                continue
            proposal = proposals.get(edge["old_fqn"])
            node = nodes.get(edge["source_node"])
            if proposal is None or node is None:
                continue
            item_id = (
                node.get("parent_item_id")
                if node.get("kind") == "derived"
                else node.get("item_id")
            )
            if item_id not in item_by_id:
                raise SystemExit(
                    f"source node {edge['source_node']} does not resolve to a semantic item"
                )
            key = (item_id, proposal["new_fqn"])
            previous = combined.get(key)
            role = edge["role"]
            if previous is None or (previous["role"] == "supporting" and role == "primary"):
                combined[key] = {
                    "new_fqn": proposal["new_fqn"],
                    "new_module": proposal["new_module"],
                    "role": role,
                }
        for (item_id, _), row in combined.items():
            panels[item_id].append(row)
        for rows in panels.values():
            rows.sort(key=lambda row: (row["role"] != "primary", row["new_fqn"]))
    converted: dict[str, dict] = {}
    inline_bodies: dict[str, str] = {}
    rendered_titles: dict[tuple[str, str], list[str]] = defaultdict(list)
    for content in sorted(args.packets.rglob("Content.lean")):
        packet = json.loads(content.with_name("packet.json").read_text(encoding="utf-8"))
        item = packet["item"]
        if item["id"] not in approved:
            continue
        if item["id"] in converted:
            raise SystemExit(f"duplicate converted item {item['id']}")
        source = content.read_text(encoding="utf-8")
        projection = item.get("verso_projection", {})
        structure_only = projection.get("structure_only", False)
        if projection.get("inline_in_structure", False):
            if not structure_only:
                raise SystemExit(f"inline Structure projection must be structure-only: {item['id']}")
            if panels.get(item["id"]):
                raise SystemExit(f"inline Structure projection cannot carry a formalization panel: {item['id']}")
            inline_bodies[item["id"]] = projected_structure_body(source, item)
        if not structure_only:
            heading = re.search(r"(?m)^#\s+(.+?)\s*$", source)
            if heading is None:
                raise SystemExit(f"converted item has no generated level-one heading: {item['id']}")
            metadata_item = item_by_id[item["id"]]
            rendered_titles[(metadata_item["node_id"], heading.group(1))].append(item["id"])
            target = module_path(output, item["verso_module"])
            item_source = add_formalization_panel(
                source, item, panels.get(item["id"], [])
            )
            write(target, item_source)
        converted[item["id"]] = item
    title_collisions = {
        key: ids for key, ids in rendered_titles.items() if len(ids) > 1
    }
    if title_collisions:
        details = "; ".join(
            f"node {node_id!r}, title {title!r}: {sorted(ids)}"
            for (node_id, title), ids in sorted(title_collisions.items())
        )
        raise SystemExit(f"same-parent generated item title collision: {details}")
    missing_approvals = approved - set(converted)
    if missing_approvals:
        raise SystemExit(f"approved items without Content.lean: {sorted(missing_approvals)}")
    rendered = {
        item_id: item
        for item_id, item in converted.items()
        if not item.get("verso_projection", {}).get("structure_only", False)
    }

    nodes = {node["node_id"]: node for node in book["nodes"]}
    children: dict[str | None, list[str]] = defaultdict(list)
    for node in book["nodes"]:
        children[node["parent_id"]].append(node["node_id"])

    available_nodes: set[str] = set()
    for node_id, node in reversed(list(nodes.items())):
        if any(
            item_id in rendered or item_id in inline_bodies
            for item_id in node["item_ids"]
        ) or any(
            child in available_nodes for child in children[node_id]
        ):
            available_nodes.add(node_id)

    for node_id, node in nodes.items():
        if node_id not in available_nodes:
            continue
        imports = ["import VersoManual"]
        body = []
        for item_id in node["item_ids"]:
            item = rendered.get(item_id)
            if item is not None:
                imports.append(f"import {item['verso_module']}")
                body.append(f"{{include 1 {item['verso_module']}}}")
            elif item_id in inline_bodies:
                body.append(inline_bodies[item_id])
            else:
                continue
        for child_id in children[node_id]:
            if child_id not in available_nodes:
                continue
            child_module = node_module(child_id)
            imports.append(f"import {child_module}")
            body.append(f"{{include 1 {child_module}}}")
        module = node_module(node_id)
        title = node["title"]
        number = node.get("number")
        display_title = f"{number}. {title}" if number else title
        display_title = escape_inline(display_title)
        source = "\n".join(imports) + "\n\nopen Verso.Genre Manual\n\n"
        source += f"namespace {module}\n\n"
        source += f"#doc (Manual) {json.dumps(display_title)} =>\n"
        source += "%%%\n"
        source += f"tag := {json.dumps(node_id)}\n"
        source += "number := false\n"
        source += "%%%\n\n"
        source += "\n\n".join(body) + "\n\n"
        # Deliberately leave this namespace open to EOF.  A closing `end`
        # after an included document part is parsed by Verso as trailing block
        # content and violates the header/blocks/subparts invariant.
        write(module_path(output, module), source)

    top_nodes = [node_id for node_id in children[None] if node_id in available_nodes]
    root_imports = ["import VersoManual"] + [f"import {node_module(node)}" for node in top_nodes]
    root_body = [f"{{include 0 {node_module(node)}}}" for node in top_nodes]
    root_source = "\n".join(root_imports) + "\n\nopen Verso.Genre Manual\n\n"
    root_source += f"#doc (Manual) {json.dumps(book['title'])} =>\n%%%\n"
    root_source += f"authors := {json.dumps(book['authors'])}\n%%%\n\n"
    root_source += "\n\n".join(root_body) + "\n"
    write(output / f"{PACKAGE}.lean", root_source)

    aggregate_imports = [f"import {PACKAGE}"]
    write(output / "GeneratedImports.lean", "\n".join(aggregate_imports) + "\n")
    print(json.dumps({
        "converted_items": len(converted),
        "rendered_items": len(rendered),
        "inline_items": len(inline_bodies),
        "available_nodes": len(available_nodes),
        "top_nodes": len(top_nodes),
        "total_items": len(item_by_id),
        "approved_items": len(approved),
        "formalization_panels": len(panels),
        "available_declarations": len(available_declarations) if all(alignment_inputs) else 0,
    }))


if __name__ == "__main__":
    main()

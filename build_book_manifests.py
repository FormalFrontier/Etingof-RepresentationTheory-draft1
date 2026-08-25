#!/usr/bin/env python3
"""Build semantic book, item, and overlay manifests from the draft corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
SUBSECTIONS_525 = [
    ("5.25.1", "Conjugacy classes"),
    ("5.25.2", "1-dimensional representations"),
    ("5.25.3", "Principal series"),
    ("5.25.4", "Complementary series"),
]
COMPOSITE_INTRODUCTION_PROJECTIONS: dict[str, dict[str, Any]] = {
    "Chapter2/Introduction": {
        "title": "Chapter 2 and Section 2.1 structural headings",
        "body_region": "none",
        "structure_only": True,
        "structural_headings": [
            {"node_id": "chapter-02", "source": "Chapter 2: Basic notions of representation theory"},
            {"node_id": "chapter-02/section-2-1", "source": "2.1. What is representation theory?"},
        ],
    },
    "Chapter3/Introduction": {
        "title": "Introduction to subrepresentations in semisimple representations",
        "body_region": "after_section_heading",
        "structure_only": False,
        "structural_headings": [
            {"node_id": "chapter-03", "source": "Chapter 3"},
            {"node_id": "chapter-03", "source": "General results of representation theory"},
            {
                "node_id": "chapter-03/section-3-1",
                "source": "3.1. Subrepresentations in semisimple representations",
            },
        ],
    },
    "Chapter4/Introduction": {
        "title": "Introduction to representations of finite groups",
        "body_region": "before_section_heading",
        "structure_only": True,
        "inline_in_structure": True,
        "content_node_id": "chapter-04",
        "structural_headings": [
            {"node_id": "chapter-04", "source": "Chapter 4"},
            {"node_id": "chapter-04", "source": "Representations of finite groups: Basic results"},
            {"node_id": "chapter-04/section-4-1", "source": "4.1. Maschke's theorem"},
        ],
    },
    "Chapter5/Introduction": {
        "title": "Introduction to the Frobenius-Schur indicator",
        "body_region": "after_section_heading",
        "structure_only": False,
        "structural_headings": [
            {
                "node_id": "chapter-05",
                "source": "Chapter 5. Representations of finite groups: Further results",
            },
            {"node_id": "chapter-05/section-5-1", "source": "5.1. Frobenius-Schur indicator"},
        ],
    },
}


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def digest_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def page_key(page: str) -> tuple[int, str]:
    if page.startswith("frontmatter-"):
        return int(page.split("-")[-1]), page
    return 8 + int(page), page


def position(page: str, line: int) -> tuple[int, int]:
    return page_key(page)[0], line


def slug(value: str) -> str:
    value = value.lower().replace("$", "")
    value = re.sub(r"[^a-z0-9]+", "-", value).strip("-")
    return value or "item"


def lean_segment(value: str) -> str:
    pieces = re.split(r"[^A-Za-z0-9]+", value)
    rendered = "".join(piece[:1].upper() + piece[1:] for piece in pieces if piece)
    if not rendered:
        rendered = "Item"
    if rendered[0].isdigit():
        rendered = "N" + rendered
    return rendered


def source_blob(root: Path, item_id: str) -> str:
    path = root / "blobs" / f"{item_id}.md"
    if not path.exists():
        raise SystemExit(f"missing source blob for {item_id}: {path}")
    return path.read_text(encoding="utf-8")


def markdown_headings(text: str) -> list[str]:
    return [
        match.group(1).strip()
        for line in text.splitlines()
        if (match := re.match(r"^\s*#{1,6}\s+(.*?)\s*$", line))
    ]


def validate_composite_projection(item_id: str, text: str, projection: dict[str, Any]) -> None:
    expected_headings = [row["source"] for row in projection["structural_headings"]]
    actual_headings = markdown_headings(text)
    if actual_headings != expected_headings:
        raise SystemExit(
            f"{item_id}: structural heading projection is stale: "
            f"expected {expected_headings!r}, found {actual_headings!r}"
        )
    lines = text.splitlines()
    section_heading = next(
        index
        for index, line in enumerate(lines)
        if re.match(r"^\s*##+\s+", line)
    )

    def prose_in(region: list[str]) -> bool:
        return any(line.strip() and not re.match(r"^\s*#{1,6}\s+", line) for line in region)

    before = prose_in(lines[:section_heading])
    after = prose_in(lines[section_heading + 1 :])
    expected_regions = {
        "none": (False, False),
        "before_section_heading": (True, False),
        "after_section_heading": (False, True),
    }
    expected = expected_regions[projection["body_region"]]
    if (before, after) != expected:
        raise SystemExit(
            f"{item_id}: projected body region is stale: "
            f"expected {expected}, found {(before, after)}"
        )


def feature_profile(text: str, crosses_page: bool) -> dict[str, Any]:
    lines = text.splitlines()
    table_rows = sum(bool(re.match(r"^\s*\|.*\|\s*$", line)) for line in lines)
    footnote_definitions = sum(bool(re.match(r"^\[\^[^]]+\]:", line)) for line in lines)
    fences = sum(line.lstrip().startswith("```") for line in lines)
    display_delimiters = text.count("$$")
    profile = {
        "line_count": len(lines),
        "crosses_page": crosses_page,
        "display_math_delimiters": display_delimiters,
        "table_rows": table_rows,
        "footnote_definitions": footnote_definitions,
        "code_fences": fences,
    }
    profile["complex"] = bool(
        crosses_page
        or len(lines) > 60
        or display_delimiters >= 20
        or table_rows
        or footnote_definitions
        or fences
    )
    return profile


def find_heading(
    pages: dict[str, list[str]], label: str, fallback_page: str
) -> tuple[str, int, list[dict[str, Any]]]:
    label_pattern = re.escape(label)
    patterns = [
        re.compile(rf"^\s*#{{1,6}}\s+{label_pattern}(?:\.|\s|$)"),
        re.compile(rf"^\s*\*\*{label_pattern}(?:\.|\s|\*)"),
    ]
    matches: list[tuple[str, int]] = []
    for page, lines in pages.items():
        for index, line in enumerate(lines, start=1):
            if any(pattern.search(line) for pattern in patterns):
                matches.append((page, index))
    matches.sort(key=lambda value: position(*value))
    if matches:
        page, line = matches[0]
    else:
        page, line = fallback_page, 1
    sources = [
        {"page": match_page, "line": match_line, "primary": i == 0}
        for i, (match_page, match_line) in enumerate(matches)
    ]
    return page, line, sources


def build_nodes(root: Path, chapter_map: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    pages = {
        path.stem: path.read_text(encoding="utf-8").splitlines()
        for path in (root / "pages").glob("*.md")
        if path.name != "CONVENTIONS.md"
    }
    nodes: list[dict[str, Any]] = [
        {
            "node_id": "frontmatter",
            "kind": "frontmatter",
            "parent_id": None,
            "number": None,
            "title": "Frontmatter",
            "slug": "frontmatter",
            "start": {"page": "frontmatter-1", "line": 1},
            "heading_sources": [],
        }
    ]
    by_chapter: dict[str, list[dict[str, Any]]] = {}
    for chapter in chapter_map["chapters"]:
        chapter_id = f"chapter-{chapter['number']:02d}"
        chapter_node = {
            "node_id": chapter_id,
            "kind": "chapter",
            "parent_id": None,
            "number": str(chapter["number"]),
            "title": chapter["title"],
            "slug": chapter_id,
            "start": {"page": chapter["start_page"], "line": 1},
            "heading_sources": [],
        }
        nodes.append(chapter_node)
        chapter_nodes = [chapter_node]
        for section in chapter["sections"]:
            section_label = section["id"]
            page, line, sources = find_heading(pages, section_label, section["start_page"])
            section_id = f"{chapter_id}/section-{section_label.replace('.', '-')}"
            section_node = {
                "node_id": section_id,
                "kind": "section",
                "parent_id": chapter_id,
                "number": section_label,
                "title": section["title"],
                "slug": f"section-{section_label.replace('.', '-')}",
                "start": {"page": page, "line": line},
                "heading_sources": sources,
            }
            nodes.append(section_node)
            chapter_nodes.append(section_node)
            if section_label == "5.25":
                for subsection_label, title in SUBSECTIONS_525:
                    sub_page, sub_line, sub_sources = find_heading(
                        pages, subsection_label, section["start_page"]
                    )
                    subsection_id = (
                        f"{section_id}/subsection-{subsection_label.replace('.', '-')}"
                    )
                    subsection_node = {
                        "node_id": subsection_id,
                        "kind": "subsection",
                        "parent_id": section_id,
                        "number": subsection_label,
                        "title": title,
                        "slug": f"subsection-{subsection_label.replace('.', '-')}",
                        "start": {"page": sub_page, "line": sub_line},
                        "heading_sources": sub_sources,
                    }
                    nodes.append(subsection_node)
                    chapter_nodes.append(subsection_node)
        by_chapter[f"Chapter{chapter['number']}"] = chapter_nodes
    nodes.append(
        {
            "node_id": "backmatter",
            "kind": "backmatter",
            "parent_id": None,
            "number": None,
            "title": "Backmatter",
            "slug": "backmatter",
            "start": {"page": "221", "line": 1},
            "heading_sources": [],
        }
    )
    return nodes, by_chapter


def semantic_heading_position(text: str, label: str) -> int | None:
    """Return the first explicit Markdown heading for ``label`` in ``text``.

    The negative digit lookahead is significant for nested numbering: a
    heading for 5.25.1 must not also count as an explicit heading for 5.25.
    """
    label_pattern = re.escape(label)
    patterns = [
        re.compile(rf"^\s*#{{1,6}}\s+{label_pattern}(?:\.(?!\d)|\s|$)", re.MULTILINE),
        re.compile(rf"^\s*\*\*{label_pattern}(?:\.(?!\d)|\s|\*)", re.MULTILINE),
    ]
    matches = [match.start() for pattern in patterns if (match := pattern.search(text))]
    return min(matches) if matches else None


def assign_node(
    item: dict[str, Any],
    by_chapter: dict[str, list[dict[str, Any]]],
    text: str,
) -> str:
    item_id = item["id"]
    if item_id.startswith("Frontmatter/"):
        return "frontmatter"
    if item_id.startswith("Backmatter/"):
        return "backmatter"
    chapter_match = re.match(r"(Chapter\d+)/", item_id)
    if not chapter_match:
        raise SystemExit(f"cannot determine chapter for {item_id}")
    candidates = by_chapter[chapter_match.group(1)]
    semantic_candidates = [
        (node, heading_position)
        for node in candidates
        if node["kind"] in {"section", "subsection"}
        and (heading_position := semantic_heading_position(text, node["number"])) is not None
    ]
    if semantic_candidates:
        return max(
            semantic_candidates,
            key=lambda candidate: (
                candidate[0]["node_id"].count("/"),
                candidate[1],
            ),
        )[0]["node_id"]
    start = position(item["start_page"], item["start_line"])
    eligible = [
        node
        for node in candidates
        if position(node["start"]["page"], node["start"]["line"]) <= start
    ]
    if not eligible:
        return candidates[0]["node_id"]
    return max(
        eligible,
        key=lambda node: position(node["start"]["page"], node["start"]["line"]),
    )["node_id"]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("repository", type=Path)
    parser.add_argument("output_directory", type=Path)
    args = parser.parse_args()
    root = args.repository.resolve()
    output = args.output_directory.resolve()
    output.mkdir(parents=True, exist_ok=True)

    chapter_map = read_json(root / "pages/chapter_map.json")
    progress_items = read_json(root / "progress/items.json")
    # The enriched catalog contains twelve corrected structural records that are
    # stale in the root projection.  Keep only its 583 partition records here;
    # workflow fields are deliberately not copied into the release manifest.
    raw_items = [item for item in progress_items if item.get("id")]
    nodes, by_chapter = build_nodes(root, chapter_map)

    converted_items = []
    for item in sorted(
        raw_items,
        key=lambda value: position(value["start_page"], value["start_line"]),
    ):
        text = source_blob(root, item["id"])
        projection = COMPOSITE_INTRODUCTION_PROJECTIONS.get(item["id"])
        if projection is not None:
            validate_composite_projection(item["id"], text, projection)
        profile = feature_profile(text, item["start_page"] != item["end_page"])
        module_suffix = ".".join(lean_segment(part) for part in item["id"].split("/"))
        assigned_node = assign_node(item, by_chapter, text)
        if projection is not None:
            assigned_node = projection.get("content_node_id", assigned_node)
        converted_item = {
            "id": item["id"],
            "kind": item["type"],
            "title": projection["title"] if projection is not None else item["title"],
            "node_id": assigned_node,
            "order": len(converted_items) + 1,
            "slug": slug(item["id"].split("/")[-1]),
            "span": {
                "start": {"page": item["start_page"], "line": item["start_line"]},
                "end": {"page": item["end_page"], "line": item["end_line"]},
            },
            "source_sha256": digest_text(text),
            "features": profile,
            "conversion_route": "sol" if profile["complex"] else "terra",
            "verso_module": f"IntroductionToRepresentationTheoryVerso.Content.{module_suffix}",
            "verso_document": f"IntroductionToRepresentationTheoryVerso.Content.{module_suffix}",
        }
        if projection is not None:
            converted_item["verso_projection"] = {
                key: value for key, value in projection.items() if key not in {"content_node_id", "title"}
            }
        converted_items.append(converted_item)

    derived = [item for item in progress_items if not item.get("id")]
    overlay_counts: dict[str, int] = {}
    overlays = []
    for record in derived:
        parent = record["derived_from"]
        overlay_counts[parent] = overlay_counts.get(parent, 0) + 1
        overlays.append(
            {
                "id": f"{parent}/Derived{overlay_counts[parent]:02d}",
                "parent_item_id": parent,
                "source_span": record.get("source_span"),
                "claim": record.get("claim"),
            }
        )

    item_ids_by_node: dict[str, list[str]] = {node["node_id"]: [] for node in nodes}
    for item in converted_items:
        item_ids_by_node[item["node_id"]].append(item["id"])
    for node in nodes:
        node["item_ids"] = item_ids_by_node[node["node_id"]]

    book_payload = {
        "schema_version": SCHEMA_VERSION,
        "work_id": "EtingofEtAl-IntroductionToRepresentationTheory",
        "title": chapter_map["book"],
        "authors": chapter_map["authors"],
        "nodes": nodes,
    }
    item_payload = {"schema_version": SCHEMA_VERSION, "items": converted_items}
    overlay_payload = {"schema_version": SCHEMA_VERSION, "overlays": overlays}
    for name, payload in (
        ("book.json", book_payload),
        ("items.json", item_payload),
        ("overlays.json", overlay_payload),
    ):
        (output / name).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

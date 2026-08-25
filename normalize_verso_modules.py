#!/usr/bin/env python3
"""Normalize converted items into composable, item-shaped Verso documents."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import re
from pathlib import Path


def escape_inline(value: str) -> str:
    """Escape punctuation that Verso's inline parser can interpret as markup."""
    # Backslash must be escaped first.  The remaining characters are the
    # punctuation used by the titles in this corpus that can open/close markup.
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


def item_discriminator(item_id: str) -> str:
    """Render the stable item-ID leaf as a compact human-readable label."""
    leaf = item_id.rsplit("/", 1)[-1].replace("_", " ")
    leaf = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", leaf)
    leaf = re.sub(r"(?<=[A-Za-z])(?=\d)", " ", leaf)
    return " ".join(leaf.split())


def markdown_heading_count(text: str) -> int:
    count = 0
    fence: str | None = None
    for line in text.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            token = stripped[:3]
            fence = None if fence == token else token if fence is None else fence
        elif fence is None and re.match(r"^#+\s", line):
            count += 1
    return count


def tag_source_headings(
    text: str, item_id: str, title: str, expected_heading_count: int
) -> str:
    """Give every source heading a stable, item-scoped Verso tag."""
    lines = text.splitlines(keepends=True)
    marker = f"tag := {json.dumps(item_id)}"
    try:
        generated_tag = next(i for i, line in enumerate(lines) if line.strip() == marker)
        generated_metadata_end = next(
            i for i in range(generated_tag + 1, len(lines)) if lines[i].strip() == "%%%"
        )
    except StopIteration:
        return text

    i = generated_metadata_end + 1
    # An early version inserted an untagged item header.  Remove that legacy
    # header when it makes the converted fragment contain more headings than
    # its source Markdown.  Genuine source headings are never removed.
    heading_starts: list[int] = []
    fence: str | None = None
    for j in range(i, len(lines)):
        stripped = lines[j].lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            token = stripped[:3]
            fence = None if fence == token else token if fence is None else fence
        elif fence is None and re.match(r"^#+\s", lines[j]):
            heading_starts.append(j)
    if len(heading_starts) > expected_heading_count:
        legacy = heading_starts[0]
        legacy_title = re.sub(r"^#+\s+", "", lines[legacy].rstrip("\n"))
        if legacy_title == escape_inline(title):
            legacy_end = legacy + 1
            if legacy_end < len(lines) and lines[legacy_end].strip() == "%%%":
                legacy_end = next(
                    j + 1
                    for j in range(legacy_end + 1, len(lines))
                    if lines[j].strip() == "%%%"
                )
            del lines[legacy:legacy_end]

    heading_number = 0
    fence: str | None = None
    while i < len(lines):
        stripped = lines[i].lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            token = stripped[:3]
            fence = None if fence == token else token if fence is None else fence
            i += 1
            continue
        if fence is not None or re.match(r"^#+\s", lines[i]) is None:
            i += 1
            continue

        if i > 0 and lines[i - 1].strip():
            lines.insert(i, "\n")
            i += 1
        heading_number += 1
        tag_line = f"tag := {json.dumps(f'{item_id}/heading-{heading_number}')}\n"
        if i + 1 < len(lines) and lines[i + 1].strip() == "%%%":
            metadata_end = next(
                (
                    j
                    for j in range(i + 2, len(lines))
                    if lines[j].strip() == "%%%"
                ),
                None,
            )
            if metadata_end is None:
                raise SystemExit(f"unterminated heading metadata in {item_id}")
            existing_tag = next(
                (
                    j
                    for j in range(i + 2, metadata_end)
                    if lines[j].lstrip().startswith("tag :=")
                ),
                None,
            )
            if existing_tag is None:
                lines.insert(i + 2, tag_line)
                metadata_end += 1
            elif f'{item_id}/heading-' in lines[existing_tag]:
                lines[existing_tag] = tag_line
            i = metadata_end + 1
        else:
            lines[i + 1 : i + 1] = ["%%%\n", tag_line, "%%%\n"]
            i += 4
    return "".join(lines)


def remove_projected_source_headings(text: str, item_id: str, expected_count: int) -> str:
    """Remove source headings represented by semantic Structure documents.

    Projection is deliberately all-or-nothing for an item.  This keeps the
    operation idempotent and rejects a partially projected Content module.
    """
    if expected_count == 0:
        return text
    lines = text.splitlines(keepends=True)
    marker = f"tag := {json.dumps(item_id)}"
    try:
        generated_tag = next(i for i, line in enumerate(lines) if line.strip() == marker)
        generated_metadata_end = next(
            i for i in range(generated_tag + 1, len(lines)) if lines[i].strip() == "%%%"
        )
    except StopIteration as error:
        raise SystemExit(f"missing generated item metadata in {item_id}") from error
    heading_starts = [
        index
        for index in range(generated_metadata_end + 1, len(lines))
        if re.match(r"^#+\s", lines[index])
    ]
    if not heading_starts:
        return text
    if len(heading_starts) != expected_count:
        raise SystemExit(
            f"{item_id}: expected {expected_count} projected source headings, "
            f"found {len(heading_starts)}"
        )
    for start in reversed(heading_starts):
        end = start + 1
        if end < len(lines) and lines[end].strip() == "%%%":
            try:
                end = next(
                    index + 1
                    for index in range(end + 1, len(lines))
                    if lines[index].strip() == "%%%"
                )
            except StopIteration as error:
                raise SystemExit(f"unterminated projected heading metadata in {item_id}") from error
        del lines[start:end]
    return "".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("packets", type=Path)
    args = parser.parse_args()
    content_paths = sorted(args.packets.rglob("Content.lean"))
    title_counts = Counter(
        (
            packet["item"]["node_id"],
            packet["item"]["title"],
        )
        for path in content_paths
        for packet in [json.loads(path.with_name("packet.json").read_text(encoding="utf-8"))]
    )
    changed = checked = 0
    for content_path in content_paths:
        packet_path = content_path.with_name("packet.json")
        source_path = content_path.with_name("source.md")
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        expected_hash = packet["item"]["source_sha256"]
        actual_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
        if actual_hash != expected_hash:
            raise SystemExit(f"source hash mismatch: {source_path}")
        module = packet["item"]["verso_module"]
        item_id = packet["item"]["id"]
        text = content_path.read_text(encoding="utf-8")
        title = packet["item"]["title"]
        display_title = (
            f"{item_discriminator(item_id)} — {title}"
            if title_counts[(packet["item"]["node_id"], title)] > 1
            else title
        )
        has_namespace = bool(re.search(rf"(?m)^namespace {re.escape(module)}$", text))
        other_namespaces = re.findall(r"(?m)^namespace\s+([^\s]+)\s*$", text)
        if other_namespaces and not has_namespace:
            raise SystemExit(f"unexpected namespace in {content_path}: {other_namespaces}")
        match = re.search(r"(?m)^def content\s*:=\s*#doc\s+\(Manual\)", text)
        if match is not None:
            text = text[: match.start()] + "#doc (Manual)" + text[match.end():]
        elif not re.search(r"(?m)^#doc\s+\(Manual\)", text):
            raise SystemExit(f"missing `#doc (Manual)` in {content_path}")
        if not has_namespace:
            doc_match = re.search(r"(?m)^#doc\s+\(Manual\)", text)
            assert doc_match is not None
            text = text[: doc_match.start()] + f"namespace {module}\n\n" + text[doc_match.start():]
            text = text.rstrip() + "\n"

        # The title on #doc is metadata for the standalone fragment.  Its
        # leading level-one header makes the fragment an actual item part when
        # included beneath a section/subsection document.
        doc = re.search(
            r'(?m)^#doc\s+\(Manual\)(?:[ \t]+"(?:[^"\\]|\\.)*")?[ \t]*=>[ \t]*$',
            text,
        )
        if doc is None:
            raise SystemExit(f"unrecognized `#doc` declaration in {content_path}")
        doc_line = f"#doc (Manual) {json.dumps(escape_inline(display_title))} =>"
        text = text[: doc.start()] + doc_line + text[doc.end():]
        old_header = (
            f"\n\n# {escape_inline(title)}\n"
            "%%%\n"
            "number := false\n"
            "%%%"
        )
        header = (
            f"\n\n# {escape_inline(display_title)}\n"
            "%%%\n"
            f"tag := {json.dumps(item_id)}\n"
            "number := false\n"
            "%%%"
        )
        marker = f"tag := {json.dumps(item_id)}"
        insertion = doc.start() + len(doc_line)
        if marker not in text:
            # Existing source headings become children of the generated item
            # heading.  This is done only while adding the stable item tag.
            if text.startswith(old_header, insertion):
                body_start = insertion + len(old_header)
                text = text[:insertion] + header + text[body_start:]
                body_start = insertion + len(header)
            else:
                text = text[:insertion] + header + text[insertion:]
                body_start = insertion + len(header)
            text = text[:body_start] + re.sub(
                r"(?m)^(#+)(?=\s)", r"#\1", text[body_start:]
            )
        else:
            # Keep the generated item's displayed title synchronized, notably
            # when duplicate packet titles need a deterministic disambiguator.
            lines = text.splitlines(keepends=True)
            marker_index = next(i for i, line in enumerate(lines) if line.strip() == marker)
            heading_index = next(
                i
                for i in range(marker_index - 1, -1, -1)
                if re.match(r"^#\s", lines[i])
            )
            newline = "\n" if lines[heading_index].endswith("\n") else ""
            lines[heading_index] = f"# {escape_inline(display_title)}{newline}"
            text = "".join(lines)

        # Markdown citation-like text such as ``[FH]`` has its opener escaped
        # during native conversion.  Verso also requires the matching closer
        # to be escaped; doing so does not change the rendered prose.
        # Do not scan across native math (`$`...``): in prose such as
        # ``\[Hint: ... $`k[G]_2` ...\]`` the first `]` belongs to TeX, not to
        # the outer bracketed prose.
        text = re.sub(r"\\\[([^\]\n$]*?)(?<!\\)\]", r"\\[\1\\]", text)
        source_heading_count = markdown_heading_count(source_path.read_text(encoding="utf-8"))
        projection = packet["item"].get("verso_projection")
        projected_heading_count = (
            len(projection["structural_headings"]) if projection is not None else 0
        )
        text = remove_projected_source_headings(text, item_id, projected_heading_count)
        text = tag_source_headings(
            text,
            item_id,
            title,
            source_heading_count - projected_heading_count,
        )
        # A `#doc` body extends to EOF.  A namespace-closing command after it
        # is therefore rendered as prose, so item modules intentionally leave
        # their namespace open (Lean closes it at EOF).
        text = re.sub(
            rf"\n+end\s+{re.escape(module)}\s*$",
            "\n",
            text.rstrip(),
        )
        text = text.rstrip() + "\n"

        old = content_path.read_text(encoding="utf-8")
        if text != old:
            content_path.write_text(text, encoding="utf-8")
            changed += 1
        checked += 1
    print(json.dumps({"checked": checked, "normalized": changed}))


if __name__ == "__main__":
    main()
